import Tools.GeneratedStamp
import Tools.ProfileJson
import Effect4.Api
import TypeScript.Render
import Lean.Data.Json

/-!
# Truth — the Lean face of the rc.112 truth check

What it is: for every program of the `Eff` corpus (`Effect4.Program.Wire.Corpus.all` plus
`pTwo` of `git:14e6835:src/OCaml5/Bridge.lean`), the Lean machine's verdict and its observable
schedule, written as one JSON manifest (`harness/truth/corpus.json`) that the rc.112 runner
(`harness/truth/run-truth.ts`) and, later, the OCaml host replay against.

    lake env lean -M4096 --run harness/truth/Truth.lean [harness/truth/corpus.json]

Without an argument the manifest goes to stdout. Depends on `Effect4.Api` (typing, printing,
running), `TypeScript.Render` (the pinned renderer: bytes of the printed program), and
`Lean.Data.Json` (escaping and layout of the manifest; nothing of the project's semantics).

Why one file: a `--run` tool can import only Lake modules, and `ocaml/tools` is not
a Lake library, so the library half (`OCaml5.Truth`, everything above `main`) and the thin
driver (`main`) share this file. The library half is pure; `main` only parses arguments and
writes.

Manifest (`format: effect4-truth-manifest-v1`), one entry per program:

* `name`, `wellTyped`, `type` (`{answer, error, requiresEmpty}` as `Ty.render` spells them,
  `null` when ill-typed);
* `expr`: the program as one TypeScript expression (`Api.print` rendered by
  `TypeScript.Render.expr house0 0`), or `null` with `exprRefusal` naming the refusal;
* `decl`: the exported constant `Api.printDecl "main"` rendered by
  `TypeScript.Render.constDecl house0`, or `null` (ill-typed, or refused);
* `run`: `Api.run p fuel` — `outcome` (`finished`, `frontier`, `stuck …`), `exit` (the root's
  exit in the wire below, `null` while the root is live), `fibers` (id, exited, parked token),
  `events` (the machine events with an rc.112 counterpart, in order), `schedule` (the same
  events reduced to the alphabet the runner can observe), `internal` (the other non-frame
  events, recorded, never compared), `frames` (how many frame rows were dropped);
* `runSync`: `Api.runSync p fuel` — `Effect.runSyncExit`'s exit, and `sync`, whether the
  program settled inside it (its exit is not the `AsyncFiberError` defect).

The value wire: `unit` ↦ `null`, `nat` ↦ number,
`bool` ↦ boolean, a tuple / exit list ↦ JSON array, `fiber k` ↦ `{"fiber":k}`,
`cell k` ↦ `{"ref":k}`, `promise k` ↦ `{"deferred":k}`, `scopeHandle k` ↦ `{"scope":k}`,
`context` ↦ `{"context":true}`, a reified exit ↦ `{"success":v}` / `{"failure":cause}`; a
cause is `{"reasons":[…]}` with `{"fail":n|string|{"boom":null}|[tag,message]}`, `{"die":d}`,
where a represented error defect is `{"die":{"error":<the same error wire>}}`,
`{"interrupt":who|null}`;
an exit is `{"success":v}` / `{"failure":cause}`. Annotations are dropped.

Behaviours held:

* deterministic — the manifest is a function of the corpus and the fuel (by construction:
  no IO above `main`);
* total under fuel — every run is `Api.run`/`Api.runSync` at the given fuel, a frontier when
  it runs out, never a hang (by construction);
* complete over the corpus — every program of `corpus` has one entry, names are unique
  (tested: the `#guard`s at the end);
* honest about refusals — a print refusal or an ill-typed program is recorded as such, the
  program is never patched (by construction: `expr`/`decl` are `Api.print`/`Api.printDecl`
  verbatim).
-/

open Lean (ToJson toJson)

/-- `Lean.Json`, named apart from `Effect4.Json` (the tree's own JSON carrier, which
`open Effect4` brings into scope). -/
abbrev J := Lean.Json

namespace OCaml5.Truth

open Effect4 Effect4.Api Effect4.Machine Effect4.Program
open TypeScript (house0)

/-! ## The corpus -/

/-- `forkOptions` from `git:14e6835:src/OCaml5/Bridge.lean`, verbatim. -/
def forkOptions : Supervision.ForkOptions :=
  { startImmediately := false, daemon := false, maskMode := .inherit }

/-- `pTwo` from `git:14e6835:src/OCaml5/Bridge.lean`, verbatim: two children forked, the second awaited twice (`.var 1` names the
second child before and after the first await). -/
def pTwo : Api.Program :=
  .bind (.withFiber (.fork (.bind (.yieldNow 0) (.succeed (.lit (.nat 1)))) forkOptions))
    (.bind (.withFiber (.fork (.bind (.yieldNow 0) (.succeed (.lit (.nat 2)))) forkOptions))
      (.bind (.awaitFiber (.var 1) .awaitValue) (.awaitFiber (.var 1) .awaitValue)))

/-- `acquireRelease` inside `scoped` (V1, 2026-09-07): the release, registered on the ambient
scope, runs when `scoped` closes it and writes the acquired value into a cell the root made
first; the root then reads the cell. The release is typed over `[ref, a, exit]`
(`Typing.lean`): `.var 0` is the cell, `.var 1` the acquired `7`. -/
def pAcquire : Api.Program :=
  .bind (.perform .refMake (.lit (.nat 0)))
    (.bind (.scoped (.acquireRelease (.succeed (.lit (.nat 7)))
        (.perform .refSet (.app "pair" (.cons (.var 0) (.cons (.var 1) .nil))))))
      (.perform .refGet (.var 0)))

/-- `acquireRelease` after its scope closed (`scopeAddFinalizerExit`'s closed branch,
`internal/effect.ts:3851-3853`): a child forked inside `scoped` inherits the scoped context;
it runs after the root has left `scoped` — the root awaits it — so its `acquireRelease`
finds the ambient scope closed and runs the release at once, on the child. The root then
reads the cell the release wrote. In the child the release is typed over `[ref, a, exit]`. -/
def pAcquireClosed : Api.Program :=
  .bind (.perform .refMake (.lit (.nat 0)))
    (.bind (.scoped (.withFiber (.fork
        (.acquireRelease (.succeed (.lit (.nat 7)))
          (.perform .refSet (.app "pair" (.cons (.var 0) (.cons (.var 1) .nil)))))
        forkOptions)))
      (.bind (.awaitFiber (.var 1) .awaitValue) (.perform .refGet (.var 0))))

/-! ### The join's fixtures (2026-09-07): `Effect.provide`, `Layer.effect`, the memo store

Keys are typed by their code on the native route (`nativeServiceTy`): `kA`, `kB` carry a
number (code `4`), `kRef` a `Ref.Ref<number>` (code `7`). A layer body is a closed program, so
a body reaches the root's cell through `Effect.service`, never through a binder. -/

def kA : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩
def kB : ServiceKey := ⟨⟨5⟩, ⟨4⟩⟩
def kRef : ServiceKey := ⟨⟨6⟩, ⟨7⟩⟩

/-- `Effect.provide(Effect.service(kA), Layer.effect(kA, Effect.succeed(7)))`
(`internal/layer.ts:8-22`): the layer built into `provide`'s scope, the service read under the
built context. -/
def pProvide : Api.Program :=
  .provideLayer (.effect kA (.succeed (.lit (.nat 7)))) false (.service kA)

/-- A layer whose construction acquires a resource and whose release bumps the root's cell,
reached as the service `kRef`; the release is typed over `[ref, a, exit]`. -/
def layerBump (k : ServiceKey) : LayerTerm NativeOp :=
  .effect k (.bind (.service kRef)
    (.acquireRelease (.succeed (.lit (.nat 1))) (.perform (.refUpdate .incr) (.var 0))))

/-- Two layers merged (`Layer.ts:1587-1602`), each acquiring in its own layer scope; when
`Effect.provide` closes its scope on the way out (`internal/effect.ts:3967`) both memo entries
release their layer scopes (`Layer.ts:404-408`), both releases run, and the root reads `2`. -/
def pProvideMerge : Api.Program :=
  .bind (.perform .refMake (.lit (.nat 0)))
    (.provideService kRef (.var 0)
      (.bind (.scoped (.provideLayer (.merge (layerBump kA) (layerBump kB)) false (.service kB)))
        (.perform .refGet (.var 0))))

/-- A layer whose construction bumps the root's cell and provides `5`. -/
def layerCount (k : ServiceKey) : LayerTerm NativeOp :=
  .effect k (.bind (.service kRef)
    (.bind (.perform (.refUpdate .incr) (.var 0)) (.succeed (.lit (.nat 5)))))

/-- The same layer term at two sites under one memo map (`Layer.merge(L, L)`): printed inline
it is two layer objects (`Layer.ts:411`, identity by object) and here it is two paths
(`LayerId`), so each site builds once and the cell reads `2` on both faces. What this pins is
the memo store's protocol — one entry per site, built, completed, released and its layer scope
closed on exit — not a hit; a hit needs one object at two sites, which no inline-printed
program has (`docs/research/2026-09-07-join-delivery.md`). -/
def pProvideTwice : Api.Program :=
  .bind (.perform .refMake (.lit (.nat 0)))
    (.provideService kRef (.var 0)
      (.bind (.provideLayer (.merge (layerCount kA) (layerCount kA)) false (.service kA))
        (.perform .refGet (.var 0))))

/-- The memo fix (the host rows slice, 2026-09-08, DB-12 amended): one layer at two sites, the
second a reference to the first's path — printed `const L_1_0_0_0_0 = Layer.effect(…)` then
`Layer.merge(L_1_0_0_0_0, L_1_0_0_0_0)` — is one object in rc.112 (`Layer.ts:411`) and one
memo key here (`resolveLayer` redirects), so the layer builds once and the cell reads `1`.
Beside `pProvideTwice`'s `2`, the pair is the receipt. The target path: the root `bind`'s
child `1` is the `provideService`, its child `0` the inner `bind`, its child `0` the
`provideLayer`, its child `0` the `merge`, its child `0` the layer. -/
def pDiamond : Api.Program :=
  .bind (.perform .refMake (.lit (.nat 0)))
    (.provideService kRef (.var 0)
      (.bind (.provideLayer (.merge (layerCount kA) (.ref [1, 0, 0, 0, 0])) false (.service kA))
        (.perform .refGet (.var 0))))

def kC : ServiceKey := ⟨⟨7⟩, ⟨4⟩⟩

/-- Three layers merged n-ary (`Layer.mergeAll(a, b, c)`, `mergeAllEffect`,
`Layer.ts:1587-1602`): one parallel parent scope, one sequential child per layer, each build
bumping the cell; the root reads `3`. -/
def pMergeAll : Api.Program :=
  .bind (.perform .refMake (.lit (.nat 0)))
    (.provideService kRef (.var 0)
      (.bind
        (.provideLayer
          (.mergeAll (.cons (layerCount kA) (.cons (layerCount kB) (.cons (layerCount kC) .nil))))
          false (.service kC))
        (.perform .refGet (.var 0))))

/-- A unit-declared resource fixture. Acquisition and release run through actual
Effect.sync and Effect.acquireRelease on the host. The final read observes release,
and the returned pair also exercises the external-handle wire. -/
def acquireHandleTable : RowTable :=
  [ { name := "acquire", spelling := "Host.acquire", kind := .async,
      registration := .external, request := .unit, answer := .handle "Host.Resource", error := .never, cite := "" }
  , { name := "close", spelling := "Host.close", kind := .async,
      registration := .external, request := .handle "Host.Resource", answer := .unit, error := .never, cite := "" }
  , { name := "read", spelling := "Host.read", kind := .async,
      registration := .external, request := .handle "Host.Resource", answer := .nat, error := .never, cite := "" } ]

def pAcquireHandle : Api.Program :=
  .bind (.scoped (.acquireRelease (.callback (.external 0) (.lit .unit))
      (.callback (.external 1) (.var 0))))
    (.bind (.callback (.external 2) (.var 0))
      (.succeed (.app "pair" (.cons (.var 0) (.cons (.var 1) .nil)))))

def acquireHandleAnswers : List (Completion Val Err Defect FiberId Ann) :=
  [.ofExit (.success (.nat 0)), .ofExit (.success .unit), .ofExit (.success (.nat 1))]

def strs (xs : List String) : Term := .app "strings" (xs.foldr (fun s t => .cons (.lit (.str s)) t) .nil)
def pairT (a b : Term) : Term := .app "pair" (.cons a (.cons b .nil))

/-- The sqlite fixture over the canonical `SqliteBun` table (host rows step 6): open the
`:memory:` client, create, insert through `strings` parameters (JSON text, decoded by the
host before binding), select, and close at the scope's end. The answers come from the tape
rc.112 recorded (`harness/truth/tapes/pSqlite.jsonl`), never from a Lean-side list. -/
def pSqlite : Api.Program :=
  .scoped (.bind (.acquireRelease (.callback (.external 0) (.lit (.str ":memory:")))
                                  (.callback (.external 2) (.var 0)))
    (.bind (.callback (.external 1) (pairT (.var 0) (pairT (.lit (.str "CREATE TABLE t (a INTEGER, b TEXT)")) (strs []))))
      (.bind (.callback (.external 1) (pairT (.var 0) (pairT (.lit (.str "INSERT INTO t (a, b) VALUES (?, ?)")) (strs ["7", "\"x\""]))))
        (.callback (.external 1) (pairT (.var 0) (pairT (.lit (.str "SELECT a, b FROM t")) (strs [])))))))

/-- The key-value fixture over the canonical `KeyValueStoreMemory` table: make, set, get,
has, remove; the answer is the `(get, has)` pair. Answers from `tapes/pKv.jsonl`. -/
def pKv : Api.Program :=
  .bind (.callback (.external 0) (.lit .unit))
    (.bind (.callback (.external 2) (pairT (.var 0) (pairT (.lit (.str "k")) (.lit (.str "1")))))
      (.bind (.callback (.external 1) (pairT (.var 0) (.lit (.str "k"))))
        (.bind (.callback (.external 4) (pairT (.var 0) (.lit (.str "k"))))
          (.bind (.callback (.external 3) (pairT (.var 0) (.lit (.str "k"))))
            (.succeed (pairT (.var 2) (.var 3)))))))

/-! ### The error paths (2026-09-09, after the slice): what a real `SqlError` does

`sql.unsafe` on a missing table fails with rc.112's `SqlError`; the recorder posts the pair
of DB-15 in rc.112's two-level form — the reason's tag and the driver's message under it,
`("UnknownError", "no such table: missing")`, the outer `"SqlError"` implied by the row
(ruling G1) — to the tape and the machine replays it as `Err.tagged`. Each
way a program has of meeting such a failure is one fixture over the same client and statement:
it escapes through the scope, whose release still runs (`pSqlFail`); it is caught
(`pSqlCatch`); it is reified into the answer (`pSqlExit`); a layer built over it dies under
`Layer.orDie` (`pSqlOrDie`: both faces retain the adapter's exact two-string pair inside the
defect, compared as represented error data). The answers
come from `tapes/pSql*.jsonl`. -/

/-- The statement that fails: no table `missing`. -/
def sqlMissing (handle : Term) : Api.Program :=
  .callback (.external 1) (pairT handle (pairT (.lit (.str "SELECT a FROM missing")) (strs [])))

/-- `body` under an open client (`.var 0`) that the scope's end releases, as `pSqlite`. -/
def sqlClient (body : Api.Program) : Api.Program :=
  .scoped (.bind (.acquireRelease (.callback (.external 0) (.lit (.str ":memory:")))
                                  (.callback (.external 2) (.var 0)))
    body)

def pSqlFail : Api.Program := sqlClient (sqlMissing (.var 0))
/-- The two arms of a `catchCause` share one answer type (`Ty` has no union), so the body
answers a string the statement never reaches and the handler the string that is observed. -/
def pSqlCatch : Api.Program :=
  sqlClient (.catchCause (.bind (sqlMissing (.var 0)) (.succeed (.lit (.str "rows"))))
    (.succeed (.lit (.str "recovered"))))
def pSqlExit : Api.Program := sqlClient (.exit (sqlMissing (.var 0)))

def kSql : ServiceKey := ⟨⟨8⟩, ⟨4⟩⟩

/-- A layer whose build acquires the client on the layer scope, fails on the statement, and
releases when the failed build's scope closes; `Layer.orDie` turns the tagged failure into a
defect on both faces. -/
def pSqlOrDie : Api.Program :=
  .provideLayer (.orDie (.effect kSql
      (.bind (.acquireRelease (.callback (.external 0) (.lit (.str ":memory:")))
                              (.callback (.external 2) (.var 0)))
        (.bind (sqlMissing (.var 0)) (.succeed (.lit (.nat 1)))))))
    false (.service kSql)

/-- The programs over the sqlite table. -/
def sqliteFixtures : List String := ["pSqlite", "pSqlFail", "pSqlCatch", "pSqlExit", "pSqlOrDie"]

/-- Per-fixture input data supplied beside the canonical program: the row table, and the
built-in oracle answers of a unit-declared fixture (`pAcquireHandle`); a canonical package
fixture's answers come from its tape, appended by `main`. -/
def hostInputs (name : String) : RowTable × List (Completion Val Err Defect FiberId Ann) :=
  if name == "pAcquireHandle" then (acquireHandleTable, acquireHandleAnswers)
  else if sqliteFixtures.contains name then (Packages.sqliteBun, [])
  else if name == "pKv" then (Packages.keyValueStoreMemory, [])
  else ([], [])

/-- A failure with the tagged package error of DB-15: `Effect.fail(pair("SqlError", "boom"))`
fails with the pair, which the host wires as a two-string array and the machine reads as
`Err.tagged` (`errOf`). The exit's fail payload is compared on both faces. -/
def pFailTagged : Api.Program :=
  .fail (.app "pair" (.cons (.lit (.str "SqlError")) (.cons (.lit (.str "boom")) .nil)))

/-- S2: ordinary text failures keep their exact strings, including the string "boom",
which is distinct from the raw unsupported-error marker Err.boom. -/
def pFailText : Api.Program := .fail (.lit (.str "lost"))
def pFailBoomText : Api.Program := .fail (.lit (.str "boom"))

/-- A text failure during layer construction becomes a represented text defect under
Layer.orDie. There is no external table or tape in this fixture. -/
def pTextOrDie : Api.Program :=
  .provideLayer (.orDie (.effect kA
    (.bind (.fail (.lit (.str "lost"))) (.succeed (.lit (.nat 1))))))
    false (.service kA)


/-- S3: the printed handlers exercise the actual first-Fail behavior at rc.112
internal/effect.ts:2798–2810, including retained store writes on a miss. -/
def catchMixed : CauseTerm := .both (.fail (.lit (.nat 7)))
  (.both (.die (.lit (.nat 3))) (.fail (.lit (.nat 9))))
def pCatchError : Api.Program := .catchIf (.lit (.bool true))
  (.fail (.lit (.nat 7))) (.succeed (.var 0))
def pCatchIfHit : Api.Program := .catchIf
  (.app "eq" (.cons (.var 0) (.cons (.lit (.nat 7)) .nil)))
  (.failCause catchMixed) (.succeed (.var 0))
def pCatchIfMiss : Api.Program := .catchIf
  (.app "eq" (.cons (.var 0) (.cons (.lit (.nat 9)) .nil)))
  (.failCause catchMixed) (.succeed (.var 0))
def pCatchIfRetained : Api.Program :=
  .bind (.perform .refMake (.lit (.nat 1)))
    (.catchCause
      (.catchIf (.lit (.bool false))
        (.bind (.perform .refSet (.app "pair" (.cons (.var 0) (.cons (.lit (.nat 9)) .nil))))
          (.fail (.lit (.nat 7))))
        (.perform .refGet (.var 0)))
      (.perform .refGet (.var 0)))

/-- The programs checked: the original wire, control, layer and host fixtures, followed by
the S2 error-image and S3 handler fixtures. Every listed program contributes one manifest entry. -/
def corpus : List (String × Api.Program) :=
  Wire.Corpus.all ++ [("pTwo", pTwo), ("pAcquire", pAcquire), ("pAcquireClosed", pAcquireClosed),
    ("pProvide", pProvide), ("pProvideMerge", pProvideMerge), ("pProvideTwice", pProvideTwice),
    ("pDiamond", pDiamond), ("pMergeAll", pMergeAll), ("pAcquireHandle", pAcquireHandle),
    ("pFailTagged", pFailTagged), ("pSqlite", pSqlite), ("pKv", pKv),
    ("pSqlFail", pSqlFail), ("pSqlCatch", pSqlCatch), ("pSqlExit", pSqlExit), ("pSqlOrDie", pSqlOrDie),
    ("pFailText", pFailText), ("pFailBoomText", pFailBoomText), ("pTextOrDie", pTextOrDie), ("pCatchError", pCatchError),
    ("pCatchIfHit", pCatchIfHit), ("pCatchIfMiss", pCatchIfMiss), ("pCatchIfRetained", pCatchIfRetained)]

/-! ## The value wire -/

def errJson : Err → J
  | .boom => Lean.Json.mkObj [("boom", Lean.Json.null)]
  | .tag n => toJson n
  -- the host wires the failed pair as a two-element array, as `pair` builds it
  | .tagged t m => Lean.Json.arr #[Lean.Json.str t, Lean.Json.str m]
  | .text s => Lean.Json.str s

def defectJson : Defect → J
  | .notImplemented => Lean.Json.str "notImplemented"
  | .asyncFiber => Lean.Json.str "asyncFiber"
  | .badName => Lean.Json.str "badName"
  | .missingService => Lean.Json.str "missingService"
  | .user n => Lean.Json.mkObj [("user", toJson n)]
  | .error e => Lean.Json.mkObj [("error", errJson e)]

def reasonJson : Reason Err Defect FiberId Ann → J
  | .fail e _ => Lean.Json.mkObj [("fail", errJson e)]
  | .die d _ => Lean.Json.mkObj [("die", defectJson d)]
  | .interrupt none _ => Lean.Json.mkObj [("interrupt", Lean.Json.null)]
  | .interrupt (some who) _ => Lean.Json.mkObj [("interrupt", toJson who.value)]

def causeJson (c : CauseV) : J :=
  Lean.Json.mkObj [("reasons", Lean.Json.arr (c.reasons.map reasonJson).toArray)]

/-- Values in the wire, on the shared carrier (`Machine/Value.lean`'s table): a handle by its
kind byte, a reified exit by its constructor index with the cause read back through
`causeImage`, the snapshot by its fibers, a `list` as one array. A shape the machine never
produces renders deterministically under `"raw"`, so the wire stays total. -/
partial def valJson : Val → J
  | .unit => Lean.Json.null
  | .nat n => toJson n
  | .bool b => Lean.Json.bool b
  -- strings are machine values since DB-15; the host wires a string as itself, an option as
  -- rc.112's `Option` (`{"some":v}` / `{"none":true}`, the runner's wire of `_tag`)
  | .str s => Lean.Json.str s
  | .some v => Lean.Json.mkObj [("some", valJson v)]
  | .none => Lean.Json.mkObj [("none", Lean.Json.bool true)]
  | Value.external index => Lean.Json.mkObj [("external", toJson index)]
  | Value.fiber id => Lean.Json.mkObj [("fiber", toJson id)]
  | Value.fiberSnapshot handles =>
    Lean.Json.mkObj [("fibers", Lean.Json.arr
      ((((Effect4.Store.Image.list Value.fiberHandle).ofVal handles).getD []).map fun i =>
        toJson i.value).toArray)]
  | Value.cell k => Lean.Json.mkObj [("ref", toJson k)]
  | Value.promise k => Lean.Json.mkObj [("deferred", toJson k)]
  | Value.scope s => Lean.Json.mkObj [("scope", toJson s)]
  | Value.fiberContext _ _ _ => Lean.Json.mkObj [("context", Lean.Json.bool true)]
  -- a built service map (`Env.encode`, what a layer build answers and `Effect.provide` reads):
  -- the same `Context` object on the rc.112 face
  | Value.serviceContext _ => Lean.Json.mkObj [("context", Lean.Json.bool true)]
  | Val.exitOk v => Lean.Json.mkObj [("success", valJson v)]
  | Value.exitErr written =>
    Lean.Json.mkObj [("failure", ((causeImage.ofVal written).map causeJson).getD Lean.Json.null)]
  | .list values => Lean.Json.arr (values.map valJson).toArray
  | other => Lean.Json.mkObj [("raw", Lean.Json.str (toString (repr other)))]

def exitJson : ExitV → J
  | .success v => Lean.Json.mkObj [("success", valJson v)]
  | .failure c => Lean.Json.mkObj [("failure", causeJson c)]

/-- The kind of an exit, with the archived tracer's precedence (`outcomeWire`): a `Fail`
reason wins, then an `Interrupt`, then a `Die`; an empty cause is its own kind. -/
def exitKind : ExitV → String
  | .success _ => "success"
  | .failure c =>
    if c.reasons.any (fun | .fail _ _ => true | _ => false) then "fail"
    else if c.reasons.any (fun | .interrupt _ _ => true | _ => false) then "interrupt"
    else if c.reasons.any (fun | .die _ _ => true | _ => false) then "die"
    else "empty"

/-- Whether an exit is `runSyncExit`'s `AsyncFiberError` defect. -/
def isAsyncFiberDefect : ExitV → Bool
  | .failure c => c.reasons.any (fun | .die .asyncFiber _ => true | _ => false)
  | _ => false

/-! ## Events -/

abbrev Event := RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx

/-- The events with an rc.112 counterpart, as the manifest spells them. `none` for the rest. -/
def observable : Event → Option String
  | .forked p c d => some s!"forked {p.value}->{c.value}{if d then " daemon" else ""}"
  | .started f => some s!"started {f.value}"
  | .scheduledTask o p _ => some s!"scheduledTask owner={o.value} prio={p}"
  | .ranTask o _ => some s!"ranTask owner={o.value}"
  | .yieldInjected f n => some s!"yieldInjected {f.value}@{n}"
  | .parkedOn f t => some s!"parkedOn {f.value} token={t}"
  | .resumedWith f t _ => some s!"resumedWith {f.value} token={t}"
  | .exited f e => some s!"exited {f.value} {(exitJson e).compress}"
  | _ => none

/-- The reduced schedule alphabet the runner can observe on rc.112: fiber starts, exits (by
kind), forks, parks and resumes, and the dispatcher's scheduling and runs. Tokens, priorities'
tasks and exit values are erased; fiber ids are the machine's (root `0`, children in fork
order), which the runner reproduces by first-seen order. -/
def reduced : Event → Option String
  -- a daemon fork is invisible to the runner: only a non-daemon child joins `fiber._children`
  -- (`internal/effect.ts:5279-5281`), which is where the runner sees forks; `events` keeps it
  | .forked _ _ true => none
  | .forked p c false => some s!"forked {p.value} {c.value}"
  | .started f => some s!"started {f.value}"
  | .scheduledTask o p _ => some s!"scheduled {o.value} {p}"
  | .ranTask o _ => some s!"ran {o.value}"
  | .parkedOn f _ => some s!"parked {f.value}"
  | .resumedWith f _ _ => some s!"resumed {f.value}"
  | .exited f e => some s!"exited {f.value} {exitKind e}"
  | _ => none

/-- The events that are neither observable nor frame rows: recorded, never compared. -/
def internal : Event → Option String
  | .interruptRecorded who t =>
    some s!"interruptRecorded by={(who.map (·.value)).getD 0} target={t.value}"
  | .interruptDeferred t => some s!"interruptDeferred {t.value}"
  | .childrenInterrupted p cs => some s!"childrenInterrupted {p.value} n={cs.length}"
  | .observerFired f _ => some s!"observerFired {f.value}"
  | .finalizerProgram f _ e => some s!"finalizerProgram {f.value} {exitKind e}"
  | .scopeLinked _ sc k f => some s!"scopeLinked scope={sc} key={k} fiber={f.value}"
  | .scopeClosedOnLink sc f => some s!"scopeClosedOnLink scope={sc} fiber={f.value}"
  | .raceStarted r h n => some s!"raceStarted {r} host={h.value} entrants={n}"
  | .raceLaunched r e => some s!"raceLaunched {r} entrant={e.value}"
  | .raceSettled r e => some s!"raceSettled {r} {exitKind e}"
  | .contextSet f _ => some s!"contextSet {f.value}"
  | .callback k e => some s!"callback key={k} {exitKind e}"
  | _ => none

def isFrame : Event → Bool
  | .frame _ _ => true
  | _ => false

/-! ## One program's entry -/

def outcomeText : Api.Outcome → String
  | .finished => "finished"
  | .frontier => "frontier"
  | .stuck why => s!"stuck {repr why}"

def typeJson (ty : EffTy) : J :=
  Lean.Json.mkObj
    [ ("answer", Lean.Json.str ty.answer.render)
    , ("error", Lean.Json.str ty.error.render)
    , ("requires", Lean.Json.arr (ty.requires.elems.map Tools.ProfileJson.flatKeyJson).toArray)
    , ("requiresEmpty", Lean.Json.bool (decide (ty.requires = Machine.Env.Requirement.empty))) ]

def refusalText : PrintRefusal → String
  | .choose site => s!"choose site {site}"
  | .internalAction name => s!"internal action {name}"
  | .layerRef target => s!"layer reference to {target}"

def fiberJson (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) : J :=
  Lean.Json.mkObj
    [ ("id", toJson f.id.value)
    , ("exited", Lean.Json.bool f.exit.isSome)
    , ("exit", match f.exit with | some e => exitJson e | none => Lean.Json.null)
    , ("parkedToken", match f.parked with | .withGuard t => toJson t | .notParked => Lean.Json.null) ]

def strings (xs : List String) : J := Lean.Json.arr (xs.map Lean.Json.str).toArray

def runJson (p : Api.Program) (fuel : Nat) (table : RowTable := [])
    (answers : List (Completion Val Err Defect FiberId Ann) := []) : J :=
  let r := Api.run p fuel [] answers table
  let trace := r.trace
  Lean.Json.mkObj
    [ ("outcome", Lean.Json.str (outcomeText r.outcome))
    , ("exit", match r.exit with | some e => exitJson e | none => Lean.Json.null)
    , ("exitKind", match r.exit with | some e => Lean.Json.str (exitKind e) | none => Lean.Json.null)
    , ("fiberCount", toJson r.fiberCount)
    , ("fibers", Lean.Json.arr (r.machine.fibers.map fiberJson).toArray)
    , ("events", strings (trace.filterMap observable))
    , ("schedule", strings (trace.filterMap reduced))
    , ("internal", strings (trace.filterMap internal))
    , ("frames", toJson (trace.filter isFrame).length) ]

def runSyncJson (p : Api.Program) (fuel : Nat) (table : RowTable := [])
    (answers : List (Completion Val Err Defect FiberId Ann) := []) : J :=
  let (_, exit) := Api.runSync p fuel [] answers table
  Lean.Json.mkObj
    [ ("exit", exitJson exit)
    , ("exitKind", Lean.Json.str (exitKind exit))
    , ("sync", Lean.Json.bool (!isAsyncFiberDefect exit)) ]

def entry (fuel : Nat) (tapes : String → List (Completion Val Err Defect FiberId Ann))
    (name : String) (p : Api.Program) : J :=
  let (table, builtIn) := hostInputs name
  let answers := builtIn ++ tapes name
  let ty := Api.typeOf p table
  let printed := Api.print p table
  -- the declaration block (`Api.printModule`, the host rows slice): one `const L_<path>` per
  -- referenced layer target, then `main`; one declaration for a program with no references
  let decl := (Api.printModule "main" p table).map fun m =>
    String.join (m.decls.map (TypeScript.Render.decl house0))
  Lean.Json.mkObj
    [ ("name", Lean.Json.str name)
    , ("wellTyped", Lean.Json.bool ty.isSome)
    , ("type", match ty with | some t => typeJson t | none => Lean.Json.null)
    , ("expr", match printed with
        | .ok e => Lean.Json.str (TypeScript.Render.expr house0 0 e)
        | .error _ => Lean.Json.null)
    , ("exprRefusal", match printed with
        | .ok _ => Lean.Json.null
        | .error why => Lean.Json.str (refusalText why))
    , ("decl", match decl with
        | some text => Lean.Json.str text
        | none => Lean.Json.null)
    , ("run", runJson p fuel table answers)
    , ("runSync", runSyncJson p fuel table answers) ]

/-- The whole manifest; `tapes` gives each program the answers rc.112 recorded for its package
rows (the empty list for a program without a tape, which then parks at its first row). -/
def manifest (fuel : Nat) (tapes : String → List (Completion Val Err Defect FiberId Ann)) : J :=
  Lean.Json.mkObj
    [ ("format", Lean.Json.str "effect4-truth-manifest-v1")
    , ("generated", Lean.Json.str "GENERATED by harness/truth/Truth.lean — do not edit")
    , ("regenerate", Lean.Json.str "lake env lean -M4096 --run harness/truth/Truth.lean harness/truth/corpus.json --tapes harness/truth/tapes")
    , ("fuel", toJson fuel)
    , ("scopeKey", Tools.ProfileJson.flatKeyJson nativeScopeKey)
    , ("hostRows", Lean.Json.arr (acquireHandleTable.map Tools.ProfileJson.rowJson).toArray)
    , ("programs", Lean.Json.arr (corpus.map fun (name, p) => entry fuel tapes name p).toArray) ]

/-! ## The tapes: rc.112's recorded answers, decoded into the oracle

**What a tape is, and the quantifier on the claim it supports (DI-23).** A tape is the list
of package-row completions rc.112 gave *one* program on *one* run of the pinned host, in call
order, one JSON Lines row per call (`harness/truth/tapes/<name>.jsonl`, written by
`harness/truth/run-truth.ts`). Replaying it here is an agreement claim of exactly this shape:

* **single-fiber.** The rows carry the calling fiber's index but are consumed in file order,
  so a tape is a faithful oracle only while every row of a program is made by one fiber. Every
  fixture with a tape is single-fiber today, and there is no fork-using host fixture. The
  first one is an obligation, not an extension: rows would have to be selected per fiber, and
  a schedule the machine chose differently would consume them in a different order. Nothing in
  this file detects that; the fixture's author must.
* **the schedule comparison is untouched by tapes.** `compareSchedules` (`run-truth.ts`)
  compares the two faces' `started`/`forked`/`parked`/`resumed`/`ran`/`exited` rows and is not
  a function of the tape. A tape decides what a row *answered*, never when a fiber ran.
* **pinned host.** `effect@4.0.0-rc.112` and `@effect/sql-sqlite-bun@4.0.0-rc.112`, the
  versions `scripts/check-truth.py` refuses to run without, on bun. A tape is evidence about
  those bytes and no others.
* **the corpus.** 31 programs, of which 6 have tapes; the gate re-records all six on every run
  and refuses a byte that moved, so a committed tape is the answer rc.112 *just* gave, not a
  remembered one.
* **the error column.** A `failed` row is the DB-15 pair, made at the adapter before the
  program sees it (`prelude.ts` `toPair`, DI-59), so the value replayed here, the value the
  printed program's own handler observed and the value on the tape are one value.

The evidence word is *reproduced* (the gate regenerates and compares bytes) together with
*tested* (a finite corpus under a named observer) — never *proved*. `Test/contracts/faces.contract.md`
states the same quantifiers for the reader who is not in this file. -/

/-- The value wire, read back: `null` a unit, a number a natural, a string, a boolean, an
array a list, `{"external":i}` the next allocation index a resource reply names (the machine
mints the handle, `externalValue`), `{"some":v}` / `{"none":true}` an option. Anything else is
no value: a tape row that does not decode stops the driver rather than replaying a guess. -/
partial def jsonToVal : J → Option Val
  | .null => some .unit
  | .bool b => some (.bool b)
  | .str s => some (.str s)
  | .arr xs => (xs.toList.mapM jsonToVal).map .list
  | j@(.num _) => match j.getNat? with | .ok n => some (.nat n) | .error _ => none
  | j@(.obj _) =>
    match j.getObjVal? "external" with
    | .ok i => match i.getNat? with | .ok n => some (.nat n) | .error _ => none
    | .error _ =>
      match j.getObjVal? "some" with
      | .ok v => (jsonToVal v).map .some
      | .error _ => match j.getObjVal? "none" with | .ok _ => some .none | .error _ => none

/-- An oracle answer: what a tape row decodes to. -/
abbrev Answer := Completion Val Err Defect FiberId Ann

/-- One tape row as a completion: `answer` a success, `failed` the tagged pair of DB-15 (the
runner's informational `error`, the outer tag, beside it is not read). A legacy `died` row is an unstructured diagnostic, so this legacy reader refuses it.
The versioned session reader separately supports selected represented defects; it does not
retroactively supply missing category/payload provenance to old rows. -/
def tapeAnswer (row : J) : Except String Answer :=
  match row.getObjVal? "answer" with
  | .ok a => match jsonToVal a with
    | some v => .ok (.ofExit (.success v))
    | none => .error s!"undecodable answer {a.compress}"
  | .error _ =>
    match row.getObjVal? "failed" with
    | .ok (.arr #[.str tag, .str message]) => .ok (.ofExit (.failure (Cause.fail (.tagged tag message))))
    | .ok other => .error s!"undecodable failure {other.compress}"
    | .error _ =>
      match row.getObjVal? "died" with
      | .ok defect => .error s!"a host defect on the tape cannot be replayed as a typed failure: {defect.compress}"
      | .error _ => .error s!"a tape row with neither answer nor failed: {row.compress}"

def tapeAnswers (lines : List String) : Except String (List Answer) :=
  (lines.filter (· ≠ "")).mapM fun line => do
    let row ← Lean.Json.parse line
    tapeAnswer row

/-! ## Receipts -/

#guard corpus.length = 31
#guard (corpus.map (·.1)).eraseDups.length = corpus.length
#guard (corpus.map (·.1)) =
  ["p42", "pBind", "pFork", "pAwait", "pGen", "pLoop", "pCatch", "pScope", "pTwo", "pAcquire",
   "pAcquireClosed", "pProvide", "pProvideMerge", "pProvideTwice", "pDiamond", "pMergeAll", "pAcquireHandle",
   "pFailTagged", "pSqlite", "pKv", "pSqlFail", "pSqlCatch", "pSqlExit", "pSqlOrDie",
   "pFailText", "pFailBoomText", "pTextOrDie", "pCatchError", "pCatchIfHit", "pCatchIfMiss", "pCatchIfRetained"]
-- S2 wire identities are distinct before any host comparison.
#guard errJson .boom == Lean.Json.mkObj [("boom", Lean.Json.null)]
#guard errJson (.text "boom") == Lean.Json.str "boom"
#guard errJson .boom != errJson (.text "boom")
#guard defectJson (.error (.text "lost")) == Lean.Json.mkObj [("error", Lean.Json.str "lost")]
#guard Api.typeOf pFailText = some ⟨.never, .string, Env.Requirement.empty⟩
#guard Api.typeOf pFailBoomText = some ⟨.never, .string, Env.Requirement.empty⟩
#guard (Api.run pFailText 1000).exit = some (.failure (Cause.fail (.text "lost")))
#guard (Api.run pFailBoomText 1000).exit = some (.failure (Cause.fail (.text "boom")))
#guard Api.wellTyped pTextOrDie
#guard (Api.run pTextOrDie 1000).exit = some (.failure (Cause.die (.error (.text "lost"))))
-- the error-path fixtures type only under the sqlite table and read back
#guard sqliteFixtures.all fun name => (corpus.lookup name).isSome
#guard Api.wellTyped pSqlFail Packages.sqliteBun
#guard Api.wellTyped pSqlCatch Packages.sqliteBun
#guard Api.wellTyped pSqlExit Packages.sqliteBun
#guard Api.wellTyped pSqlOrDie Packages.sqliteBun
#guard !Api.wellTyped pSqlFail
#guard !Api.wellTyped pSqlCatch
#guard !Api.wellTyped pSqlExit
#guard !Api.wellTyped pSqlOrDie
#guard Api.roundTrip pSqlFail Packages.sqliteBun = .ok pSqlFail
#guard Api.roundTrip pSqlCatch Packages.sqliteBun = .ok pSqlCatch
#guard Api.roundTrip pSqlExit Packages.sqliteBun = .ok pSqlExit
#guard Api.roundTrip pSqlOrDie Packages.sqliteBun = .ok pSqlOrDie
-- their types: the failure escapes, is caught, is reified, becomes a defect
#guard (Api.typeOf pSqlFail Packages.sqliteBun).map (fun t => (t.answer, t.error)) =
  some (Packages.sqlRows, Packages.sqlError)
#guard (Api.typeOf pSqlCatch Packages.sqliteBun).map (fun t => (t.answer, t.error)) = some (.string, .never)
#guard (Api.typeOf pSqlExit Packages.sqliteBun).map (fun t => (t.answer, t.error)) =
  some (.exitOf Packages.sqlRows Packages.sqlError, .never)
#guard (Api.typeOf pSqlOrDie Packages.sqliteBun).map (fun t => (t.answer, t.error)) = some (.nat, .never)
-- the two package fixtures type only under their tables and read back; their runs are the
-- tapes' (the batteries of `Test/Api/PackagesContract.lean` pin the shapes over fixed answers)
#guard Api.wellTyped pSqlite Packages.sqliteBun
#guard Api.wellTyped pKv Packages.keyValueStoreMemory
#guard !Api.wellTyped pSqlite
#guard !Api.wellTyped pKv
#guard Api.roundTrip pSqlite Packages.sqliteBun = .ok pSqlite
#guard Api.roundTrip pKv Packages.keyValueStoreMemory = .ok pKv
-- the tape decoder: the wire read back
#guard jsonToVal (Lean.Json.mkObj [("external", 0)]) = some (.nat 0)
#guard jsonToVal (Lean.Json.mkObj [("some", "1")]) = some (.some (.str "1"))
#guard jsonToVal (Lean.Json.mkObj [("none", true)]) = some .none
#guard jsonToVal (Lean.Json.arr #[Lean.Json.arr #[Lean.Json.arr #["a", "7"]]]) = some (.list [.list [.list [.str "a", .str "7"]]])
#guard (tapeAnswers ["{\"fiber\":0,\"op\":\"has\",\"request\":[],\"answer\":true}", "", "{\"failed\":[\"SqlError\",\"m\"]}"]).toOption =
  some [.ofExit (.success (.bool true)), .ofExit (.failure (Cause.fail (.tagged "SqlError" "m")))]
#guard (tapeAnswers ["{\"answer\":{\"raw\":1}}"]).toOption = none
-- the runner's informational field beside `failed` is not read; a `died` row is refused
#guard (tapeAnswers ["{\"fiber\":0,\"op\":\"unsafe\",\"request\":[],\"failed\":[\"UnknownError\",\"no such table: missing\"],\"error\":\"SqlError\"}"]).toOption =
  some [.ofExit (.failure (Cause.fail (.tagged "UnknownError" "no such table: missing")))]
#guard (tapeAnswers ["{\"fiber\":0,\"op\":\"Sql.open\",\"request\":[\"/nowhere/x.db\"],\"died\":\"SQLiteError: unable to open database file\"}"]).toOption = none
-- the tagged failure types at the pair, evaluates to `Err.tagged`, and reads back
#guard Api.typeOf pFailTagged = some ⟨.never, .prod .string .string, Env.Requirement.empty⟩
#guard (Api.run pFailTagged 1000).exit = some (.failure (Cause.fail (.tagged "SqlError" "boom")))
#guard Api.roundTrip pFailTagged = .ok pFailTagged
-- the join's fixtures are well-typed, so they cross as declarations
#guard Api.wellTyped pProvide
#guard Api.wellTyped pProvideMerge
#guard Api.wellTyped pProvideTwice
-- the host rows slice: the reference is well formed and typed by expansion, the diamond
-- prints as a two-declaration block, and both read back whole
#guard pDiamond.layerRefsWF
#guard Api.wellTyped pDiamond
#guard Api.wellTyped pMergeAll
#guard (Api.printModule "main" pDiamond).map (·.decls.length) = some 2
#guard (Api.printModule "main" pMergeAll).map (·.decls.length) = some 1
#guard (Api.printModule "main" pDiamond).map Api.readModule = some (.ok pDiamond)
#guard (Api.printModule "main" pMergeAll).map Api.readModule = some (.ok pMergeAll)
#guard (Api.printModule "main" pProvideTwice).map Api.readModule = some (.ok pProvideTwice)

#guard LawfulTable acquireHandleTable
#guard Api.wellTyped pAcquireHandle acquireHandleTable
#guard (Api.run pAcquireHandle 1000 [] acquireHandleAnswers acquireHandleTable).exit =
  some (.success (.list [.handle 7 0, .nat 1]))
#guard (Api.run pAcquireHandle 1000 [] acquireHandleAnswers acquireHandleTable).stores.externals.allocated =
  ["Host.Resource"]

end OCaml5.Truth

/-- The tapes under `dir`: `<name>.jsonl` per corpus program that has one, decoded into that
program's oracle answers; a program without a tape gets none. A row that does not decode is an
error, not a guess. -/
def readTapes (dir : System.FilePath) : IO (String → List OCaml5.Truth.Answer) := do
  let mut table : List (String × List OCaml5.Truth.Answer) := []
  for (name, _) in OCaml5.Truth.corpus do
    let file := dir / (name ++ ".jsonl")
    if ← file.pathExists then
      let text ← IO.FS.readFile file
      match OCaml5.Truth.tapeAnswers (text.splitOn "\n") with
      | .ok answers => table := (name, answers) :: table
      | .error why => throw (IO.userError s!"tape {file}: {why}")
  return fun name => ((table.find? (·.1 == name)).map (·.2)).getD []

/-- The driver: `<out> [--tapes <dir>]` writes the manifest there, else prints it (with the
tapes of `harness/truth/tapes`). The fuel is fixed at `1000`, enough for every corpus program
to settle or park. -/
def main (args : List String) : IO Unit := do
  let fuel := 1000
  let (out?, tapeDir) := match args with
    | [out, "--tapes", dir] => (some out, dir)
    | [out] => (some out, "harness/truth/tapes")
    | _ => (none, "harness/truth/tapes")
  let tapes ← readTapes tapeDir
  let text := (OCaml5.Truth.manifest fuel tapes).pretty 100 ++ "\n"
  match out? with
  | some out =>
    IO.FS.writeFile out text
    let stamp ← Tools.GeneratedStamp.line "harness/truth/Truth.lean" []
      ["harness/truth/run-truth.ts", "harness/truth/prelude.ts", "ts/eff/package.json", "ts/eff/bun.lock"]
    Tools.GeneratedStamp.sidecar out stamp
    IO.println s!"wrote {OCaml5.Truth.corpus.length} programs to {out}"
  | _ => IO.println text
