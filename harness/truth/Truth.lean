import Test.Counterexamples.Machine.Semantics.InterruptEscape
import Test.Codegen.TermRows
import Test.Program.MaskContract
import Test.Program.BoundsControls
import Effect4.Codegen.PrintTyped
import Test.Program.QueueMask
import Test.Program.SemaphoreScenarios
import Test.Program.PoolPublic
import Tools.GeneratedStamp
import Tools.ProfileJson
import Effect4.Api
import Effect4.Laws.Api.Frontier
import Effect4.Laws.Program.Denote
import Test.Program.Gen
import TypeScript.Render
import Lean.Data.Json

/-!
# Truth — the Lean face of the rc.112 truth check

What it is: for every program of the `Eff` corpus (`Effect4.Program.Wire.Corpus.all` plus
`pTwo` of `git:14e6835:src/OCaml5/Bridge.lean`), the Lean machine's verdict and its observable
schedule, written as one JSON manifest (`harness/truth/corpus.json`) that the rc.112 runner
(`harness/truth/run-truth.ts`) and, later, the OCaml host replay against.

    lake env lean -M4096 --run harness/truth/Truth.lean [harness/truth/corpus.json]
    lake env lean -M4096 --run harness/truth/Truth.lean --corpus <out.json> <count> <depth>

Without an argument the manifest goes to stdout. The second form writes the same manifest
shape for the generated corpus (`Test/Program/Gen.lean`, `count` programs at `depth`, named
`g<i>` as `tools/Drivers/Corpus.lean` names them), with no tapes and the empty table; it is the
input of `scripts/check-corpus.py` (`make check-corpus`), the run and type comparisons
against rc.112 over the whole corpus. Depends on `Effect4.Api` (typing, printing,
running), `TypeScript.Render` (the pinned renderer: bytes of the printed program), and
`Lean.Data.Json` (escaping and layout of the manifest; nothing of the project's semantics).

Why one file: a `--run` tool can import only Lake modules, and `ocaml/tools` is not
a Lake library, so the library half (`OCaml5.Truth`, everything above `main`) and the thin
driver (`main`) share this file. The library half is pure; `main` only parses arguments and
writes.

Manifest (`format: effect4-truth-manifest-v1`), one entry per program:

* `name`, `wellTyped`, `type` (`{answer, error, requiresEmpty}` as `Ty.render` spells them,
  `null` when ill-typed), `straight` (whether the program is in the fragment `run_eq_meaning`
  covers, `Effect4.Program.Denote.Straight`: on such a program rc.112's exit is compared,
  through the theorem, with the algebra's answer);
* `expr`: the program as one TypeScript expression (`Api.print` rendered by
  `TypeScript.Render.expr house0 0`), or `null` with `exprRefusal` naming the refusal;
* `decl`: the exported constant `Api.printDecl "main"` rendered by
  `TypeScript.Render.constDecl house0`, or `null` (ill-typed, or refused);
* `declInferred`: the same block with no type annotation on any declaration, the module the
  type oracle reads so that the host's compiler infers the program's type on its own;
* `run`: `Api.run p fuel` — `outcome` (`finished`, `frontier`, `stuck …`), `exit` (the root's
  exit in the wire below, `null` while the root is live), `fibers` (id, exited, parked token),
  `events` (the machine events with an rc.112 counterpart, in order), `schedule` (the same
  events reduced to the alphabet the runner can observe, each fiber under its number in the
  recorder's order, `numbering`), `internal` (the other non-frame events, recorded, never
  compared), `frames` (how many frame rows were dropped);
* `runSync`: `Api.runSync p fuel` — `Effect.runSyncExit`'s exit, and `sync`, whether the
  program settled inside it (its exit is not the `AsyncFiberError` defect).

The value wire: `unit` ↦ `null`, `nat` ↦ number,
`bool` ↦ boolean, a tuple / exit list ↦ JSON array, `fiber k` ↦ `{"fiber":n}`, where `n` is
the number of the fiber `k` in the recorder's order in a compared exit (`numbering`),
`cell k` ↦ `{"ref":k}`, `promise k` ↦ `{"deferred":k}`, `scopeHandle k` ↦ `{"scope":k}`,
`context` ↦ `{"context":true}`, a reified exit ↦ `{"success":v}` / `{"failure":cause}`; a
cause is `{"reasons":[…]}` with `{"fail":n|string|{"boom":null}|[tag,message]|{"payload":hex}}`,
where the program's own exit writes a payload through its error column,
`{"fail":{"payload":{"_tag":…,…}}}` (`errJsonAt`, decisions row 120, ruling (a)),
`{"die":d}`,
where a represented error defect is `{"die":{"error":<the same error wire>}}`,
`{"interrupt":who|null}`, the interruptor under the same number;
an exit is `{"success":v}` / `{"failure":cause}`. Annotations are dropped.

Behaviours held:

* deterministic — the manifest is a function of the corpus and the fuel (by construction:
  no IO above `main`);
* total under fuel — every run is `Api.run`/`Api.runSync` at the given fuel, a frontier when
  it runs out, never a hang (by construction);
* complete over the corpus — every program of `corpus` has one entry, names are unique
  (tested: the `#guard`s at the end);
* honest about refusals — a print refusal or an ill-typed program is recorded as such.
  Ordinary fixtures retain the raw producer. Joined fixtures retain `Program.printTyped`
  verbatim through the explicitly restricted fixture adapter;
* one numbering — each compared field writes a fiber under its number in the recorder's
  first-seen order (`numbering`), so the two faces are compared up to one renaming of the
  fibers, and the machine's allocation order is compared in no field (tested: the receipts on
  `lateSights`, `pQueueOrder` and `pLateSeen`).
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
reached as the service `kRef`; the release is typed over `[ref, a, exit]`, so its `Ref.update`
sits at level 3 and carries `incr`'s image there, `succ(var 3)`. -/
def layerBump (k : ServiceKey) : LayerTerm NativeOp :=
  .effect k (.bind (.service kRef)
    (.acquireRelease (.succeed (.lit (.nat 1)))
      (.perform (.refUpdateWith (Effect4.Machine.FnName.image .update 3 .incr)) (.var 0))))

/-- Two layers merged (`Layer.ts:1587-1602`), each acquiring in its own layer scope; when
`Effect.provide` closes its scope on the way out (`internal/effect.ts:3967`) both memo entries
release their layer scopes (`Layer.ts:404-408`), both releases run, and the root reads `2`. -/
def pProvideMerge : Api.Program :=
  .bind (.perform .refMake (.lit (.nat 0)))
    (.provideService kRef (.var 0)
      (.bind (.scoped (.provideLayer (.merge (layerBump kA) (layerBump kB)) false (.service kB)))
        (.perform .refGet (.var 0))))

/-- A layer whose construction bumps the root's cell and provides `5`: the `Ref.update` sits
under the service's binder, at level 1, and carries `incr`'s image there. -/
def layerCount (k : ServiceKey) : LayerTerm NativeOp :=
  .effect k (.bind (.service kRef)
    (.bind (.perform (.refUpdateWith (Effect4.Machine.FnName.image .update 1 .incr)) (.var 0))
      (.succeed (.lit (.nat 5)))))

/-- Two literal copies have different LayerId paths and print separate layer objects
(`Layer.ts:411`). Both builds run, so the root cell reads `2` on both faces. -/
def pProvideTwice : Api.Program :=
  .bind (.perform .refMake (.lit (.nat 0)))
    (.provideService kRef (.var 0)
      (.bind (.provideLayer (.merge (layerCount kA) (layerCount kA)) false (.service kA))
        (.perform .refGet (.var 0))))

/-- P2b / DI-71: a counted layer definition and two nested `ref` sites share one
memo entry. The printer hoists one layer object (`Layer.ts:411`), and both references
redirect to its path here. The definition is the outer provideLayer's child `0`,
reached through bind `1`, provideService `0`, and bind `0`. The root cell reads `1`.
Together with pProvideTwice, this compares sharing by reference with literal copies. -/
def pDiamond : Api.Program :=
  .bind (.perform .refMake (.lit (.nat 0)))
    (.provideService kRef (.var 0)
      (.bind (.provideLayer (layerCount kA) false
        (.provideLayer (.ref [1, 0, 0, 0]) false
          (.provideLayer (.ref [1, 0, 0, 0]) false (.service kA))))
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
  .bind (.scoped (.acquireRelease (.perform (.external 0) (.lit .unit))
      (.perform (.external 1) (.var 0))))
    (.bind (.perform (.external 2) (.var 0))
      (.succeed (.app "pair" (.cons (.var 0) (.cons (.var 1) .nil)))))

def acquireHandleAnswers : List (Completion Val Err Defect FiberId Ann) :=
  [.ofExit (.success (.nat 0)), .ofExit (.success .unit), .ofExit (.success (.nat 1))]

/-- The host row whose request supplies two list element bounds (UNGUARD W1). -/
def joinedFirstTable : RowTable := [Test.Program.BoundsControls.firstRow]

/-- A call term, using the native atom alphabet. -/
def joinedCall (name : String) (args : List Term) : Term :=
  .app name (args.foldr .cons .nil)

/-- W1 retains a union of two lists in the input term, with both branches present. -/
def joinedFirstInput (numeric : Bool) : Term :=
  joinedCall "ite"
    [.lit (.bool numeric), joinedCall "cons" [.lit (.nat 1), joinedCall "nil" []],
     joinedCall "strings" [.lit (.str "negative")]]

-- Finite control: the request is a union of lists, before the row matches its element bounds.
#guard [true, false].all fun numeric =>
  (termTy (nativeSignature joinedFirstTable) [] (joinedFirstInput numeric)).map Ty.normalize ==
    some Test.Program.BoundsControls.twoLists.normalize

/-- W1 supplies each member of the same two-list union to the actual host row. -/
def joinedFirst (numeric : Bool) : Api.Program :=
  .bind (.succeed (joinedFirstInput numeric)) (.perform (.external 0) (.var 0))

def pJoinedFirstNumber : Api.Program := joinedFirst true
def pJoinedFirstString : Api.Program := joinedFirst false

/-- W2 joins the reply while the next stored value stays a number. -/
def joinedModify (initial : Nat) : Api.Program :=
  .bind (.perform .refMake (.lit (.nat initial)))
    (.bind
      (.perform
        (.refModifyWith
          (joinedCall "ite"
            [ joinedCall "lt" [.lit (.nat 0), .var 1]
            , joinedCall "pair" [.lit (.nat 1), joinedCall "succ" [.var 1]]
            , joinedCall "pair"
                [joinedCall "concat" [.lit (.str "negative"), .lit (.str "")],
                 joinedCall "succ" [.var 1]] ]))
        (.var 0))
      (.bind (.perform .refGet (.var 0))
        (.succeed (joinedCall "ite"
          [joinedCall "eq" [.var 2, .lit (.nat (initial + 1))], .var 1,
           joinedCall "concat" [.lit (.str "joinedModify: wrong cell value"), .lit (.str "")]]))))

def pJoinedModifyNumber : Api.Program := joinedModify 1
def pJoinedModifyString : Api.Program := joinedModify 0

/-- Only these fixtures use the typed expression adapter below. -/
def joinedFixtures : List String :=
  ["pJoinedFirstNumber", "pJoinedFirstString", "pJoinedModifyNumber", "pJoinedModifyString"]

def strs (xs : List String) : Term := .app "strings" (xs.foldr (fun s t => .cons (.lit (.str s)) t) .nil)
def pairT (a b : Term) : Term := .app "pair" (.cons a (.cons b .nil))

/-- The sqlite fixture over the canonical `SqliteBun` table (host rows step 6): open the
`:memory:` client, create, insert through `strings` parameters (JSON text, decoded by the
host before binding), select, and close at the scope's end. The answers come from the tape
rc.112 recorded (`harness/truth/tapes/pSqlite.jsonl`), never from a Lean-side list. -/
def pSqlite : Api.Program :=
  .scoped (.bind (.acquireRelease (.perform (.external 0) (.lit (.str ":memory:")))
                                  (.perform (.external 2) (.var 0)))
    (.bind (.perform (.external 1) (pairT (.var 0) (pairT (.lit (.str "CREATE TABLE t (a INTEGER, b TEXT)")) (strs []))))
      (.bind (.perform (.external 1) (pairT (.var 0) (pairT (.lit (.str "INSERT INTO t (a, b) VALUES (?, ?)")) (strs ["7", "\"x\""]))))
        (.perform (.external 1) (pairT (.var 0) (pairT (.lit (.str "SELECT a, b FROM t")) (strs [])))))))

/-- The key-value fixture over the canonical `KeyValueStoreMemory` table: make, set, get,
has, remove; the answer is the `(get, has)` pair. Answers from `tapes/pKv.jsonl`. -/
def pKv : Api.Program :=
  .bind (.perform (.external 0) (.lit .unit))
    (.bind (.perform (.external 2) (pairT (.var 0) (pairT (.lit (.str "k")) (.lit (.str "1")))))
      (.bind (.perform (.external 1) (pairT (.var 0) (.lit (.str "k"))))
        (.bind (.perform (.external 4) (pairT (.var 0) (.lit (.str "k"))))
          (.bind (.perform (.external 3) (pairT (.var 0) (.lit (.str "k"))))
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
  .perform (.external 1) (pairT handle (pairT (.lit (.str "SELECT a FROM missing")) (strs [])))

/-- `body` under an open client (`.var 0`) that the scope's end releases, as `pSqlite`. -/
def sqlClient (body : Api.Program) : Api.Program :=
  .scoped (.bind (.acquireRelease (.perform (.external 0) (.lit (.str ":memory:")))
                                  (.perform (.external 2) (.var 0)))
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
      (.bind (.acquireRelease (.perform (.external 0) (.lit (.str ":memory:")))
                              (.perform (.external 2) (.var 0)))
        (.bind (sqlMissing (.var 0)) (.succeed (.lit (.nat 1)))))))
    false (.service kSql)

/-- The programs over the sqlite table. -/
def sqliteFixtures : List String := ["pSqlite", "pSqlFail", "pSqlCatch", "pSqlExit", "pSqlOrDie"]

/-- Per-fixture input data supplied beside the canonical program: the row table, and the
built-in oracle answers of a unit-declared fixture (`pAcquireHandle`); a canonical package
fixture's answers come from its tape, appended by `main`. -/
def hostInputs (name : String) : RowTable × List (Completion Val Err Defect FiberId Ann) :=
  if name == "pAcquireHandle" then (acquireHandleTable, acquireHandleAnswers)
  else if name == "pJoinedFirstNumber" then
    (joinedFirstTable, [.ofExit (.success (.some (.nat 1)))])
  else if name == "pJoinedFirstString" then
    (joinedFirstTable, [.ofExit (.success (.some (.str "negative")))])
  else if sqliteFixtures.contains name then (Packages.sqliteBun, [])
  else if name == "pKv" then (Packages.keyValueStoreMemory, [])
  else ([], [])

/-- Only W1 closes its single runtime row at the checker's actual call instance.
Typing and printing keep `firstRow`. The raw runner does not instantiate a template reply.
This finite adapter establishes no general runtime-table substitution law. -/
def fixtureRuntimeTable (name : String) (p : Api.Program) (table : RowTable) : Option RowTable := do
  if name != "pJoinedFirstNumber" && name != "pJoinedFirstString" then return table
  guard (table.length == 1)
  let row ← table[0]?
  let sig := nativeSignature table
  guard ((Program.calls sig [] p).length == 1)
  let call ← Program.callAt sig [] p [1]
  guard (call.op == .external 0)
  return [{ row with request := call.request, answer := call.answer, error := call.error }]

-- finite evaluation: the same checked union instance serves both runtime branches
#guard [pJoinedFirstNumber, pJoinedFirstString].all fun p =>
  (fixtureRuntimeTable "pJoinedFirstNumber" p joinedFirstTable).map
    (fun rows => rows.map fun row => (row.request, row.answer, row.error)) ==
      some [(Test.Program.BoundsControls.twoLists.normalize, (Ty.option (.union .nat .string)).normalize, .never)]
-- red: a value of the instance remains refused at the raw template column
#guard externalAdmits joinedFirstTable 0 (.ofExit (.success (.some (.nat 1)))) == false
-- green: the exact closed instance admits that value
#guard (fixtureRuntimeTable "pJoinedFirstNumber" pJoinedFirstNumber joinedFirstTable).any
  (fun rows => externalAdmits rows 0 (.ofExit (.success (.some (.nat 1)))))
-- finite controls: the other union member is admitted, while a Boolean payload still refuses
#guard externalAdmits joinedFirstTable 0 (.ofExit (.success (.some (.str "negative")))) == false
#guard (fixtureRuntimeTable "pJoinedFirstString" pJoinedFirstString joinedFirstTable).any
  (fun rows => externalAdmits rows 0 (.ofExit (.success (.some (.str "negative")))))
#guard (fixtureRuntimeTable "pJoinedFirstNumber" pJoinedFirstNumber joinedFirstTable).any
  (fun rows => !(externalAdmits rows 0 (.ofExit (.success (.some (.bool true))))))
-- red: the adapter refuses a different source shape instead of guessing an instance
#guard (fixtureRuntimeTable "pJoinedFirstNumber" (.succeed (.lit .unit)) joinedFirstTable).isNone

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

/-- DI-39/DI-17 handler observations: a hit replaces the cause, a miss retains it,
including any later failure whose tag the predicate would have caught. The mixed
columns therefore retain every possible error in Lean's inferred type. The host's
narrower inference is historical evidence of a type discrepancy, not permission to
remove a retained error (`E4-RESID-CE-001`). Runtime selection is unchanged. -/
def tagged (t m : String) : Term :=
  .app "pair" (.cons (.lit (.str t)) (.cons (.lit (.str m)) .nil))
def tagBody : Api.Program :=
  .bind (.select (.lit (.bool true)) .bool (.succeed (.lit (.nat 0))) (.fail (.lit (.str "text"))))
    (.fail (tagged "A" "m"))
def pTagHit : Api.Program := .catchIf (tagTest "A" 0) tagBody (.succeed (.lit (.nat 1)))
def pTagMiss : Api.Program := .catchIf (tagTest "B" 0) tagBody (.succeed (.lit (.nat 1)))
def pTagTwoFail : Api.Program := .catchIf (tagTest "A" 0)
  (.failCause (.both (.fail (tagged "B" "x")) (.fail (tagged "A" "m")))) (.succeed (.lit (.nat 1)))

/-- DI-78: one optional error value is consumed for presence and payload selection.
Both branches have the same declared error column, so the empty case has a real
payload bound rather than inferring one from its fallback. -/
def optionResult (present : Bool) : Api.Program :=
  .bind (.exit (.select (.lit (.bool present)) .bool (.fail (.lit (.nat 7)))
      (.succeed (.lit (.nat 0)))))
    (.bind (.succeed (.app "causeError" (.cons (.var 0) .nil)))
      (.succeed (.app "pair"
        (.cons (.app "isSome" (.cons (.var 1) .nil))
          (.cons (.app "getOrElse" (.cons (.var 1) (.cons (.lit (.nat 9)) .nil))) .nil)))))
def pOptionSome : Api.Program := optionResult true
def pOptionNone : Api.Program := optionResult false

/-- Decisions row 120, part E2: a tagged payload record as a typed failure. The module declares
`NotFound`'s `Data.TaggedError` class and fails with `new NotFound({ id: 9 })`; the exit's
error is compared through the type-directed codec (`errJsonAt`). -/
def notFound (id : Nat) : Term :=
  .record [("_tag", false, .lit "NotFound"), ("id", false, .nat)] ["_tag", "id"]
    (.cons (.lit (.str "NotFound")) (.cons (.lit (.nat id)) .nil))
def pFailPayload : Api.Program := .fail (notFound 9)
/-- The payload caught by its tag: `tagIs` reads the instance's own `_tag` on both faces. -/
def pTagPayload : Api.Program :=
  .catchIf (tagTest "NotFound" 0) (.fail (notFound 9)) (.succeed (.lit (.nat 1)))

/-- Decisions row 228: a list fold in a term position, with an outer capture and a fold inside
a fold. `a0` is a bound number, and `a1` a bound list built from it, `[a0 + 1, a0]`. The outer
fold walks `a1` from `a0` and binds `a2` and `a3`. The inner fold walks the captured `a1` again,
from the outer element `a3`, and binds `a4` and `a5`. Its body reads its two binders and the
outer element. With `a0 = 2` the answer is `8`: the two inner folds answer `3` and `3`. A printer
that named the inner binders at the outer fold's level would answer `7`. No fold states a type,
so the module reads back on both readers.

The list is built from a bound number and not from number literals. On the target a list of
number literals has a literal element type, and a list of two such lists with different
literals does not type-check under tsgo 7 (`cons(cons(1, cons(2, nil())), cons(cons(3, nil()),
nil()))`: `readonly (1 | 2)[]` is not `readonly 3[]`). That is the list atoms' typing and not
the fold's. -/
def pFold : Api.Program :=
  let call (name : String) (args : List Term) : Term := .app name (args.foldr .cons .nil)
  let list (xs : List Term) : Term := xs.foldr (fun x acc => call "cons" [x, acc]) (call "nil" [])
  .bind (.succeed (.lit (.nat 2)))
    (.bind (.succeed (list [call "succ" [.var 0], .var 0]))
      (.succeed (.fold none (.var 1) (.var 0)
        (call "add" [.var 2,
          .fold none (.var 1) (.var 3) (call "add" [.var 4, call "sub" [.var 5, .var 3]])]))))

/-- The state plan's T5 (decisions row 251): a step of the Queue's probe as a truth program. The
program is `Test.Codegen.TermRows.twoOffers`: the probe's offer step, twice on the Queue's first
state with no taker (`docs/research/2026-10-05-claude-lead/queue-readiness/QueueSkeleton.lean`).
Each step is one `Ref.modify` whose term reads and rewrites the state record, and no name spelled
such a term. The cell's printed type names `Deferred<void, never>`, and the program makes no
`Deferred`, so its module prints. It answers `[a hint was due, the buffer's length, the head
index]`, which is `[false, 2, 0]`. A source that does not elaborate is a failure with a text,
never a patched program; a guard below holds the source to its elaboration. -/
def pQueueOffer : Api.Program :=
  match Effect4.Program.Authoring.elaborate Test.Codegen.TermRows.twoOffers with
  | .ok p => p
  | .error _ => .fail (.lit (.str "pQueueOffer: the source does not elaborate"))

/-- The state plan's T5: one `Ref.modify` whose term folds, with an outer capture. `a0` is a bound
number, and `a1` a cell that holds `5`. The row's node stands at level 2, so its term binds the
cell's value as `a2`, and the fold inside the term binds `a3` and `a4` above that. The fold walks
`[a0 + 1, a0, 3]` from the cell's value and adds each element times the captured `a0`. The cell's
new value is its old one plus `a0`. With `a0 = 2` the step answers `5 + 3·2 + 2·2 + 3·2 = 21` and
leaves `7`, and the program answers the pair `[21, 7]`. A face that bound the term's value at the
node's own level, or the fold's binders at the term's, would read another program. -/
def pModifyFold : Api.Program :=
  let call (name : String) (args : List Term) : Term := .app name (args.foldr .cons .nil)
  let list (xs : List Term) : Term := xs.foldr (fun x acc => call "cons" [x, acc]) (call "nil" [])
  .bind (.succeed (.lit (.nat 2)))
    (.bind (.perform .refMake (.lit (.nat 5)))
      (.bind (.perform (.refModifyWith (call "pair"
            [.fold none (list [call "succ" [.var 0], .var 0, .lit (.nat 3)]) (.var 2)
                (call "add" [.var 3, call "mul" [.var 4, .var 0]]),
              call "add" [.var 2, .var 0]])) (.var 1))
        (.bind (.perform .refGet (.var 1))
          (.succeed (call "pair" [.var 2, .var 3])))))

/-- The state plan's T5: the rate limiter's request as a truth program (the first that the
slice's brief names). The program is `Test.Codegen.TermRows.fourRequests`: the request of
`Test/Dogfood/P4RateLimiter.lean`, four times on one window cell that admits three. Each request
is one `Ref.modify` whose term pairs the decision with the new window: one arm pairs `true`, and
the other `false`. Until the literal rule of decisions row 256 the pinned compiler refused the
module at those two arms, and the lane held the program out. It answers `[first decision,
fourth decision, admitted, rejected, used]`, which is `[true, false, 3, 1, 3]`. A source that
does not elaborate is a failure with a text, never a patched program. -/
def pRateRequest : Api.Program :=
  match Effect4.Program.Authoring.elaborate Test.Codegen.TermRows.fourRequests with
  | .ok p => p
  | .error _ => .fail (.lit (.str "pRateRequest: the source does not elaborate"))

/-- The state plan's T5, part B: a gate at `Deferred<void, never>`. The faces print
`Deferred.make`'s type arguments from the operation, so the module holds
`Deferred.make<void, never>()`. `a0` is the gate, and `a1` is a fiber that waits at the gate
and then answers `7`. The main fiber yields once, so the waiter is parked at the gate. Then the
main fiber reads whether the gate is done, opens it, opens it again, and joins the waiter. The
program answers `[done before, the first opening, the second opening, the waiter's answer]`,
which is `[false, true, false, 7]`: the first opening completes the gate and releases the
waiter, and the second finds the gate complete. -/
def pDeferredGate : Api.Program :=
  let call (name : String) (args : List Term) : Term := .app name (args.foldr .cons .nil)
  .bind (.perform (.deferredMakeOf .unit .never) (.lit .unit))
    (.bind (.withFiber (.fork
        (.bind (.perform .deferredAwait (.var 0)) (.succeed (.lit (.nat 7)))) Wire.Corpus.forkOptions))
      (.bind (.yieldNow 0)
        (.bind (.perform .deferredIsDone (.var 0))
          (.bind (.perform .deferredSucceed (call "pair" [.var 0, .lit .unit]))
            (.bind (.perform .deferredSucceed (call "pair" [.var 0, .lit .unit]))
              (.bind (.awaitFiber (.var 1) .joinEffect)
                (.succeed (call "tuple" [.var 3, .var 4, .var 5, .var 6]))))))))

open Effect4.Program.Authoring in
/-- The source of `pInterruptedWait`: a child marks a log, waits at a promise that nothing
completes, and would mark the log again; its parent interrupts it while it waits. -/
def interruptedWait : Src NativeOp := eff do
  let d ← Deferred.make .nat .never
  let log ← Ref.make (nat 0)
  let f ← fork (eff do
    let _ ← Ref.update "l" (app "add" [var "l", nat 1]) log
    let _ ← Deferred.await d
    Ref.update "l" (app "add" [var "l", nat 10]) log)
  let _ ← withFiber (Action.interrupt f)
  let e ← await f
  let l ← Ref.get log
  return tuple [app "causeIsInterrupt" [e], l]

/-- A parked fiber that an interrupt wakes, with no mask: the control of the `resumed` row's
second cause (`reduce`). `a0` is a promise that nothing completes, and `a1` a log cell. A child
marks the log with `1` and waits at the promise. The main fiber interrupts it there. The child
is interruptible, so the interrupt applies at once: the child runs again, and it exits
interrupted before its second mark. The program answers `[the child's exit is an interruption,
the log]`, which is `[true, 1]`. Its schedule holds `parked 1`, then `resumed 1` and
`started 1`, and no token is resumed. A source that does not elaborate is a failure with a
text, never a patched program. -/
def pInterruptedWait : Api.Program :=
  match Effect4.Program.Authoring.elaborate interruptedWait with
  | .ok p => p
  | .error _ => .fail (.lit (.str "pInterruptedWait: the source does not elaborate"))

/-- The mask that restores (decisions rows 244 to 246): a mask around a wait that is
interrupted. The program is `Test.Program.MaskContract.s2`, the note's scenario S2. `a0` is a
promise that nothing completes, and `a1` a log cell. A child runs the mask as the derived form:
the getter `Effect.uninterruptibleMask((a) => Effect.succeed(a))` under a `flatMap`, and the
body under `Effect.uninterruptible`. The body marks the log with `1`, waits at the promise in a
restore site, `pipe(Deferred.await(a0), a)`, and would mark `10`. The main fiber interrupts the
child while it waits. The caller is interruptible, so the restore site is interruptible: the
child exits interrupted, and its body does not go on. The program answers `[the child's exit is
an interruption, the log]`, which is `[true, 1]`. Its rows are `pInterruptedWait`'s: the mask
adds no row. A source that does not elaborate is a failure with a text, never a patched
program. -/
def pMaskWait : Api.Program :=
  match Effect4.Program.Authoring.elaborate Test.Program.MaskContract.s2 with
  | .ok p => p
  | .error _ => .fail (.lit (.str "pMaskWait: the source does not elaborate"))

/-- The mask that restores: a restore site under a masked caller. The program is
`Test.Program.MaskContract.s3`, the note's scenario S3: the child of `pMaskWait` under
`Effect.uninterruptible`, with a body that adds the awaited value to its second mark. A helper
fiber interrupts the child while it waits. The caller is masked, so the saved choice is the
identity and the wait is not interrupted. The main fiber reads the log, completes the promise
with `7`, and awaits the child and the helper. The child's body goes on to its end, and the
child is interrupted when its caller's mask ends. The program answers `[the log after the
interrupt's request, the child's exit is an interruption, the log at the end]`, which is
`[1, true, 18]`. -/
def pMaskedRestore : Api.Program :=
  match Effect4.Program.Authoring.elaborate Test.Program.MaskContract.s3 with
  | .ok p => p
  | .error _ => .fail (.lit (.str "pMaskedRestore: the source does not elaborate"))

open Effect4.Program.Authoring in
/-- The source of `pLateSeen`: a detached child with a deferred start, then two children that
start at once. The second interrupts the first, which waits at a promise that nothing
completes. The root yields once, so the detached child runs before the root answers. -/
def lateSeen : Src NativeOp := eff do
  let gate ← Deferred.make .unit .never
  -- a deferred start, detached, the parent's mask (`daemon` is a keyword of the surface here)
  let helper ← fork (succeed (nat 5)) ⟨false, true, .inherit⟩
  let waiter ← fork (Deferred.await gate)
  let _ ← fork (withFiber (Action.interrupt waiter))
  let exit ← await waiter
  let _ ← yieldNow 0
  return tuple [exit, helper]

/-- **A fiber that the recorder sees late, named in an exit**: the control of the fiber numbers
in `run.exit` and `runSync.exit` (`numbering`). The helper is the machine's fiber `1`: a
detached fork with a deferred start, so it has no `forked` row, and the recorder first sees it
at its first run. The waiter and its interruptor start at once: the machine's fibers `2` and
`3`, the recorder's `1` and `2`. The root awaits the waiter and yields, and the helper runs
then: the recorder's `3`. The program answers `[the waiter's exit, the helper]`. The exit names
the interruptor, so the wire holds a fiber in two fields: `{"interrupt":2}` and `{"fiber":3}`
under the recorder's numbers, which are `3` and `1` under the machine's ids. No fiber awaits the
helper before its first run (the limit on the `exited` row, in the section on the fiber
numbers). A source that does not elaborate is a failure with a text, never a patched
program. -/
def pLateSeen : Api.Program :=
  match Effect4.Program.Authoring.elaborate lateSeen with
  | .ok p => p
  | .error _ => .fail (.lit (.str "pLateSeen: the source does not elaborate"))

/-! ### The Queue's first operations (decisions rows 219 to 222, 233, 238 and 240)

Five programs over the library's operations (`src/Effect4/Modules/Queue/Ops.lean`): the first
host runs of the Queue's expansion. Each is a scenario of the Queue's batteries
(`Test/Program/QueueScenarios.lean`, `Test/Program/QueueMask.lean`), so the program that rc.112
runs is the program that the batteries run on the Lean machine. A waiting operation prints as
its expansion: the mask's getter, the request's two `Deferred` cells, one `Ref.modify` for each
step, and one `Effect.forkDetach` for each posted helper. The pin's own `Queue` is not printed
(decisions row 235). A source that does not elaborate is a failure with a text, never a patched
program. -/

/-- **A taker waits, and an offer's posted helper wakes it** (the scenario R2). `a0` is the
queue's cell, at capacity two. A child takes: it enrols and waits at its hint. The root offers
`7`: its step names the taker, and it posts one helper, a detached fork with a deferred start.
The root joins the child. The helper's task resolves the hint, and the taker takes the message
in its own step. The program answers `7`. -/
def pQueueWake : Api.Program :=
  match Effect4.Program.Authoring.elaborate Test.Program.QueueScenarios.r2 with
  | .ok p => p
  | .error _ => .fail (.lit (.str "pQueueWake: the source does not elaborate"))

/-- **A second offer waits at capacity one** (the scenario R4). The first offer is accepted. A
child offers `2`: the buffer is full, so the offer waits at its hint. The root takes `1`: its
step frees room, accepts the pending offer and decides its answer, and one helper carries that
answer to the offerer (decisions row 240). The root joins the offerer and takes again. The
program answers `[true, 1, true, 2]`. -/
def pQueueFull : Api.Program :=
  match Effect4.Program.Authoring.elaborate Test.Program.QueueScenarios.r4 with
  | .ok p => p
  | .error _ => .fail (.lit (.str "pQueueFull: the source does not elaborate"))

/-- **A waiting taker is interrupted** (the scenario R5). A child takes and waits at the mask's
restore site. The root interrupts it there: the wait is interruptible, and its withdrawal
removes the request. The root then offers `5`, which stays, and takes it. The program answers
`[5, 0]`: the message, and no taker left in the cell. -/
def pQueueInterrupted : Api.Program :=
  match Effect4.Program.Authoring.elaborate Test.Program.QueueScenarios.r5 with
  | .ok p => p
  | .error _ => .fail (.lit (.str "pQueueInterrupted: the source does not elaborate"))

/-- **A taker under a masked caller** (decisions row 222). A child takes under
`Effect.uninterruptible`, and it records its message in a cell. A second child interrupts it
while it waits. The caller is masked, so the restore is the identity: the request stays
registered. The root offers `9`: the taker takes it and records it inside its caller's mask,
and it is interrupted when that mask ends. The program answers `[1, 9, true, 0, 0]`: one taker
registered after the interrupt's request, the recorded message, the taker's exit an
interruption, an empty buffer and no taker at the end. -/
def pQueueMasked : Api.Program :=
  match Effect4.Program.Authoring.elaborate Test.Program.QueueMask.maskedCaller with
  | .ok p => p
  | .error _ => .fail (.lit (.str "pQueueMasked: the source does not elaborate"))

/-- **The order of one step's two notifications** (the scenario R8). Capacity one. The takers A
and B wait, a message is offered, and a second offer waits at the full buffer. A's take frees
room: its step accepts the second offer and leaves B ready, and it posts the offerer's answer
before B's wake. Each fiber writes a mark when it goes on. The program answers the log
`[1, 101, 2]`: A's message, the offerer's mark, B's message. -/
def pQueueOrder : Api.Program :=
  match Effect4.Program.Authoring.elaborate Test.Program.QueueScenarios.r8 with
  | .ok p => p
  | .error _ => .fail (.lit (.str "pQueueOrder: the source does not elaborate"))

/-! ### Semaphore's first operations (decisions rows 259 to 261 and 276)

Ten programs over the library's operations (`src/Effect4/Modules/Semaphore/Ops.lean`): the
first host runs of Semaphore's expansion. Each is a scenario of
`Test/Program/SemaphoreScenarios.lean`, so the program that rc.112 runs is the program that the
batteries run on the Lean machine. An operation prints as its expansion: the mask's getter, the
request's `Deferred` cells, one `Ref.modify` for each step, and one `Effect.forkDetach` for a
release's helper, whose body is the walk. The pin's own `Semaphore` is not printed (decisions
row 235). The case P9 has no host run: its yield is a decision of a tape. A source that does not
elaborate is a failure with a text, never a patched program.

**The cases P1 and P4 run in two forms each.** In both cases a child's hook releases, so the
helper is posted on that child's dispatcher. The sync entry flushes the root's dispatcher alone
(`runSyncExit`, `src/Effect4/Machine/Fibers.lean`). As the batteries write the two cases, the
root yields four times. Under the sync entry it therefore settles before the walk, on another
exit than the fork run's, and both faces give each of the two exits. They are the lane's first
programs whose two entries settle on two exits. The runner's exit column compares the fork
entry on both faces, and the sync pair has its own column (`main`,
`harness/truth/run-truth.ts`; decisions row 279, point 1). Until 2026-10-06 that column took
rc.112's sync exit whenever the sync run settled, and it was red for these two programs. The
two red rows of that rule are in `docs/research/2026-10-06-seat-semw-evidence/README.md`. In a
joined form the root joins the waiting fibers, and its sync entry ends in the
`AsyncFiberError` defect. -/

/-- The program of a scenario of Semaphore's battery, or a failure with a text. -/
def semaphoreProgram (name : String) (source : Effect4.Program.Authoring.Src NativeOp) :
    Api.Program :=
  match Effect4.Program.Authoring.elaborate source with
  | .ok p => p
  | .error _ => .fail (.lit (.str (name ++ ": the source does not elaborate")))

/-- **A waiter takes inside the walk, and the walk stops at no free permit** (the case P1, in
its joined form). A total of 2. A holds 2 in a protected body. B asks for 2 and C for 1: both
wait. A's body ends, and its hook releases 2 and posts one helper. The walk's first visit
selects B, which takes 2 inside the helper's task. B's exit resumes the root's join there too.
The next visit reads no free permit and stops, so C is not visited. The program answers the
counts before the release, the counts after B's exit and the marks:
`[[2, 2, [2, 1], [0, 1]], [2, 1, [1], [1]], [22]]`. -/
def pSemaphoreProtectedJoined : Api.Program :=
  semaphoreProgram "pSemaphoreProtectedJoined" Test.Program.SemaphoreScenarios.p1Joined

/-- **The case P1 as the batteries write it: its two entries settle on two exits.** The root
yields four times in place of its join. Under the fork entry the walk runs, and the program
answers the joined form's exit. Under the sync entry the root's yields end before the walk. The
release is in the cell, both waiters still wait, and no mark is written:
`[[2, 2, [2, 1], [0, 1]], [0, 2, [2, 1], [0, 1]], []]`. Both faces give each exit. -/
def pSemaphoreProtected : Api.Program :=
  semaphoreProgram "pSemaphoreProtected" Test.Program.SemaphoreScenarios.p1

/-- **The walk passes a waiter that does not fit, and resumes a later one** (the case P2). The
root holds 1 and 1. B asks for 2 and C for 1. The root releases 1: the release answers 1 free.
The visit passes B, whose count does not fit, and it selects C, which takes 1. B's entry stays.
The program answers `[[2, 2, [2, 1], [0, 1]], 1, [2, 1, [2], [0]], [31]]`. -/
def pSemaphoreScan : Api.Program :=
  semaphoreProgram "pSemaphoreScan" Test.Program.SemaphoreScenarios.p2

/-- **A resumed caller's next request takes inside the walk** (the case P3). The root holds 2. B
asks for 1 and then for 1 again, with no yield between. C asks for 1. The root releases 2. B
takes 1 and takes 1 again inside the walk, and C waits. The program answers
`[[2, 2, [1, 1], [0, 1]], [2, 1, [1], [1]], [21, 22]]`. -/
def pSemaphoreOvertake : Api.Program :=
  semaphoreProgram "pSemaphoreOvertake" Test.Program.SemaphoreScenarios.p3

/-- **Two protected bodies run and release inside one walk** (the case P4, in its joined
form). A holds 2, protected. B and C wait in the protected form, for 2 and for 1. B's body and
its release run inside the walk, and then C's body runs. The root joins B and then C. Nothing
stays taken. B's release posts a second helper, which runs after the root's exit and finds
nobody. The program answers `[[2, 2, [2, 1], [0, 1]], [0, 0, [], []], [22, 31]]`. -/
def pSemaphoreBodiesJoined : Api.Program :=
  semaphoreProgram "pSemaphoreBodiesJoined" Test.Program.SemaphoreScenarios.p4Joined

/-- **The case P4 as the batteries write it**, with the same root of four yields. Its fork
entry gives the joined form's exit, and its sync entry gives the exit before the walk, as the
case P1's does. -/
def pSemaphoreBodies : Api.Program :=
  semaphoreProgram "pSemaphoreBodies" Test.Program.SemaphoreScenarios.p4

/-- **An interrupted waiter withdraws, raw and protected** (the case P7). A total of 1, held by
the root. A raw waiter is interrupted, and then a protected waiter: each one's entry leaves, and
`taken` does not change. The root's release then answers 1 free and posts no helper. The program
answers the six readings. -/
def pSemaphoreInterrupted : Api.Program :=
  semaphoreProgram "pSemaphoreInterrupted" Test.Program.SemaphoreScenarios.p7

/-- **The two forms that never wait, on both answers.** A protected body takes 2 of 2, runs and
releases. The root takes 1. A second protected form asks for 2 and does not take: it answers the
empty option, its body does not run, and nothing is released. Two takes of 1 follow: the first
takes, and the second does not. The program answers
`[some 7, [0, 0, [], []], none, true, false, [2, 0, [], []], [2]]`. -/
def pSemaphoreIfAvailable : Api.Program :=
  semaphoreProgram "pSemaphoreIfAvailable" Test.Program.SemaphoreScenarios.ifAvailable

/-- **The protected permit under a masked caller** (decisions row 222). The root holds the one
permit. A child asks for it in the protected form under `Effect.uninterruptible`, and a second
child requests its interruption while it waits. The caller is masked, so the restore is the
identity: the request stays enrolled. The root releases: the child takes, its body runs inside
its caller's mask, its hook releases, and it is interrupted when that mask ends. The program
answers `[[1, 1, [1], [0]], 11, true, [0, 0, [], []]]`. -/
def pSemaphoreMasked : Api.Program :=
  semaphoreProgram "pSemaphoreMasked" Test.Program.SemaphoreScenarios.maskedCaller

/-- **The README's example.** The root takes the one permit. A worker asks for it in the
protected form, and it waits. The root releases, which answers 1 free, and joins the worker: the
walk resumes the worker, which runs its body and releases. The program answers `[1, 7]`. -/
def pSemaphoreHandoff : Api.Program :=
  semaphoreProgram "pSemaphoreHandoff" Test.Program.SemaphoreScenarios.handoff

/-! ### Pool's first operations (decisions rows 267 to 269, 276 and 279)

Ten programs over the library's operations (`src/Effect4/Modules/Pool/Ops.lean`): the first
host runs of Pool's expansion. Each is a case of `Test/Program/PoolPublic.lean`, so the program
that rc.112 runs is the program that the batteries run on the Lean machine. `make` prints as
its acquisitions, one `Ref.make` of the cell and one `Effect.acquireRelease` whose release is
the close. `use` prints as one mask over the lease's loop, the body at the restore site and the
return as its hook. The pin's own `Pool` is not printed (decisions row 235). A source that does
not elaborate is a failure with a text, never a patched program.

A snapshot of the cell is `[the idle stamps, the borrowed items' stamps, their leases' stamps,
the number of waiters, closing, next]`. The log's rows are `[1, mark, resource]` at a body's
entry, `[2, mark, resource]` at its end, `[8]` before a gate opens and `[9, resource]` from a
resource's finalizer. The marks are 9 for H, 1 for A and for W, 2 for B, 3 for C, 4 for D and 5
for L.

**The signed difference of decisions row 268 keeps no case out of the lane.** The lane runs the
module's expansion on both faces, and the expansion's close waits on both. The difference is
between this close and the close of the pin's own `Pool`, which ends at once. No program of the
lane calls the pin's `Pool`: its answers are those of the card's probes
(`docs/research/2026-10-05-claude-lead/module-cards/pool-probes/pool-close.ts`, with its
outputs). The same holds for the order of reuse (row 269) and for a failed acquisition (row
267): `pPoolOrder` and `pPoolMakeFails` answer the profile's order and the profile's failure
on both faces.

**The two entries.** Five programs settle on one exit under both entries: in each no return
finds a waiter, so no helper is posted. The two programs of a close that waits end the sync
entry in the `AsyncFiberError` defect: the closer waits, and the helper of the holder's return
is on the holder's dispatcher, which the sync entry does not flush (`runSyncExit`,
`src/Effect4/Machine/Fibers.lean`). The cases PP3, PP4 and PP5 settle on two exits, as
Semaphore's cases P1 and P4 do: a child's return posts the helper on that child's dispatcher,
and the root's four yields end before a wake. The runner's exit column compares the fork entry
on both faces, and the sync pair has its own column (decisions row 279, point 1). -/

/-- The program of a case of Pool's battery, or a failure with a text. -/
def poolProgram (name : String) (source : Effect4.Program.Authoring.Src NativeOp) :
    Api.Program :=
  match Effect4.Program.Authoring.elaborate source with
  | .ok p => p
  | .error _ => .fail (.lit (.str (name ++ ": the source does not elaborate")))

/-- **A returned item is used again, and its finalizer runs once, at the close** (the case
PP1). Size 1. A borrows and returns, and then B: both bodies hold the resource 1. The pool's
scope closes, and the finalizer writes its one row there. The program answers the cell before
the close and the log:
`[[[0], [], [], 0, false, 2], [[1, 1, 1], [2, 1, 1], [1, 2, 1], [2, 2, 1], [9, 1]]]`. -/
def pPoolReuse : Api.Program := poolProgram "pPoolReuse" Test.Program.PoolPublic.pp1

/-- **The order of reuse is the release's** (the case PP2, decisions row 269). Size 2. A and B
hold the resources 1 and 2. A returns, then B: the idle stamps are `[1, 0]`, with B's item at
the front. C then gets the resource 2, and D the resource 1. The close finalizes the items in
the reverse order of their acquisition. The pin's own `Pool` puts a returned item at the end.
The program runs the module's expansion, so both faces answer the release's order. -/
def pPoolOrder : Api.Program := poolProgram "pPoolOrder" Test.Program.PoolPublic.pp2

/-- **Two waiters, and each return wakes one** (the case PP3). Size 1. H holds, and A and B
wait. H returns and posts one helper, which selects A at the count 1. A's own step takes the
item, and B still waits. A's return posts the next helper, which wakes B. The root yields four
times after each of the two gates. Its two entries settle on two exits. Under the sync entry
the yields end before a helper runs: the item stays idle beside both waiters, no borrower but H
runs, and the log is `[[1, 9, 1], [2, 9, 1], [9, 1]]`. -/
def pPoolWaiters : Api.Program := poolProgram "pPoolWaiters" Test.Program.PoolPublic.pp3

/-- **A waiter is interrupted between the return and the wake** (the case PP4). PP3, and the
root interrupts A after H's return and before the posted helper runs. A's entry leaves. The
helper selects the first waiter of the state that it finds, which is B. A's body never runs.
Its two entries settle on two exits, as PP3's do. -/
def pPoolLateWake : Api.Program := poolProgram "pPoolLateWake" Test.Program.PoolPublic.pp4

/-- **The wake that a return posts** (the case PP5, in its public form). Size 1. H holds, and A
enrols. H returns: the item is idle beside A's entry. The helper selects A, and A's own step
takes the item at the lease's stamp 1. Its two entries settle on two exits, as PP3's do. -/
def pPoolWake : Api.Program := poolProgram "pPoolWake" Test.Program.PoolPublic.pp5

/-- **A failed acquisition fails `make`** (the case PP6, decisions row 267). The acquisition
registers a cleanup, writes the row `[5]` and fails with 77. `make` fails with that failure,
the cleanup runs at the scope's close, and no borrower runs. The program answers whether the
scope's exit is a failure, its failure and the log: `[true, some 77, [[5], [9, 1]]]`. The pin's
own `make` answers before any item exists. -/
def pPoolMakeFails : Api.Program := poolProgram "pPoolMakeFails" Test.Program.PoolPublic.pp6

/-- **The close waits for a borrowed item** (the case PP7, decisions row 268). Size 1. H holds,
and W waits. The pool's scope closes. The close's helper wakes W, whose lease is refused: W is
interrupted. The closer waits. A third fiber awaits W's exit, writes the row `[8]` and opens
H's gate. H's body ends, and its return posts the helper that wakes the closer. The finalizer's
row follows H's return. The program answers the cell before the close, `true` for W's
interruption, `false` for H's, the cell after the close and the log
`[[1, 9, 1], [8], [2, 9, 1], [9, 1]]`. The sync entry ends in the `AsyncFiberError` defect. -/
def pPoolCloseWaits : Api.Program := poolProgram "pPoolCloseWaits" Test.Program.PoolPublic.pp7

/-- **An interrupted waiter withdraws** (the case PP8). Size 1. H holds. A waits and is
interrupted: no waiter is left. H's return then owes no wake, and B leases at once. -/
def pPoolWithdrawn : Api.Program := poolProgram "pPoolWithdrawn" Test.Program.PoolPublic.pp8

/-- **A borrow at a closed pool** (decisions row 279, point 2). The pool's scope closes with no
borrower. Then L borrows. Its exit is a failure whose cause is the interruption of L's own
fiber, and its body does not run. The program answers L's exit, the cell and the log. The
interruptor is the number of L's own fiber, 1 on each face (decisions row 274). -/
def pPoolClosed : Api.Program := poolProgram "pPoolClosed" Test.Program.PoolPublic.closed

/-- **A borrow at a closing pool, while a holder holds.** H holds, and W waits. The scope
closes, and the closer waits for H. L awaits W's exit and then borrows: its exit is the
interruption of its own fiber, 3 on each face, before H's return. A fourth fiber awaits L's
exit, reads the cell, writes the row `[8]` and opens H's gate. While H holds, the cell reads
H's lease as it was, no idle stamp, and one waiter, which is the closer. The sync entry ends in
the `AsyncFiberError` defect. -/
def pPoolClosing : Api.Program := poolProgram "pPoolClosing" Test.Program.PoolPublic.closing

/-- The ten programs of Pool's first operations, in the lane's order. -/
def poolPrograms : List Api.Program :=
  [pPoolReuse, pPoolOrder, pPoolWaiters, pPoolLateWake, pPoolWake, pPoolMakeFails,
    pPoolCloseWaits, pPoolWithdrawn, pPoolClosed, pPoolClosing]

/-- The programs checked: the original wire, control, layer and host fixtures, followed by
the S2 error-image, S3 handler and part-4 residual fixtures, the list fold, the two programs
of an operation's binder term (the fold in a `Ref.modify`, and a step of the Queue's probe),
the rate limiter's request, a gate at `Deferred<void, never>`, a parked fiber that an
interrupt wakes, the two programs of the mask that restores, the five programs of the
Queue's first operations, the ten programs of Semaphore's first operations, and the ten
programs of Pool's first operations. Every listed program contributes one manifest entry. -/
def pInterruptEscape : Api.Program := Test.Counterexamples.InterruptEscape.escape

def corpus : List (String × Api.Program) :=
  Wire.Corpus.all ++ [("pTwo", pTwo), ("pAcquire", pAcquire), ("pAcquireClosed", pAcquireClosed),
    ("pProvide", pProvide), ("pProvideMerge", pProvideMerge), ("pProvideTwice", pProvideTwice),
    ("pDiamond", pDiamond), ("pMergeAll", pMergeAll), ("pAcquireHandle", pAcquireHandle),
    ("pFailTagged", pFailTagged), ("pSqlite", pSqlite), ("pKv", pKv),
    ("pSqlFail", pSqlFail), ("pSqlCatch", pSqlCatch), ("pSqlExit", pSqlExit), ("pSqlOrDie", pSqlOrDie),
    ("pFailText", pFailText), ("pFailBoomText", pFailBoomText), ("pTextOrDie", pTextOrDie), ("pCatchError", pCatchError),
    ("pCatchIfHit", pCatchIfHit), ("pCatchIfMiss", pCatchIfMiss), ("pCatchIfRetained", pCatchIfRetained),
    ("pTagHit", pTagHit), ("pTagMiss", pTagMiss), ("pTagTwoFail", pTagTwoFail), ("pOptionSome", pOptionSome), ("pOptionNone", pOptionNone), ("pFailPayload", pFailPayload), ("pTagPayload", pTagPayload), ("pInterruptEscape", pInterruptEscape),
    ("pJoinedFirstNumber", pJoinedFirstNumber), ("pJoinedFirstString", pJoinedFirstString),
    ("pJoinedModifyNumber", pJoinedModifyNumber), ("pJoinedModifyString", pJoinedModifyString),
    ("pFold", pFold), ("pModifyFold", pModifyFold), ("pQueueOffer", pQueueOffer),
    ("pRateRequest", pRateRequest), ("pDeferredGate", pDeferredGate),
    ("pInterruptedWait", pInterruptedWait), ("pMaskWait", pMaskWait),
    ("pMaskedRestore", pMaskedRestore), ("pLateSeen", pLateSeen), ("pQueueWake", pQueueWake),
    ("pQueueFull", pQueueFull), ("pQueueInterrupted", pQueueInterrupted),
    ("pQueueMasked", pQueueMasked), ("pQueueOrder", pQueueOrder),
    ("pSemaphoreProtectedJoined", pSemaphoreProtectedJoined),
    ("pSemaphoreScan", pSemaphoreScan), ("pSemaphoreOvertake", pSemaphoreOvertake),
    ("pSemaphoreBodiesJoined", pSemaphoreBodiesJoined),
    ("pSemaphoreInterrupted", pSemaphoreInterrupted),
    ("pSemaphoreIfAvailable", pSemaphoreIfAvailable), ("pSemaphoreMasked", pSemaphoreMasked),
    ("pSemaphoreHandoff", pSemaphoreHandoff), ("pSemaphoreProtected", pSemaphoreProtected),
    ("pSemaphoreBodies", pSemaphoreBodies),
    ("pPoolReuse", pPoolReuse), ("pPoolOrder", pPoolOrder), ("pPoolWaiters", pPoolWaiters),
    ("pPoolLateWake", pPoolLateWake), ("pPoolWake", pPoolWake),
    ("pPoolMakeFails", pPoolMakeFails), ("pPoolCloseWaits", pPoolCloseWaits),
    ("pPoolWithdrawn", pPoolWithdrawn), ("pPoolClosed", pPoolClosed),
    ("pPoolClosing", pPoolClosing)]

/-! ## The value wire -/

def errJson : Err → J
  | .boom => Lean.Json.mkObj [("boom", Lean.Json.null)]
  | .tag n => toJson n
  -- the host wires the failed pair as a two-element array, as `pair` builds it
  | .tagged t m => Lean.Json.arr #[Lean.Json.str t, Lean.Json.str m]
  | .text s => Lean.Json.str s
  -- a record payload (decisions row 120) where no type directs its image (a promoted defect's
  -- error, a child fiber's exit, a reified exit inside a value): the codec's one-key object of
  -- its canonical bytes in hexadecimal (`Schema.Codec.encodeErr`), apart from the four shapes
  -- above. At the program's own exit the error column directs it (`errJsonAt`).
  | .payload p => Lean.Json.mkObj [("payload", Lean.Json.str (Effect4.Schema.Codec.payloadHex p))]

def defectJson : Defect → J
  | .notImplemented => Lean.Json.str "notImplemented"
  | .asyncFiber => Lean.Json.str "asyncFiber"
  | .badName => Lean.Json.str "badName"
  | .missingService => Lean.Json.str "missingService"
  | .user n => Lean.Json.mkObj [("user", toJson n)]
  | .error e => Lean.Json.mkObj [("error", errJson e)]

/-! A fiber in the wire is a number. Each function below that can meet a fiber takes `fiber`,
the number that the wire writes for a machine fiber id. A compared exit passes the run's
numbering (`numberOf`, in the section on the fiber numbers below). The machine's own record
(`events`, `fibers`) passes `id`. Three fields hold a fiber: an interruptor, a fiber handle and
the handles of a snapshot. -/

def reasonJson (fiber : Nat → Nat) : Reason Err Defect FiberId Ann → J
  | .fail e _ => Lean.Json.mkObj [("fail", errJson e)]
  | .die d _ => Lean.Json.mkObj [("die", defectJson d)]
  | .interrupt none _ => Lean.Json.mkObj [("interrupt", Lean.Json.null)]
  | .interrupt (some who) _ => Lean.Json.mkObj [("interrupt", toJson (fiber who.value))]

def causeJson (fiber : Nat → Nat) (c : CauseV) : J :=
  Lean.Json.mkObj [("reasons", Lean.Json.arr (c.reasons.map (reasonJson fiber)).toArray)]

/-- Values in the wire, on the shared carrier (`Machine/Value.lean`'s table): a handle by its
kind byte, a reified exit by its constructor index with the cause read back through
`causeImage`, the snapshot by its fibers, a `list` as one array. A shape the machine never
produces renders deterministically under `"raw"`, so the wire stays total. A fiber is written
as `fiber` numbers it. -/
partial def valJson (fiber : Nat → Nat) : Val → J
  | .unit => Lean.Json.null
  | .nat n => toJson n
  | .bool b => Lean.Json.bool b
  -- strings are machine values since DB-15; the host wires a string as itself, an option as
  -- rc.112's `Option` (`{"some":v}` / `{"none":true}`, the runner's wire of `_tag`)
  | .str s => Lean.Json.str s
  | .some v => Lean.Json.mkObj [("some", valJson fiber v)]
  | .none => Lean.Json.mkObj [("none", Lean.Json.bool true)]
  | Value.external index => Lean.Json.mkObj [("external", toJson index)]
  | Value.fiber index => Lean.Json.mkObj [("fiber", toJson (fiber index))]
  | Value.fiberSnapshot handles =>
    Lean.Json.mkObj [("fibers", Lean.Json.arr
      ((((Effect4.Store.Image.list Value.fiberHandle).ofVal handles).getD []).map fun i =>
        toJson (fiber i.value)).toArray)]
  | Value.cell k => Lean.Json.mkObj [("ref", toJson k)]
  | Value.promise k => Lean.Json.mkObj [("deferred", toJson k)]
  | Value.scope s => Lean.Json.mkObj [("scope", toJson s)]
  | Value.fiberContext _ _ _ => Lean.Json.mkObj [("context", Lean.Json.bool true)]
  -- a built service map (`Env.encode`, what a layer build answers and `Effect.provide` reads):
  -- the same `Context` object on the rc.112 face
  | Value.serviceContext _ => Lean.Json.mkObj [("context", Lean.Json.bool true)]
  | Val.exitOk v => Lean.Json.mkObj [("success", valJson fiber v)]
  | Value.exitErr written =>
    Lean.Json.mkObj [("failure",
      ((causeImage.ofVal written).map (causeJson fiber)).getD Lean.Json.null)]
  | .list values => Lean.Json.arr (values.map (valJson fiber)).toArray
  | other => Lean.Json.mkObj [("raw", Lean.Json.str (toString (repr other)))]

def exitJson (fiber : Nat → Nat) : ExitV → J
  | .success v => Lean.Json.mkObj [("success", valJson fiber v)]
  | .failure c => Lean.Json.mkObj [("failure", causeJson fiber c)]

mutual
/-- The codec's JSON (`Effect4.Json`) as the manifest's (`Lean.Json`). A number is a natural
(`Schema.Codec.nat?`): the codec writes no other, and anything else is named, never rounded. An
object's keys come out in `Lean.Json`'s order, by code point, which is UTF-8 byte order. -/
def leanJson : Effect4.Json → J
  | .null => Lean.Json.null
  | .bool b => Lean.Json.bool b
  | .number f => match Effect4.Schema.Codec.nat? (.number f) with
    | some n => toJson n
    | none => Lean.Json.str "not a natural"
  | .str s => Lean.Json.str s
  | .arr items => Lean.Json.arr (leanJsons items).toArray
  | .obj entries => Lean.Json.mkObj (leanEntries entries)
/-- `leanJson` at every item. -/
def leanJsons : List Effect4.Json → List J
  | [] => []
  | j :: js => leanJson j :: leanJsons js
/-- `leanJson` at every value, keys kept. -/
def leanEntries : List (String × Effect4.Json) → List (String × J)
  | [] => []
  | (k, j) :: es => (k, leanJson j) :: leanEntries es
end

/-- A typed failure's error at the program's error column (decisions row 120, ruling (a), part
E2): a payload through the type-directed codec (`Schema.encode`), under the one key `payload`,
its objects' keys in UTF-8 byte order (`leanJson`). That is the JSON rc.112 writes for the
printed class's instance (`Data.Error`'s `toJSON`, `{ ...plainArgs, ...this }`,
`vendor/effect-4.0.0-rc.112/src/internal/core.ts:602-604`), which `run-truth.ts` sorts the same
way. Any other error, and a payload the codec does not write (a `number`, `null`, `undefined`
or byte field), is `errJson`'s. -/
def errJsonAt (errorTy : Option Ty) : Err → J
  | .payload p =>
    match errorTy.bind fun t => Effect4.Schema.encode t p.val with
    | some j => Lean.Json.mkObj [("payload", leanJson j)]
    | none => errJson (.payload p)
  | e => errJson e

/-- `reasonJson` with the failure's error at the program's error column (`errJsonAt`). -/
def reasonJsonAt (fiber : Nat → Nat) (errorTy : Option Ty) : Reason Err Defect FiberId Ann → J
  | .fail e _ => Lean.Json.mkObj [("fail", errJsonAt errorTy e)]
  | r => reasonJson fiber r

/-- The program's own exit, its failures typed by its error column: the `exit` the comparison
reads (`run.exit`, `runSync.exit`). Its fibers are written as `fiber` numbers them, which is the
run's numbering at both call sites. A child fiber's exit and the event texts keep `exitJson`. -/
def exitJsonAt (fiber : Nat → Nat) (errorTy : Option Ty) : ExitV → J
  | .success v => exitJson fiber (.success v)
  | .failure c => Lean.Json.mkObj [("failure",
      Lean.Json.mkObj [("reasons",
        Lean.Json.arr (c.reasons.map (reasonJsonAt fiber errorTy)).toArray)])]

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

/-- The events with an rc.112 counterpart, as the manifest spells them. `none` for the rest.
Recorded, never compared: a fiber keeps the machine's id here, in an exit's text too. -/
def observable : Event → Option String
  | .forked p c d => some s!"forked {p.value}->{c.value}{if d then " daemon" else ""}"
  | .started f => some s!"started {f.value}"
  | .scheduledTask o p _ => some s!"scheduledTask owner={o.value} prio={p}"
  | .ranTask o _ => some s!"ranTask owner={o.value}"
  | .yieldInjected f n => some s!"yieldInjected {f.value}@{n}"
  | .parkedOn f t => some s!"parkedOn {f.value} token={t}"
  | .resumedWith f t _ => some s!"resumedWith {f.value} token={t}"
  | .exited f e => some s!"exited {f.value} {(exitJson id e).compress}"
  | _ => none

/-- One row of the reduced schedule, over fiber numbers: the alphabet that the runner can
observe on rc.112. A fiber is forked, starts, parks, is resumed and exits (by kind), and the
dispatcher of an owner schedules a task and runs one. Tokens, tasks and exit values are
erased. -/
inductive Row where
  | forked (parent child : Nat)
  | started (fiber : Nat)
  | scheduled (owner priority : Nat)
  | ran (owner : Nat)
  | parked (fiber : Nat)
  | resumed (fiber : Nat)
  | exited (fiber : Nat) (kind : String)
deriving DecidableEq

/-- A row as the manifest and the recorder spell it. -/
def Row.text : Row → String
  | .forked parent child => s!"forked {parent} {child}"
  | .started fiber => s!"started {fiber}"
  | .scheduled owner priority => s!"scheduled {owner} {priority}"
  | .ran owner => s!"ran {owner}"
  | .parked fiber => s!"parked {fiber}"
  | .resumed fiber => s!"resumed {fiber}"
  | .exited fiber kind => s!"exited {fiber} {kind}"

/-- A row under a renaming of its fibers. A priority and an exit's kind name no fiber. -/
def Row.rename (to : Nat → Nat) : Row → Row
  | .forked parent child => .forked (to parent) (to child)
  | .started fiber => .started (to fiber)
  | .scheduled owner priority => .scheduled (to owner) priority
  | .ran owner => .ran (to owner)
  | .parked fiber => .parked (to fiber)
  | .resumed fiber => .resumed (to fiber)
  | .exited fiber kind => .exited (to fiber) kind

/-- The fiber that a row can show the recorder for the first time: the child of a `forked` row,
and the fiber of a `started` row. No other row gives a fiber its index (`numbering`). -/
def Row.sight : Row → Option Nat
  | .forked _ child => some child
  | .started fiber => some fiber
  | _ => none

/-- One event as a row, under the machine's fiber ids: the root is `0`, and a fork's child
takes the next id when the machine allocates it (`spawn`, `src/Effect4/Machine/Fibers.lean`).
A fork is no row here: `machineRows` decides which fork is a row, and where. -/
def rowOf : Event → Option Row
  | .forked _ _ _ => none   -- `machineRows` decides forks
  | .started f => some (.started f.value)
  | .scheduledTask o p _ => some (.scheduled o.value p)
  | .ranTask o _ => some (.ran o.value)
  | .parkedOn f _ => some (.parked f.value)
  | .resumedWith f _ _ => some (.resumed f.value)
  | .exited f e => some (.exited f.value (exitKind e))
  | _ => none

/-- The row-by-row projection of the trace, as texts: `rowOf` at one event. The fiber numbers
are the machine's ids, which follow the allocation order. The recorder numbers a fiber when it
first sees it, and that is another order when it sees a fiber late (`numbering`). Before
2026-10-06 this docstring said that the runner reproduces the machine's ids by first-seen
order. That is false for a scheduled daemon child that is followed by another fork before its
first run (`pQueueOrder`). `reduce` writes the compared rows under the recorder's numbers. -/
def reduced (e : Event) : Option String := (rowOf e).map Row.text

/-- The fiber an observable event belongs to, for the immediacy test below. -/
def eventFiber : Event → Option FiberId
  | .started f => some f
  | .scheduledTask o _ _ => some o
  | .ranTask o _ => some o
  | .yieldInjected f _ => some f
  | .parkedOn f _ => some f
  | .resumedWith f _ _ => some f
  | .exited f _ => some f
  | _ => none

/-- Was the fork of `c` by `p` immediate: `c` starts before `p`'s next observable event that
is not another fork. `forkUnsafe` runs an immediate child inside the parent's primitive
(`internal/effect.ts:5279`), so the parent emits nothing until the child yields or exits; a
scheduled child's fork is followed at once by the parent's `scheduledTask`. Other forks are
read through because the machine's parallel close spawns every finalizer before running the
first (`Fibers.lean`, `closePar`, `forkFinalizers`), where rc.112 forks and runs each in turn
(`:3820`): the batch is a modeling shortcut visible in `events`, and the reduced schedule
below places each immediate fork where the runner observes it. -/
def immediateFork (p c : FiberId) : List Event → Bool
  | [] => false
  | .started f :: rest => if f.value = c.value then true else immediateFork p c rest
  | .forked _ _ _ :: rest => immediateFork p c rest
  | e :: rest =>
    match eventFiber e with
    | some f => if f.value = p.value then false else immediateFork p c rest
    | none => immediateFork p c rest

/-- The reduced schedule under the machine's fiber ids: `rowOf` row by row, over the fiber
states the runner observes (DI-75, 2026-09-13). `reduce` renames these rows to the recorder's
numbers.

* A `started f` row is a fiber's transition into running — fresh, or parked and resumed —
  which is what the recorder's `context` hook can see. The machine's `started` event is its
  evaluation loop entering a fiber, and the loop re-enters the parent after a fork's
  commands (`Cmd.evaluate` on a fiber the residue marked not running, `Fibers.lean`), an
  internal re-entry rc.112's `runLoop` has no counterpart for; a `started` of a fiber that
  is already running is therefore no row.
* A fork appears exactly where the runner can observe it. An *immediate* child's fork is
  placed at the child's first step, daemon or not: the recorder attributes a fresh fiber's
  first primitive to the fiber on the stack. A *scheduled* non-daemon child joins
  `fiber._children` before it runs (`:5280-5281`) and is seen at the parent's next
  primitive, so its fork stays where the machine emits it. A scheduled daemon child is never
  registered and starts from the scheduler with no parent on the stack, so its fork stays in
  `events` only.
* **A `resumed k` row: a fiber that the trace last showed parked runs again, whatever woke
  it.** The recorder has the same definition (`context`, `harness/truth/run-truth.ts`): it
  writes `resumed k` and then `started k` at the first primitive of a fiber whose recorded
  state is parked. Two causes wake a parked fiber. A token's resume emits `resumedWith`
  (`Cmd.resume`, `Fibers.lean`). An interrupt that applies now emits `interruptRecorded` and
  then `started`, with no token (`interruptRecord`, then `Cmd.evaluate`). One restart is one
  row. `go` keeps the fibers that the trace last showed parked: a `parkedOn` adds the fiber, a
  `resumedWith` writes the row and removes the fiber, and a `started` of a fiber still in the
  set writes the row itself. So the `started` after a `resumedWith` writes no second row.
  Before 2026-10-06 the row came from `resumedWith` alone, and it meant a token's resume. No
  truth program then woke a parked fiber by an interrupt (seat MASK; the control is
  `pInterruptedWait`, with a red guard on its trace in the receipts). -/
def machineRows (trace : List Event) : List Row :=
  go trace [] [] []
where
  go : List Event → List (FiberId × FiberId) → List Nat → List Nat → List Row
    | [], _, _, _ => []
    | .forked p c daemon :: rest, pending, running, parked =>
      if immediateFork p c rest then go rest ((c, p) :: pending) running parked
      else (if daemon then [] else [.forked p.value c.value]) ++
        go rest pending running parked
    | .started f :: rest, pending, running, parked =>
      if running.contains f.value then go rest pending running parked
      else
        let running := f.value :: running
        match pending.find? (fun x => x.1.value = f.value) with
        | some (_, p) =>
          .forked p.value f.value :: .started f.value ::
            go rest (pending.filter (fun x => x.1.value ≠ f.value)) running parked
        | none =>
          -- a parked fiber that starts with no resume of its token: an interrupt applied now
          (if parked.contains f.value then [.resumed f.value] else []) ++
            .started f.value :: go rest pending running (parked.filter (· ≠ f.value))
    | .parkedOn f t :: rest, pending, running, parked =>
      (rowOf (.parkedOn f t)).toList ++
        go rest pending (running.filter (· ≠ f.value)) (f.value :: parked)
    | .resumedWith f t answer :: rest, pending, running, parked =>
      (rowOf (.resumedWith f t answer)).toList ++
        go rest pending running (parked.filter (· ≠ f.value))
    | .exited f e :: rest, pending, running, parked =>
      (rowOf (.exited f e)).toList ++
        go rest pending (running.filter (· ≠ f.value)) (parked.filter (· ≠ f.value))
    | e :: rest, pending, running, parked => (rowOf e).toList ++ go rest pending running parked

/-! ### The fiber numbers of the compared fields (2026-10-06)

The machine numbers a fiber when it allocates it. The recorder numbers a fiber when it first
sees it (`see`, `harness/truth/run-truth.ts`). It calls `see` at three places, and it writes a
row at each:

* `context`, the first call: a fiber at its first primitive while the primitive of another
  fiber is on the stack. The recorder writes `forked parent child`, and then `started child`.
* `context`, the second call: a fiber at its first primitive while no fiber is on the stack.
  This is the root, and a scheduled daemon child at its first run. The recorder writes
  `started fiber`.
* `scanChildren`: a child in `_children` that the recorder has not seen, at the next primitive
  of the parent. The recorder writes `forked parent child`.

So the index of a fiber on rc.112 is the rank of its first row among two kinds of row: a
`forked` row that names it as the child, and a `started` row that names it. `Row.sight` is that
rule. The parent of a `forked` row is on the stack or runs the scan, so the recorder has seen
it.

**A `scheduled` row and a `ran` row give no index, on either face.** On rc.112 each names the
fiber that made the dispatcher (`TracedScheduler.makeDispatcher`), which `currentFiber` reads
off the stack: the recorder has seen it. The machine writes `scheduledTask` at two places
(`start` and `RunMachine.postTask`, `src/Effect4/Machine/Fibers.lean`). A deferred start names
the parent, which runs. `postTask` posts an owed resume on a stored dispatcher, and no store
builds a scheduled wake today (`WakeMode.scheduled` has no construction site). If a later
machine writes such a row for a fiber before its first sight, the recorder decides: `see` does
not run at a `scheduled` row. The row then takes the number that the later sight gives.

The two orders differ when the recorder sees a fiber late. A scheduled daemon child has no
`forked` row on either face (`machineRows`), so the recorder first sees it at its first run. A
fiber that is forked after it and seen before that run takes the smaller index on rc.112, and
the larger id on the machine. In `pQueueOrder` the helper of the root's offer is the machine's
fiber `3` and the recorder's `4`.

`numbering` reads the recorder's order from the Lean face's own rows, by the same rule. Each
compared field that holds a fiber writes the fiber's position in it:

* every row of `run.schedule` (`reduce`): `forked`, `started`, `scheduled`, `ran`, `parked`,
  `resumed` and `exited`;
* `run.exit` and `runSync.exit` (`exitJsonAt`): an interruptor, a fiber handle and the handles
  of a snapshot. The sync run has its own trace, and so its own numbering.

Four fields keep the machine's ids. `run.events`, `run.internal` and `run.fibers` are the
machine's own record, and no comparison reads a fiber number in them. The runner reads
`run.fibers` once, for the root's park (`leanVerdict`, `f.id === 0`), and the root is `0` under
both numberings. A tape row's `fiber` is written by the recorder, and this file does not read
it (`tapeAnswer`).

What the comparison no longer checks: the machine's allocation order. A fiber's machine id is
compared in no field, so the two faces agree up to one renaming of the fibers.

Limits, stated and not solved:

* **A literal interruptor (DI-74).** `Cause.interrupt(n)` of a computed number is a number on
  both faces. The recorder writes the index of the run's fiber whose rc.112 id is `n`, when
  there is one (`reasonJson`, case `Interrupt`). This file writes the number of the machine's
  fiber `n`, when there is one. The two tests read different ids.
* **A fiber that the recorder never sees.** Its handle in a value takes an index of another
  table on rc.112 (`wire`, the table `fiber?`). Here it takes a position after every seen
  fiber.
* **A number that a program computes from an id (DI-73).** It is a number in the wire, and no
  face renames it.
* **The `exited` row of a fiber that is awaited before its first sight.** The rows differ in
  order, and no renaming repairs that. `reduce` states the cause and the evidence. -/

/-- The fibers of a list of rows in the order that the recorder first sees them: the first
sight of each (`Row.sight`), in row order. -/
def firstSeen (rows : List Row) : List Nat := (rows.filterMap Row.sight).eraseDups

/-- The machine's fibers of a trace in allocation order: the root, then the child of each fork
(`spawn`, `src/Effect4/Machine/Fibers.lean`, the one place that allocates a child). -/
def allocated (trace : List Event) : List Nat :=
  Api.root.value :: trace.filterMap fun
    | .forked _ child _ => some child.value
    | _ => none

/-- The fibers of some rows in the recorder's order: the fibers that the rows show, in the order
of their first sight, and then every other allocated fiber in allocation order. A fiber's
number is its position in this list. -/
def numberingOf (allocated : List Nat) (rows : List Row) : List Nat :=
  let seen := firstSeen rows
  seen ++ allocated.filter (!seen.contains ·)

/-- The machine's fibers of a run in the recorder's order (`numberingOf`). The list is a
permutation of the run's fibers (`allocated`), and it is `allocated` itself when the recorder
sees the fibers in allocation order. -/
def numbering (trace : List Event) : List Nat := numberingOf (allocated trace) (machineRows trace)

/-- A fiber's number in an order: its position. A number that names no fiber of the order
stays as it is: a literal interruptor outside the run (DI-74). -/
def numberIn (order : List Nat) (fiber : Nat) : Nat := (order.idxOf? fiber).getD fiber

/-- The number that a run's compared fields write for a machine fiber id. This is the one
renaming of the Lean face: `reduce` and `exitJsonAt` take it, and nothing else renames. -/
def numberOf (trace : List Event) : Nat → Nat := numberIn (numbering trace)

/-- The fibers that a run's numbering moves: each as `(machine id, number)`, in the order of
the numbers. The list is empty exactly when the recorder's order is the allocation order. -/
def moved (trace : List Event) : List (Nat × Nat) :=
  (numbering trace).zipIdx.filter fun entry => entry.1 != entry.2

/-- The lane's programs whose numbering is not the allocation order, each with the fibers that
it moves (`moved`), in its fork run and in its sync run. The receipts hold every other program
of the lane at the allocation order, and `main` holds the same on each run with its tape. A new
entry is a reviewed change: the lane then compares that program up to this renaming. -/
def lateSights : List (String × List (Nat × Nat)) :=
  [("pQueueOrder", [(4, 3), (3, 4)]), ("pLateSeen", [(2, 1), (3, 2), (1, 3)])]

/-- The lane's programs whose sync run alone is numbered apart from the allocation order, each
with the fibers that its sync run moves. The fork run of each is numbered in the allocation
order. In each a child's return posts a helper on that child's dispatcher, which the sync entry
does not flush, so the recorder never sees that helper there. The root's close posts a later
helper on the root's dispatcher, and the recorder sees it. No compared field reads a moved
number: the schedule is the fork run's, and the sync exit of each holds no fiber (a receipt
holds both). A new entry is a reviewed change, as an entry of `lateSights` is. -/
def lateSightsSync : List (String × List (Nat × Nat)) :=
  [("pPoolWaiters", [(5, 4), (4, 5)]), ("pPoolLateWake", [(5, 4), (4, 5)]),
    ("pPoolWake", [(4, 3), (3, 4)])]

/-- Rows under the numbers of an order. -/
def renumbered (order : List Nat) (rows : List Row) : List Row :=
  rows.map fun row => row.rename (numberIn order)

/-- The compared schedule: the rows of `machineRows`, each fiber under its number in the
recorder's order (`numbering`). The recorder writes its rows under its own indices, so the two
faces are compared up to one renaming of the fibers.

**What the lane no longer checks.** After this renaming the lane does not check the machine's
allocation order. The id that the machine gives a fiber is compared in no field. So the
position in that order of a fiber that the recorder sees late is not checked.

**A limit of the recorder: a fiber that is awaited before its first sight.** The recorder adds
its exit observer when it first sees a fiber. An awaiter that registered before that sight has
its observer in front. rc.112 runs the observers in order, so the recorder writes `exited k`
after the rows of the awaiter's resumption, and the machine writes `exited k` at the exit. The
rows then differ in order, and no renaming repairs that. One run on rc.112 reproduced it: a
detached child with a deferred start that the root joins before the child's first run
(`docs/research/2026-10-06-seat-pub-evidence/late-seen-joined.probe.json`). No lane program
awaits such a fiber, and the Queue's posted helpers are never awaited. The recorder is not
repaired. The section above lists this limit with the three others. -/
def reduce (trace : List Event) : List String :=
  (renumbered (numbering trace) (machineRows trace)).map Row.text

/-- The rows that the runner compares: every row but the `scheduled` rows (`compareSchedules`,
`harness/truth/run-truth.ts`). -/
def compared (rows : List String) : List String :=
  rows.filter fun row => !row.startsWith "scheduled "

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

/-- One required key and its service value shape (`null` when the signature does not type it).
The target oracle binds an ordinary requirement to the full literal `"k<name>_<service>"`,
independently of this shape, matching rc.112 `Context.Service<Identifier, Shape>` in the printer.
The signature's scope key instead uses the built-in `Scope.Scope` identity. -/
def requireJson (sig : Signature NativeOp) (key : ServiceKey) : J :=
  Lean.Json.mkObj
    [ ("name", toJson key.name.value), ("service", toJson key.service.value)
    , ("shape", match sig.serviceTy key with
        | some t => Lean.Json.str t.render
        | none => Lean.Json.null) ]

def typeJson (sig : Signature NativeOp) (ty : EffTy) : J :=
  Lean.Json.mkObj
    [ ("answer", Lean.Json.str ty.answer.render)
    , ("error", Lean.Json.str ty.error.render)
    , ("requires", Lean.Json.arr (ty.requires.elems.map (requireJson sig)).toArray)
    , ("requiresEmpty", Lean.Json.bool (decide (ty.requires = Machine.Env.Requirement.empty))) ]

/-- Why a module cannot declare a payload class (`ClassRefusal`, decisions row 120). -/
def classRefusalText : ClassRefusal → String
  | .notIdentifier => "not an identifier"
  | .collides => "collides with a bound name"
  | .fieldsDiffer => "two payload types under one tag"
  | .construction => "a construction outside the class form"
  | .unreadable => "a declaration that does not read back"

def refusalText : PrintRefusal → String
  | .internalAction name => s!"internal action {name}"
  | .layerRef target => s!"layer reference to {target}"
  | .unsafeName spelling => s!"unsafe name {spelling}"
  | .typeSpelling text => s!"type spelling {text}"
  | .payloadClass tag why => s!"payload class {tag}: {classRefusalText why}"
  | .binderTerm spelling => s!"binder term of {spelling}"

/-- One fiber of the machine's own record, under the machine's ids: its exit is recorded and
never compared. -/
def fiberJson (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) : J :=
  Lean.Json.mkObj
    [ ("id", toJson f.id.value)
    , ("exited", Lean.Json.bool f.exit.isSome)
    , ("exit", match f.exit with | some e => exitJson id e | none => Lean.Json.null)
    , ("parkedToken", match f.parked with | .withGuard t => toJson t | .notParked => Lean.Json.null) ]

def strings (xs : List String) : J := Lean.Json.arr (xs.map Lean.Json.str).toArray

/-- U-01 replays the same explicit decisions as the counterexample; other fixtures use
ordinary run/flush. The host recorder executes these decisions at the masked park. -/
def fixtureRun (name : String) (p : Api.Program) (fuel : Nat) (table : RowTable)
    (answers : List (Completion Val Err Defect FiberId Ann)) : Api.Inspection :=
  if name == "pInterruptEscape" then
    Api.replay p fuel Test.Counterexamples.InterruptEscape.poisoned answers table
  else Api.run p fuel answers table

def runJson (p : Api.Program) (fuel : Nat) (table : RowTable := [])
    (answers : List (Completion Val Err Defect FiberId Ann) := []) (name : String := "") : J :=
  let r := fixtureRun name p fuel table answers
  let trace := r.trace
  let errorTy := (Api.typeOf p table).map (·.error)
  -- the run's fibers under the recorder's numbers, in the two compared fields
  let fiber := numberOf trace
  Lean.Json.mkObj
    [ ("outcome", Lean.Json.str (outcomeText r.outcome))
    , ("exit", match r.exit with
        | some e => exitJsonAt fiber errorTy e
        | none => Lean.Json.null)
    , ("exitKind", match r.exit with | some e => Lean.Json.str (exitKind e) | none => Lean.Json.null)
    , ("fiberCount", toJson r.fiberCount)
    , ("fibers", Lean.Json.arr (r.machine.fibers.map fiberJson).toArray)
    , ("events", strings (trace.filterMap observable))
    , ("schedule", strings (reduce trace))
    , ("internal", strings (trace.filterMap internal))
    , ("frames", toJson (trace.filter isFrame).length) ]

def runSyncJson (p : Api.Program) (fuel : Nat) (table : RowTable := [])
    (answers : List (Completion Val Err Defect FiberId Ann) := []) : J :=
  let (machine, exit) := Api.runSync p fuel answers table
  Lean.Json.mkObj
    -- the sync run has its own trace, and so its own numbering
    [ ("exit", exitJsonAt (numberOf machine.trace) ((Api.typeOf p table).map (·.error)) exit)
    , ("exitKind", Lean.Json.str (exitKind exit))
    , ("sync", Lean.Json.bool (!isAsyncFiberDefect exit)) ]

/-- A declaration with its type annotation removed: the same initializer, typed by the host's
compiler alone. -/
def unannotated : TypeScript.Decl → TypeScript.Decl
  | .const c => .const { c with type := none }
  | d => d

/-- A fixture-only typed expression and declaration. Ordinary emission supplies admission,
not a certificate for the replacement initializer. Classes and hoisted layers refuse here. -/
def joinedOutput (p : Api.Program) (table : RowTable) :
    Except String (TypeScript.Expr × TypeScript.Module) := do
  let emission ← (Api.emitModule "main" p table).mapError fun
    | .illTyped => "typed fixture: ordinary admission refuses typing"
    | .formation why => s!"typed fixture: ordinary admission refuses raw formation {repr why}"
    | .print why => "typed fixture: ordinary emission refuses " ++ refusalText why
  unless emission.classDecls.isEmpty do
    throw "typed fixture: payload classes need the ordinary module producer"
  match emission.declarations with
  | [raw] =>
    unless raw.name == "main" && raw.exported do
      throw "typed fixture: expected one exported main declaration"
  | _ => throw "typed fixture: hoisted layers need the ordinary module producer"
  let sig := nativeSignature table
  let expression ← (Program.printTyped sig [] p).mapError refusalText
  let declaration ← (Program.printDecl "main" emission.typing.ty expression sig.scopeKey).mapError refusalText
  pure (expression, { header := [], imports := [], decls := [.const declaration] })

/-- Widening fixtures retain the actual typed initializer in both module views.
All other fixtures use the existing expression and ordinary module producers. -/
def fixtureOutput (name : String) (p : Api.Program) (table : RowTable) :
    Except String (TypeScript.Expr × Option TypeScript.Module) :=
  if joinedFixtures.contains name then
    (joinedOutput p table).map fun (expression, module) => (expression, some module)
  else
    (Api.print p table).mapError refusalText |>.map fun expression =>
      (expression, Api.printModule "main" p table)

def entry (fuel : Nat) (tapes : String → List (Completion Val Err Defect FiberId Ann))
    (name : String) (p : Api.Program) : J :=
  let (table, builtIn) := hostInputs name
  let runtimeTable := fixtureRuntimeTable name p table
  let answers := builtIn ++ tapes name
  let ty := Api.typeOf p table
  let output := fixtureOutput name p table
  let printed := output.map (·.1)
  -- The ordinary block retains its emission certificate. Joined fixtures use the explicit
  -- fixture adapter, with the same actual typed initializer in both declaration views.
  let module := output.toOption.bind (·.2)
  let decl := module.map fun m => String.join (m.decls.map (TypeScript.Render.decl house0))
  -- the same block with every annotation removed: what the host's compiler infers for the
  -- printed program on its own, which the type oracle compares with Lean's rendered type
  -- (an annotated `main` would only hand Lean's type back to itself)
  let declInferred := module.map fun m =>
    String.join (m.decls.map fun d => TypeScript.Render.decl house0 (unannotated d))
  Lean.Json.mkObj <|
    [ ("name", Lean.Json.str name)
    , ("scenario", if name == "pInterruptEscape" then Lean.Json.str "U-01" else Lean.Json.null)
    , ("wellTyped", Lean.Json.bool ty.isSome)
    , ("straight", Lean.Json.bool (Effect4.Program.Denote.Straight p))
    , ("type", match ty with | some t => typeJson (nativeSignature table) t | none => Lean.Json.null)
    , ("expr", match printed with
        | .ok e => Lean.Json.str (TypeScript.Render.expr house0 0 e)
        | .error _ => Lean.Json.null)
    , ("exprRefusal", match printed with
        | .ok _ => Lean.Json.null
        | .error why => Lean.Json.str why)
    , ("decl", match decl with
        | some text => Lean.Json.str text
        | none => Lean.Json.null)
    , ("declInferred", match declInferred with
        | some text => Lean.Json.str text
        | none => Lean.Json.null)
    , ("run", (runtimeTable.map fun rows => runJson p fuel rows answers name).getD Lean.Json.null)
    , ("runSync", (runtimeTable.map fun rows => runSyncJson p fuel rows answers).getD Lean.Json.null) ] ++
    (if name == "pJoinedFirstNumber" || name == "pJoinedFirstString" then
      [("genericRows", Lean.Json.arr (table.map Tools.ProfileJson.rowJson).toArray),
       ("runtimeInstanceRows", match runtimeTable with
        | some rows => Lean.Json.arr (rows.map Tools.ProfileJson.rowJson).toArray
        | none => Lean.Json.null)]
     else [])

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

/-- The generated corpus: `count` programs of the seeded generator at `depth`, named as the
printed corpus names them. -/
def corpusPrograms (count depth : Nat) : List (String × Api.Program) :=
  (List.range count).map fun i => (s!"g{i}", Test.Program.Gen.program i depth)

/-- The manifest of the generated corpus: the same shape as `manifest`, no tapes, the empty
table, so `run-truth.ts` and `tools/target/corpus.ts` read it unchanged. -/
def corpusManifest (fuel count depth : Nat) : J :=
  Lean.Json.mkObj
    [ ("format", Lean.Json.str "effect4-truth-manifest-v1")
    , ("generated", Lean.Json.str "GENERATED by harness/truth/Truth.lean --corpus — do not edit")
    , ("regenerate", Lean.Json.str s!"lake env lean -M4096 --run harness/truth/Truth.lean --corpus <out> {count} {depth}")
    , ("fuel", toJson fuel)
    , ("scopeKey", Tools.ProfileJson.flatKeyJson nativeScopeKey)
    , ("hostRows", Lean.Json.arr #[])
    , ("programs", Lean.Json.arr
        ((corpusPrograms count depth).map fun (name, p) => entry fuel (fun _ => []) name p).toArray)]

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
* **the corpus.** The programs of `corpus` (`main` prints how many); the gate re-records every
  tape under `harness/truth/tapes` on every run and refuses a byte that moved, so a committed
  tape is the answer rc.112 *just* gave, not a remembered one.
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

#guard (corpus.map (·.1)).eraseDups.length = corpus.length
#guard (corpus.map (·.1)) =
  ["p42", "pBind", "pFork", "pAwait", "pGen", "pLoop", "pCatch", "pScope", "pTwo", "pAcquire",
   "pAcquireClosed", "pProvide", "pProvideMerge", "pProvideTwice", "pDiamond", "pMergeAll", "pAcquireHandle",
   "pFailTagged", "pSqlite", "pKv", "pSqlFail", "pSqlCatch", "pSqlExit", "pSqlOrDie",
   "pFailText", "pFailBoomText", "pTextOrDie", "pCatchError", "pCatchIfHit", "pCatchIfMiss", "pCatchIfRetained",
   "pTagHit", "pTagMiss", "pTagTwoFail", "pOptionSome", "pOptionNone", "pFailPayload", "pTagPayload",
   "pInterruptEscape", "pJoinedFirstNumber", "pJoinedFirstString", "pJoinedModifyNumber", "pJoinedModifyString",
   "pFold", "pModifyFold", "pQueueOffer", "pRateRequest", "pDeferredGate",
   "pInterruptedWait", "pMaskWait", "pMaskedRestore", "pLateSeen", "pQueueWake", "pQueueFull",
   "pQueueInterrupted", "pQueueMasked", "pQueueOrder", "pSemaphoreProtectedJoined",
   "pSemaphoreScan", "pSemaphoreOvertake", "pSemaphoreBodiesJoined", "pSemaphoreInterrupted",
   "pSemaphoreIfAvailable", "pSemaphoreMasked", "pSemaphoreHandoff", "pSemaphoreProtected",
   "pSemaphoreBodies", "pPoolReuse", "pPoolOrder", "pPoolWaiters", "pPoolLateWake", "pPoolWake",
   "pPoolMakeFails", "pPoolCloseWaits", "pPoolWithdrawn", "pPoolClosed", "pPoolClosing"]
-- Decisions row 228: the fold with an outer capture and a nested fold types at a number,
-- answers `8` on the machine, and reads back whole.
#guard Api.typeOf pFold = some ⟨.nat, .never, Env.Requirement.empty⟩
#guard (Api.run pFold 1000).exit = some (.success (.nat 8))
#guard Api.roundTrip pFold = .ok pFold
-- The fold inside a `Ref.modify` with an outer capture types at a pair of numbers, answers
-- `[21, 7]` on the machine, and reads back whole.
#guard Api.typeOf pModifyFold = some ⟨.prod .nat .nat, .never, Env.Requirement.empty⟩
#guard (Api.run pModifyFold 1000).exit = some (.success (.list [.nat 21, .nat 7]))
#guard Api.roundTrip pModifyFold = .ok pModifyFold
-- its printed expression: the term's value is `a2`, the fold's binders `a3` and `a4`
#guard (Api.print pModifyFold).toOption.map (TypeScript.Render.expr house0 0) = some
  "Effect.flatMap(Effect.succeed(2), (a0) => Effect.flatMap(Ref.make(5), (a1) => Effect.flatMap(Ref.modify(a1, (a2) => pair(fold(cons(succ(a0), cons(a0, cons(3, nil()))), a2, (a3, a4) => add(a3, mul(a4, a0))), add(a2, a0))), (a2) => Effect.flatMap(Ref.get(a1), (a3) => Effect.succeed(pair(a2, a3))))))"
-- The probe's offer step, twice: the source elaborates (its first node makes the cell; a source
-- that did not elaborate is a `fail`), types at the triple, answers on the machine, and reads
-- back whole.
#guard match pQueueOffer with | .bind (.perform .refMake _) _ => true | _ => false
#guard Api.typeOf pQueueOffer = some ⟨.tuple [.bool, .nat, .nat], .never, Env.Requirement.empty⟩
#guard (Api.run pQueueOffer 1000).exit = some (.success (.list [.bool false, .nat 2, .nat 0]))
#guard Api.roundTrip pQueueOffer = .ok pQueueOffer
-- The rate limiter's request, four times: the source elaborates (its first node makes the
-- window's cell), types at the five answers, answers on the machine, and reads back whole.
#guard match pRateRequest with | .bind (.perform .refMake _) _ => true | _ => false
#guard Api.typeOf pRateRequest =
  some ⟨.tuple [.bool, .bool, .nat, .nat, .nat], .never, Env.Requirement.empty⟩
#guard (Api.run pRateRequest 1000).exit =
  some (.success (.list [.bool true, .bool false, .nat 3, .nat 1, .nat 3]))
#guard Api.roundTrip pRateRequest = .ok pRateRequest
-- The gate at `Deferred<void, never>` types at the four answers with no failure, answers on
-- the machine, and reads back whole: its type arguments are read from the call's head.
#guard Api.typeOf pDeferredGate =
  some ⟨.tuple [.bool, .bool, .bool, .nat], .never, Env.Requirement.empty⟩
#guard (Api.run pDeferredGate 1000).exit =
  some (.success (.list [.bool false, .bool true, .bool false, .nat 7]))
#guard Api.roundTrip pDeferredGate = .ok pDeferredGate
-- its printed expression: the gate's two types stand on the call's head
#guard (Api.print pDeferredGate).toOption.map (TypeScript.Render.expr house0 0) = some
  "Effect.flatMap(Deferred.make<void, never>(), (a0) => Effect.flatMap(Effect.forkChild(Effect.flatMap(Deferred.await(a0), (a1) => Effect.succeed(7)), { startImmediately: false, uninterruptible: \"inherit\" }), (a1) => Effect.flatMap(Effect.yieldNowWith(0), (a2) => Effect.flatMap(Deferred.isDone(a0), (a3) => Effect.flatMap(Deferred.succeed(a0, undefined), (a4) => Effect.flatMap(Deferred.succeed(a0, undefined), (a5) => Effect.flatMap(Fiber.join(a1), (a6) => Effect.succeed(tuple(a3, a4, a5, a6)))))))))"
-- red control: a bare `Deferred.make()` in the gate's place is refused by its spelling
#guard match Api.print pDeferredGate with
  | .ok (.call f [.call (.generic head _) [], rest]) =>
    (match Api.read (.call f [.call head [], rest]) with
      | .error (.arity "Deferred.make") => true
      | _ => false)
  | _ => false
-- A parked fiber that an interrupt wakes (the `resumed` row's second cause). The source
-- elaborates, types at the pair, answers on the machine, and reads back whole.
#guard match pInterruptedWait with
  | .bind (.perform (.deferredMakeOf .nat .never) _) _ => true
  | _ => false
#guard Api.typeOf pInterruptedWait = some ⟨.prod .bool .nat, .never, Env.Requirement.empty⟩
#guard (Api.run pInterruptedWait 1000).exit = some (.success (.list [.bool true, .nat 1]))
#guard Api.roundTrip pInterruptedWait = .ok pInterruptedWait
-- Its compared rows are the rows the recorder wrote on rc.112 (`harness/truth/result.json`):
-- the child parks, is resumed and started by the interrupt, and exits interrupted.
#guard reduce (Api.run pInterruptedWait 1000).trace =
  ["started 0", "forked 0 1", "started 1", "parked 1", "resumed 1", "started 1",
   "exited 1 interrupt", "exited 0 success"]
-- Red control of the rule. The trace holds no resume of a token: the row-by-row projection
-- (`reduced`), which wrote every `resumed` row before 2026-10-06, has no `resumed 1` here, so
-- it differs from the recorder at that one row. The interrupt is recorded instead.
#guard !((Api.run pInterruptedWait 1000).trace.filterMap reduced).contains "resumed 1"
#guard ((Api.run pInterruptedWait 1000).trace.filterMap internal).contains
  "interruptRecorded by=0 target=1"
-- One restart is one row, at either cause: a token's resume in `pDeferredGate`, where the
-- projection already has the row and the reduction adds none, and the interrupt here.
#guard ((reduce (Api.run pDeferredGate 1000).trace).filter (· == "resumed 1")).length = 1
#guard (((Api.run pDeferredGate 1000).trace.filterMap reduced).filter (· == "resumed 1")).length = 1
#guard ((reduce (Api.run pInterruptedWait 1000).trace).filter (· == "resumed 1")).length = 1
-- The mask that restores (decisions rows 244 to 246). Each source elaborates (its first node
-- makes the promise; a source that did not elaborate is a `fail`), types at its answer, answers
-- on the machine, and reads back whole.
#guard match pMaskWait with
  | .bind (.perform (.deferredMakeOf .nat .never) _) _ => true
  | _ => false
#guard match pMaskedRestore with
  | .bind (.perform (.deferredMakeOf .nat .never) _) _ => true
  | _ => false
#guard Api.typeOf pMaskWait = some ⟨.prod .bool .nat, .never, Env.Requirement.empty⟩
#guard (Api.run pMaskWait 1000).exit = some (.success (.list [.bool true, .nat 1]))
#guard Api.roundTrip pMaskWait = .ok pMaskWait
#guard Api.typeOf pMaskedRestore =
  some ⟨.tuple [.nat, .bool, .nat], .never, Env.Requirement.empty⟩
#guard (Api.run pMaskedRestore 1000).exit =
  some (.success (.list [.nat 1, .bool true, .nat 18]))
#guard Api.roundTrip pMaskedRestore = .ok pMaskedRestore
-- the printed expression of the first: the getter under a `flatMap`, the body's mask, and the
-- restore site as `pipe(body, saved)`
#guard (Api.print pMaskWait).toOption.map (TypeScript.Render.expr house0 0) = some
  "Effect.flatMap(Deferred.make<number, never>(), (a0) => Effect.flatMap(Ref.make(0), (a1) => Effect.flatMap(Effect.forkChild(Effect.flatMap(Effect.uninterruptibleMask((a2) => Effect.succeed(a2)), (a2) => Effect.uninterruptible(Effect.flatMap(Ref.update(a1, (a3) => add(a3, 1)), (a3) => Effect.flatMap(pipe(Deferred.await(a0), a2), (a4) => Ref.update(a1, (a5) => add(a5, 10)))))), { startImmediately: true, uninterruptible: \"inherit\" }), (a2) => Effect.flatMap(Fiber.interrupt(a2), (a3) => Effect.flatMap(Fiber.await(a2), (a4) => Effect.flatMap(Ref.get(a1), (a5) => Effect.succeed(tuple(causeIsInterrupt(a4), a5))))))))"
-- The mask adds no compared row: the masked wait's rows are the plain wait's, and under a
-- masked caller the child is resumed by the promise's token, after the helper parks.
#guard reduce (Api.run pMaskWait 1000).trace = reduce (Api.run pInterruptedWait 1000).trace
#guard reduce (Api.run pMaskedRestore 1000).trace =
  ["started 0", "forked 0 1", "started 1", "parked 1", "forked 0 2", "started 2", "parked 2",
   "resumed 1", "started 1", "exited 1 interrupt", "resumed 2", "started 2",
   "exited 2 success", "exited 0 success"]
-- red control: the two programs differ by the caller's mask and the helper, and by their answers
#guard pMaskWait != pMaskedRestore &&
  (Api.run pMaskWait 1000).exit != (Api.run pMaskedRestore 1000).exit
-- The fiber numbers of the compared fields (`numbering`). The rule on rows: a fiber's first
-- sight is its first `forked` row as the child or its first `started` row.
#guard firstSeen [.started 0, .forked 0 2, .started 2, .parked 2, .started 1, .started 2] = [0, 2, 1]
-- A `scheduled` row and a `ran` row give no number: the fiber `5` is first seen at its start,
-- and its two earlier rows take the number that the start gives.
#guard firstSeen [.started 0, .scheduled 5 0, .forked 0 7, .ran 5, .started 5] = [0, 7, 5]
#guard (renumbered (numberingOf [] [.started 0, .scheduled 5 0, .forked 0 7, .ran 5, .started 5])
    [.started 0, .scheduled 5 0, .forked 0 7, .ran 5, .started 5]).map Row.text =
  ["started 0", "scheduled 2 0", "forked 0 1", "ran 2", "started 2"]
-- A fiber that no row shows takes a number after every seen fiber, in allocation order.
#guard numberingOf [0, 1, 2, 3, 4] [.started 0, .forked 0 3, .started 3] = [0, 3, 1, 2, 4]
-- A number that names no fiber of the order stays: a literal interruptor outside the run.
#guard numberIn [0, 2, 3, 1] 3 = 2 && numberIn [0, 2, 3, 1] 1 = 3 && numberIn [0, 2, 3, 1] 9 = 9
-- The three fields of an exit that hold a fiber, under an order: an interruptor, a fiber
-- handle, and the handles of a snapshot. Red control of each: under `id` the machine's id stays.
#guard (reasonJson (numberIn [0, 2, 3, 1]) (.interrupt (some ⟨3⟩) .empty)).compress =
  "{\"interrupt\":2}"
#guard (valJson (numberIn [0, 2, 3, 1]) (Value.fiber 1)).compress = "{\"fiber\":3}"
#guard (valJson (numberIn [0, 2, 3, 1])
    (Value.fiberSnapshot (.list [Value.fiber 1, Value.fiber 3]))).compress = "{\"fibers\":[3,2]}"
#guard (reasonJson id (.interrupt (some ⟨3⟩) .empty)).compress = "{\"interrupt\":3}"
#guard (valJson id (Value.fiber 1)).compress = "{\"fiber\":1}"
#guard (valJson id (Value.fiberSnapshot (.list [Value.fiber 1, Value.fiber 3]))).compress =
  "{\"fibers\":[1,3]}"
-- The limit of DI-74, as a control: a literal interruptor that equals a machine id of the run
-- is written like that fiber, and one outside the run is written as it is.
#guard (reasonJson (numberIn [0, 2, 3, 1]) (.interrupt (some ⟨9⟩) .empty)).compress =
  "{\"interrupt\":9}"
-- Measured over the lane: the numbering of each program is the allocation order, in the fork
-- run and in the sync run, but for the programs of `lateSights`, which are pinned with the
-- fibers that they move. The driver holds the same on each run with its tape (`main`). A
-- program of `lateSightsSync` is pinned apart in its sync run alone.
#guard corpus.all fun (name, p) =>
  let (table, answers) := hostInputs name
  let pinned := (lateSights.lookup name).getD []
  moved (fixtureRun name p 1000 table answers).trace == pinned &&
    moved (Api.runSync p 1000 answers table).1.trace == (lateSightsSync.lookup name).getD pinned
-- No program is in both tables, and each sync pin moves a fiber.
#guard lateSightsSync.all fun entry => (lateSights.lookup entry.1).isNone && entry.2 != []
#guard moved (Api.run pQueueOrder 1000).trace = [(4, 3), (3, 4)] &&
  moved (Api.runSync pQueueOrder 1000).1.trace = [(4, 3), (3, 4)]
#guard moved (Api.run pLateSeen 1000).trace = [(2, 1), (3, 2), (1, 3)] &&
  moved (Api.runSync pLateSeen 1000).1.trace = [(2, 1), (3, 2), (1, 3)]
#guard lateSights.lookup "pQueueOrder" = some [(4, 3), (3, 4)] &&
  lateSights.lookup "pLateSeen" = some [(2, 1), (3, 2), (1, 3)]
-- red control of the measure: a single-fiber program moves no fiber, and it is no late sight
#guard moved (Api.run pFold 1000).trace = [] && lateSights.lookup "pFold" = none
-- The recorder sees every fiber of every lane program, so no number comes from the allocation
-- order's tail, and the trace's forks give the machine's own list of fibers.
#guard corpus.all fun (name, p) =>
  let (table, answers) := hostInputs name
  let run := fixtureRun name p 1000 table answers
  allocated run.trace == run.machine.fibers.map (·.id.value) &&
    (firstSeen (machineRows run.trace)).length == run.fiberCount &&
    (numbering run.trace).mergeSort == allocated run.trace
-- `pQueueOrder`, the program that showed the two orders. The root's offer posts a helper: the
-- machine's fiber `3`, a detached fork with a deferred start. The next taker is forked and
-- started at once: the machine's fiber `4`. The recorder sees that taker first.
#guard allocated (Api.run pQueueOrder 1000).trace = [0, 1, 2, 3, 4, 5, 6, 7]
#guard numbering (Api.run pQueueOrder 1000).trace = [0, 1, 2, 4, 3, 5, 6, 7]
-- Under the machine's ids the compared rows differ from the recorder's at row 7, and in nine
-- rows in all. This is the difference that the run of 2026-10-06 showed on rc.112:
-- `Lean "forked 0 4", rc.112 "forked 0 3"`.
#guard (compared ((machineRows (Api.run pQueueOrder 1000).trace).map Row.text))[7]? =
  some "forked 0 4"
#guard (compared (reduce (Api.run pQueueOrder 1000).trace))[7]? = some "forked 0 3"
#guard ((compared ((machineRows (Api.run pQueueOrder 1000).trace).map Row.text)).zip
    (compared (reduce (Api.run pQueueOrder 1000).trace))).countP (fun rows => rows.1 != rows.2) = 9
-- Its compared rows under the recorder's numbers are the rows that the recorder wrote on
-- rc.112 (`harness/truth/result.json`).
#guard reduce (Api.run pQueueOrder 1000).trace =
  ["started 0", "forked 0 1", "started 1", "parked 1", "forked 0 2", "started 2", "parked 2",
   "scheduled 0 0", "forked 0 3", "started 3", "scheduled 3 0", "parked 3", "parked 0", "ran 0",
   "started 4", "resumed 1", "started 1", "scheduled 1 0", "scheduled 1 0", "exited 1 success",
   "resumed 0", "started 0", "parked 0", "exited 4 success", "ran 3", "started 5",
   "exited 5 success", "ran 1", "started 6", "resumed 3", "started 3", "exited 3 success",
   "exited 6 success", "ran 1", "started 7", "resumed 2", "started 2", "exited 2 success",
   "resumed 0", "started 0", "exited 0 success", "exited 7 success"]
-- A renaming is no difference: the machine's rows with the fibers `3` and `4` exchanged have the
-- same rows under their own numbering.
#guard
  let rows := machineRows (Api.run pQueueOrder 1000).trace
  let exchanged := rows.map fun row =>
    row.rename fun fiber => if fiber == 3 then 4 else if fiber == 4 then 3 else fiber
  exchanged != rows &&
    renumbered (numberingOf [] exchanged) exchanged == renumbered (numberingOf [] rows) rows
-- Red control: a real difference survives the renaming. Here the helper's exit and the next
-- task's run change places (rows 23 and 24): the rows differ by more than a renaming of the
-- fibers, and they differ under their own numbering too, at those two rows.
#guard
  let rows := machineRows (Api.run pQueueOrder 1000).trace
  let other := rows.take 23 ++ ((rows.drop 23).take 2).reverse ++ rows.drop 25
  let own := (renumbered (numberingOf [] rows) rows).map Row.text
  let others := (renumbered (numberingOf [] other) other).map Row.text
  own[23]? == some "exited 4 success" && own[24]? == some "ran 3" &&
    others[23]? == some "ran 3" && others[24]? == some "exited 4 success" &&
    (own.zip others).countP (fun pair => pair.1 != pair.2) == 2
-- Red control: a fiber that starts at another time takes another number, and the rows then
-- differ in every row that names it. No renaming of fibers makes the two lists equal.
#guard
  let late : List Row :=
    [.started 0, .forked 0 1, .started 1, .parked 1, .ran 0, .started 2, .exited 2 "success"]
  let early : List Row :=
    [.started 0, .ran 0, .started 2, .exited 2 "success", .forked 0 1, .started 1, .parked 1]
  (renumbered (numberingOf [] late) late).map Row.text !=
    (renumbered (numberingOf [] early) early).map Row.text
-- `pLateSeen`, the control of the numbers in an exit. The source elaborates (its first node
-- makes the promise), types at the pair, and reads back whole.
#guard match pLateSeen with
  | .bind (.perform (.deferredMakeOf .unit .never) _) _ => true
  | _ => false
#guard Api.typeOf pLateSeen =
  some ⟨.prod (.exitOf .unit .never) (.fiberOf .nat .never), .never, Env.Requirement.empty⟩
#guard Api.roundTrip pLateSeen = .ok pLateSeen
#guard numbering (Api.run pLateSeen 1000).trace = [0, 2, 3, 1]
-- Its exit names the interruptor and the helper. Under the machine's ids they are `3` and `1`.
-- Under the recorder's numbers they are `2` and `3`, in the fork run and in the sync run: the
-- exit that rc.112 gave on both entries (`harness/truth/result.json`).
#guard ((Api.run pLateSeen 1000).exit.map fun e => (exitJsonAt id none e).compress) =
  some "{\"success\":[{\"failure\":{\"reasons\":[{\"interrupt\":3}]}},{\"fiber\":1}]}"
#guard ((Api.run pLateSeen 1000).exit.map fun e =>
    (exitJsonAt (numberOf (Api.run pLateSeen 1000).trace) none e).compress) =
  some "{\"success\":[{\"failure\":{\"reasons\":[{\"interrupt\":2}]}},{\"fiber\":3}]}"
#guard (exitJsonAt (numberOf (Api.runSync pLateSeen 1000).1.trace) none
    (Api.runSync pLateSeen 1000).2).compress =
  "{\"success\":[{\"failure\":{\"reasons\":[{\"interrupt\":2}]}},{\"fiber\":3}]}"
-- Its rows under the recorder's numbers: the helper is first seen at its start, as `3`.
#guard reduce (Api.run pLateSeen 1000).trace =
  ["started 0", "scheduled 0 0", "forked 0 1", "started 1", "parked 1", "forked 0 2", "started 2",
   "resumed 1", "started 1", "exited 1 interrupt", "exited 2 success", "parked 0", "ran 0",
   "started 3", "exited 3 success", "ran 0", "resumed 0", "started 0", "exited 0 success"]
-- The Queue's first operations (decisions rows 219 to 222, 233, 238 and 240). Each program is
-- the program that the Queue's batteries build from the same scenario, so rc.112 runs what the
-- batteries run on the Lean machine.
#guard [(Test.Program.QueueScenarios.r2, pQueueWake), (Test.Program.QueueScenarios.r4, pQueueFull),
    (Test.Program.QueueScenarios.r5, pQueueInterrupted),
    (Test.Program.QueueMask.maskedCaller, pQueueMasked),
    (Test.Program.QueueScenarios.r8, pQueueOrder)].all fun (source, program) =>
  ((Effect4.Api.Author.build (Test.Program.QueueScenarios.mk source)).toOption.map
    (·.program)) == some program
-- Each source elaborates (its first node makes the queue's cell; a source that did not
-- elaborate is a `fail`), types with no failure and no requirement, answers on the machine, and
-- reads back whole.
#guard [pQueueWake, pQueueFull, pQueueInterrupted, pQueueMasked, pQueueOrder].all fun p =>
  match p with
  | .bind (.perform .refMake _) _ => true
  | _ => false
#guard Api.typeOf pQueueWake = some ⟨.nat, .never, Env.Requirement.empty⟩
#guard Api.typeOf pQueueFull =
  some ⟨.tuple [.bool, .nat, .bool, .nat], .never, Env.Requirement.empty⟩
#guard Api.typeOf pQueueInterrupted = some ⟨.prod .nat .nat, .never, Env.Requirement.empty⟩
#guard Api.typeOf pQueueMasked =
  some ⟨.tuple [.nat, .nat, .bool, .nat, .nat], .never, Env.Requirement.empty⟩
#guard Api.typeOf pQueueOrder = some ⟨.list .nat, .never, Env.Requirement.empty⟩
#guard (Api.run pQueueWake 1000).exit = some (.success (.nat 7))
#guard (Api.run pQueueFull 1000).exit =
  some (.success (.list [.bool true, .nat 1, .bool true, .nat 2]))
#guard (Api.run pQueueInterrupted 1000).exit = some (.success (.list [.nat 5, .nat 0]))
#guard (Api.run pQueueMasked 1000).exit =
  some (.success (.list [.nat 1, .nat 9, .bool true, .nat 0, .nat 0]))
#guard (Api.run pQueueOrder 1000).exit = some (.success (.list [.nat 1, .nat 101, .nat 2]))
#guard [pQueueWake, pQueueFull, pQueueInterrupted, pQueueMasked, pQueueOrder].all fun p =>
  decide (Api.roundTrip p = .ok p)
-- The sync entry settles the first four. It does not settle the fifth: the root is parked
-- when its dispatcher has run once, which is the `AsyncFiberError` defect on both faces.
#guard [pQueueWake, pQueueFull, pQueueInterrupted, pQueueMasked].all fun p =>
  !isAsyncFiberDefect (Api.runSync p 1000).2
#guard isAsyncFiberDefect (Api.runSync pQueueOrder 1000).2
-- The taker that waits and is woken. Its compared rows are the rows that the recorder wrote on
-- rc.112 (`harness/truth/result.json`). The posted helper is the fiber `2`: it has no `forked`
-- row, the root's dispatcher starts it after the root parks, and its task resumes the taker.
#guard reduce (Api.run pQueueWake 1000).trace =
  ["started 0", "forked 0 1", "started 1", "parked 1", "scheduled 0 0", "parked 0", "ran 0",
   "started 2", "resumed 1", "started 1", "exited 1 success", "resumed 0", "started 0",
   "exited 0 success", "exited 2 success"]
-- red control: the five programs have five answers. The first two have the same rows: one
-- fiber waits, one helper is posted, and the root joins. The alphabet erases what the helper
-- carries, a wake in the first and the offer's answer in the second.
#guard ([pQueueWake, pQueueFull, pQueueInterrupted, pQueueMasked, pQueueOrder].map fun p =>
  (Api.run p 1000).exit).eraseDups.length = 5
#guard reduce (Api.run pQueueWake 1000).trace = reduce (Api.run pQueueFull 1000).trace
#guard ([pQueueWake, pQueueFull, pQueueInterrupted, pQueueMasked, pQueueOrder].map fun p =>
  reduce (Api.run p 1000).trace).eraseDups.length = 4
-- Semaphore's first operations (decisions rows 259 to 261 and 276). Each program is the program
-- that Semaphore's battery builds from the same scenario, so rc.112 runs what the battery runs
-- on the Lean machine.
#guard [(Test.Program.SemaphoreScenarios.p1Joined, pSemaphoreProtectedJoined),
    (Test.Program.SemaphoreScenarios.p2, pSemaphoreScan),
    (Test.Program.SemaphoreScenarios.p3, pSemaphoreOvertake),
    (Test.Program.SemaphoreScenarios.p4Joined, pSemaphoreBodiesJoined),
    (Test.Program.SemaphoreScenarios.p7, pSemaphoreInterrupted),
    (Test.Program.SemaphoreScenarios.ifAvailable, pSemaphoreIfAvailable),
    (Test.Program.SemaphoreScenarios.maskedCaller, pSemaphoreMasked),
    (Test.Program.SemaphoreScenarios.handoff, pSemaphoreHandoff),
    (Test.Program.SemaphoreScenarios.p1, pSemaphoreProtected),
    (Test.Program.SemaphoreScenarios.p4, pSemaphoreBodies)].all fun (source, program) =>
  ((Effect4.Api.Author.build (Test.Program.SemaphoreScenarios.mk source)).toOption.map
    (·.program)) == some program
-- Each source elaborates (its first node makes the semaphore's cell; a source that did not
-- elaborate is a `fail`), types with no failure and no requirement, answers on the machine, and
-- reads back whole.
#guard [pSemaphoreProtectedJoined, pSemaphoreScan, pSemaphoreOvertake, pSemaphoreBodiesJoined,
    pSemaphoreInterrupted, pSemaphoreIfAvailable, pSemaphoreMasked, pSemaphoreHandoff,
    pSemaphoreProtected, pSemaphoreBodies].all
  fun p => match p with
    | .bind (.perform .refMake _) _ => true
    | _ => false
#guard [pSemaphoreProtectedJoined, pSemaphoreOvertake, pSemaphoreBodiesJoined,
    pSemaphoreProtected, pSemaphoreBodies].all fun p =>
  decide (Api.typeOf p = some ⟨.tuple [.tuple [.nat, .nat, .list .nat, .list .nat],
    .tuple [.nat, .nat, .list .nat, .list .nat], .list .nat], .never, Env.Requirement.empty⟩)
#guard Api.typeOf pSemaphoreScan = some ⟨.tuple [.tuple [.nat, .nat, .list .nat, .list .nat],
  .nat, .tuple [.nat, .nat, .list .nat, .list .nat], .list .nat], .never, Env.Requirement.empty⟩
#guard Api.typeOf pSemaphoreIfAvailable = some ⟨.tuple [.option .nat,
  .tuple [.nat, .nat, .list .nat, .list .nat], .option .nat, .bool, .bool,
  .tuple [.nat, .nat, .list .nat, .list .nat], .list .nat], .never, Env.Requirement.empty⟩
#guard Api.typeOf pSemaphoreMasked = some ⟨.tuple [.tuple [.nat, .nat, .list .nat, .list .nat],
  .nat, .bool, .tuple [.nat, .nat, .list .nat, .list .nat]], .never, Env.Requirement.empty⟩
#guard Api.typeOf pSemaphoreHandoff = some ⟨.prod .nat .nat, .never, Env.Requirement.empty⟩
#guard (Api.typeOf pSemaphoreInterrupted).map (·.error) = some .never
#guard (Api.run pSemaphoreProtectedJoined 1000).exit = some (.success (.list
  [Test.Program.SemaphoreScenarios.count 2 [2, 1] [0, 1],
   Test.Program.SemaphoreScenarios.count 2 [1] [1], Test.Program.SemaphoreScenarios.marks [22]]))
#guard (Api.run pSemaphoreScan 1000).exit = some (.success (.list
  [Test.Program.SemaphoreScenarios.count 2 [2, 1] [0, 1], .nat 1,
   Test.Program.SemaphoreScenarios.count 2 [2] [0], Test.Program.SemaphoreScenarios.marks [31]]))
#guard (Api.run pSemaphoreOvertake 1000).exit = some (.success (.list
  [Test.Program.SemaphoreScenarios.count 2 [1, 1] [0, 1],
   Test.Program.SemaphoreScenarios.count 2 [1] [1],
   Test.Program.SemaphoreScenarios.marks [21, 22]]))
#guard (Api.run pSemaphoreBodiesJoined 1000).exit = some (.success (.list
  [Test.Program.SemaphoreScenarios.count 2 [2, 1] [0, 1],
   Test.Program.SemaphoreScenarios.count 0 [] [],
   Test.Program.SemaphoreScenarios.marks [22, 31]]))
#guard (Api.run pSemaphoreInterrupted 1000).exit = some (.success (.list
  [Test.Program.SemaphoreScenarios.count 1 [1] [0], Test.Program.SemaphoreScenarios.count 1 [] [],
   Test.Program.SemaphoreScenarios.count 1 [1] [1], Test.Program.SemaphoreScenarios.count 1 [] [],
   .nat 1, Test.Program.SemaphoreScenarios.count 0 [] []]))
#guard (Api.run pSemaphoreIfAvailable 1000).exit = some (.success (.list
  [.some (.nat 7), Test.Program.SemaphoreScenarios.count 0 [] [], .none, .bool true, .bool false,
   Test.Program.SemaphoreScenarios.count 2 [] [], Test.Program.SemaphoreScenarios.marks [2]]))
#guard (Api.run pSemaphoreMasked 1000).exit = some (.success (.list
  [Test.Program.SemaphoreScenarios.count 1 [1] [0], .nat 11, .bool true,
   Test.Program.SemaphoreScenarios.count 0 [] []]))
#guard (Api.run pSemaphoreHandoff 1000).exit = some (.success (.list [.nat 1, .nat 7]))
#guard [pSemaphoreProtectedJoined, pSemaphoreScan, pSemaphoreOvertake, pSemaphoreBodiesJoined,
    pSemaphoreInterrupted, pSemaphoreIfAvailable, pSemaphoreMasked, pSemaphoreHandoff,
    pSemaphoreProtected, pSemaphoreBodies].all
  fun p => decide (Api.roundTrip p = .ok p)
-- The sync entry settles six of the ten on the fork run's exit: in each the root releases, or
-- nobody waits.
#guard [pSemaphoreScan, pSemaphoreOvertake, pSemaphoreInterrupted, pSemaphoreIfAvailable,
    pSemaphoreMasked, pSemaphoreHandoff].all fun p =>
  !isAsyncFiberDefect (Api.runSync p 1000).2 &&
    some (Api.runSync p 1000).2 == (Api.run p 1000).exit
-- The two joined forms end the sync entry in the `AsyncFiberError` defect. The root waits in
-- its join, and the helper is on a child's dispatcher, which the sync entry does not flush.
#guard [pSemaphoreProtectedJoined, pSemaphoreBodiesJoined].all fun p =>
  isAsyncFiberDefect (Api.runSync p 1000).2
-- The cases P1 and P4 as the batteries write them: the two entries settle on two exits. The
-- sync run settles before the walk: the release is in the cell, both waiters still wait, and no
-- mark is written. The fork run gives the joined form's exit. The runner's exit column compares
-- the fork entry on both faces, and its sync column compares the sync entry, so the lane holds
-- both programs (decisions row 279, point 1).
#guard [pSemaphoreProtected, pSemaphoreBodies].all fun p =>
  (Api.runSync p 1000).2 == .success (.list
    [Test.Program.SemaphoreScenarios.count 2 [2, 1] [0, 1],
     Test.Program.SemaphoreScenarios.count 0 [2, 1] [0, 1],
     Test.Program.SemaphoreScenarios.marks []]) &&
  some (Api.runSync p 1000).2 != (Api.run p 1000).exit
#guard [(pSemaphoreProtected, pSemaphoreProtectedJoined),
    (pSemaphoreBodies, pSemaphoreBodiesJoined)].all fun (written, joined) =>
  (Api.run written 1000).exit == (Api.run joined 1000).exit
-- The README's example. Its compared rows are the rows of the Queue's taker that waits and is
-- woken: one fiber waits, the root posts one helper and joins. The alphabet erases what the
-- helper does, one `Deferred.succeed` there and a walk of one visit here.
#guard reduce (Api.run pSemaphoreHandoff 1000).trace = reduce (Api.run pQueueWake 1000).trace
-- The protected case: A's hook posts the helper on A's dispatcher (`scheduled 1 0`), and A
-- exits. The helper, fiber 4, resumes B. B's exit resumes the root inside the helper's task.
-- The root reads the cell and ends, and C is interrupted at the root's end. The helper exits
-- last, after the root.
#guard reduce (Api.run pSemaphoreProtectedJoined 1000).trace =
  ["started 0", "forked 0 1", "started 1", "parked 1", "forked 0 2", "started 2", "parked 2",
   "forked 0 3", "started 3", "parked 3", "parked 0", "ran 0", "resumed 0", "started 0",
   "resumed 1", "started 1", "scheduled 1 0", "exited 1 success", "parked 0", "ran 1",
   "started 4", "resumed 2", "started 2", "exited 2 success", "resumed 0", "started 0",
   "resumed 3", "started 3", "exited 3 interrupt", "exited 0 success", "exited 4 success"]
-- The sync run of the same program stops where the root waits in its join: A has exited, and
-- the helper's task has not run.
#guard reduce (Api.runSync pSemaphoreProtectedJoined 1000).1.trace =
  ["started 0", "forked 0 1", "started 1", "parked 1", "forked 0 2", "started 2", "parked 2",
   "forked 0 3", "started 3", "parked 3", "parked 0", "ran 0", "resumed 0", "started 0",
   "resumed 1", "started 1", "scheduled 1 0", "exited 1 success", "parked 0"]
-- red control: the first eight programs have eight answers and eight lists of compared rows.
-- The rows of the scan and of the overtaking differ only in which waiter the helper resumes.
-- The two cases as the batteries write them share the fork exits of their joined forms.
#guard ([pSemaphoreProtectedJoined, pSemaphoreScan, pSemaphoreOvertake, pSemaphoreBodiesJoined,
    pSemaphoreInterrupted, pSemaphoreIfAvailable, pSemaphoreMasked, pSemaphoreHandoff].map
  fun p => (Api.run p 1000).exit).eraseDups.length = 8
#guard ([pSemaphoreProtectedJoined, pSemaphoreScan, pSemaphoreOvertake, pSemaphoreBodiesJoined,
    pSemaphoreInterrupted, pSemaphoreIfAvailable, pSemaphoreMasked, pSemaphoreHandoff].map
  fun p => reduce (Api.run p 1000).trace).eraseDups.length = 8
-- Each of the eight is numbered in the allocation order: no fiber is forked between a helper's
-- post and its first run. The guard over the whole corpus above holds them there.
#guard [pSemaphoreProtectedJoined, pSemaphoreScan, pSemaphoreOvertake, pSemaphoreBodiesJoined,
    pSemaphoreInterrupted, pSemaphoreIfAvailable, pSemaphoreMasked, pSemaphoreHandoff].all
  fun p => moved (Api.run p 1000).trace == [] && moved (Api.runSync p 1000).1.trace == []
-- Pool's first operations (decisions rows 267 to 269, 276 and 279). Each program is the program
-- that Pool's battery builds from the same case, so rc.112 runs what the battery runs on the
-- Lean machine. The lane's run gives each answer that the battery pins on its own run, the
-- checked session at the tape `[evaluate root, flush]`.
#guard [(Test.Program.PoolPublic.pp1, pPoolReuse), (Test.Program.PoolPublic.pp2, pPoolOrder),
    (Test.Program.PoolPublic.pp3, pPoolWaiters), (Test.Program.PoolPublic.pp4, pPoolLateWake),
    (Test.Program.PoolPublic.pp5, pPoolWake), (Test.Program.PoolPublic.pp6, pPoolMakeFails),
    (Test.Program.PoolPublic.pp7, pPoolCloseWaits),
    (Test.Program.PoolPublic.pp8, pPoolWithdrawn), (Test.Program.PoolPublic.closed, pPoolClosed),
    (Test.Program.PoolPublic.closing, pPoolClosing)].all fun (source, program) =>
  ((Effect4.Api.Author.build (Test.Program.PoolScenarios.mk source)).toOption.map
    (·.program)) == some program &&
  (Api.run program 1000).exit.isSome &&
    (Api.run program 1000).exit == Test.Program.PoolScenarios.exitOf source
-- Each source elaborates (its first node makes the log's cell; a source that did not elaborate
-- is a `fail`), types with no failure and no requirement, and reads back whole.
#guard poolPrograms.all fun p => match p with
    | .bind (.perform .refMake _) _ => true
    | _ => false
#guard poolPrograms.all fun p =>
  decide ((Api.typeOf p).map (fun ty => (ty.error, ty.requires)) =
    some (.never, Env.Requirement.empty))
-- The closed pool's answer type: L's exit has no failure type, because an interruption is
-- outside the failure column.
#guard (Api.typeOf pPoolClosed).map (·.answer) = some (.tuple [.exitOf .unit .never,
  .tuple [.list .nat, .list .nat, .list .nat, .nat, .bool, .nat], .list (.list .nat)])
#guard poolPrograms.all fun p => decide (Api.roundTrip p = .ok p)
-- The sync entry settles five of the ten on the fork run's exit: in each no return finds a
-- waiter, so no helper is posted.
#guard [pPoolReuse, pPoolOrder, pPoolMakeFails, pPoolWithdrawn, pPoolClosed].all fun p =>
  !isAsyncFiberDefect (Api.runSync p 1000).2 &&
    some (Api.runSync p 1000).2 == (Api.run p 1000).exit
#guard [pPoolReuse, pPoolOrder, pPoolMakeFails, pPoolWithdrawn, pPoolClosed].all fun p =>
  !(reduce (Api.run p 1000).trace).any (·.startsWith "scheduled")
-- The two programs of a close that waits end the sync entry in the `AsyncFiberError` defect.
-- The closer waits, and the helper of H's return is on H's dispatcher, which the sync entry
-- does not flush.
#guard [pPoolCloseWaits, pPoolClosing].all fun p => isAsyncFiberDefect (Api.runSync p 1000).2
-- The cases PP3, PP4 and PP5 as the batteries write them: the two entries settle on two exits.
-- Under the sync entry the root's yields end before a wake. The item stays idle beside its
-- waiters, no borrower but H runs, and the finalizer's row follows H's two rows. The runner's
-- exit column compares the fork entry on both faces, and its sync column compares the sync
-- entry, so the lane holds the three programs (decisions row 279, point 1).
#guard (Api.runSync pPoolWaiters 1000).2 == .success (.list
  [.list [Test.Program.PoolScenarios.snap [] [0] [0] 2 false 1,
    Test.Program.PoolScenarios.snap [0] [] [] 2 false 1,
    Test.Program.PoolScenarios.snap [0] [] [] 2 false 1,
    Test.Program.PoolScenarios.snap [0] [] [] 2 false 1],
   Test.Program.PoolScenarios.rows [[1, 9, 1], [2, 9, 1], [9, 1]]])
#guard (Api.runSync pPoolLateWake 1000).2 == .success (.list
  [.list [Test.Program.PoolScenarios.snap [] [0] [0] 2 false 1,
    Test.Program.PoolScenarios.snap [0] [] [] 2 false 1,
    Test.Program.PoolScenarios.snap [0] [] [] 1 false 1,
    Test.Program.PoolScenarios.snap [0] [] [] 1 false 1],
   Test.Program.PoolScenarios.rows [[1, 9, 1], [2, 9, 1], [9, 1]]])
#guard (Api.runSync pPoolWake 1000).2 == .success (.list
  [.list [Test.Program.PoolScenarios.snap [] [0] [0] 1 false 1,
    Test.Program.PoolScenarios.snap [0] [] [] 1 false 1,
    Test.Program.PoolScenarios.snap [0] [] [] 1 false 1],
   Test.Program.PoolScenarios.rows [[1, 9, 1], [2, 9, 1], [9, 1]]])
#guard [pPoolWaiters, pPoolLateWake, pPoolWake].all fun p =>
  !isAsyncFiberDefect (Api.runSync p 1000).2 &&
    some (Api.runSync p 1000).2 != (Api.run p 1000).exit
-- Each of the ten is numbered in the allocation order in its fork run. The sync runs of the
-- three programs of two exits are not: the helper of a child's return is never seen there, and
-- the helper of the root's close, which is forked later, is seen. `lateSightsSync` pins the
-- three, and the sync run of every other program is in the allocation order.
#guard poolPrograms.all fun p => moved (Api.run p 1000).trace == []
#guard [pPoolWaiters, pPoolLateWake, pPoolWake].map
    (fun p => moved (Api.runSync p 1000).1.trace) =
  [[(5, 4), (4, 5)], [(5, 4), (4, 5)], [(4, 3), (3, 4)]]
#guard [pPoolReuse, pPoolOrder, pPoolMakeFails, pPoolCloseWaits, pPoolWithdrawn, pPoolClosed,
    pPoolClosing].all fun p => moved (Api.runSync p 1000).1.trace == []
-- No compared field reads a moved number: each of the three sync exits holds no fiber, so it is
-- one text under the machine's ids and under the sync run's numbers. `pLateSeen` above is the
-- red control: its exit holds a fiber, and its two texts differ.
#guard [pPoolWaiters, pPoolLateWake, pPoolWake].all fun p =>
  (exitJsonAt id none (Api.runSync p 1000).2).compress ==
    (exitJsonAt (numberOf (Api.runSync p 1000).1.trace) none (Api.runSync p 1000).2).compress
-- The two borrows at a closed pool: L's exit names L's own fiber, 1 and then 3, and the
-- allocation order is the recorder's order in both runs.
#guard ((Api.run pPoolClosed 1000).exit.map fun e =>
    (exitJsonAt (numberOf (Api.run pPoolClosed 1000).trace) none e).compress) = some
  "{\"success\":[{\"failure\":{\"reasons\":[{\"interrupt\":1}]}},[[0],[],[],0,true,0],[[9,1]]]}"
#guard ((Api.run pPoolClosing 1000).exit.map fun e =>
    (exitJsonAt (numberOf (Api.run pPoolClosing 1000).trace) none e).compress) = some
  "{\"success\":[[[],[0],[0],1,false,1],{\"failure\":{\"reasons\":[{\"interrupt\":3}]}},[[],[0],[0],1,true,1],false,[[0],[],[],0,true,1],[[1,9,1],[8],[2,9,1],[9,1]]]}"
-- The closed pool's compared rows: L starts and exits with an interruption, and no row of
-- another fiber stands between. Nobody interrupts L: it fails with its own interruption.
#guard reduce (Api.run pPoolClosed 1000).trace =
  ["started 0", "forked 0 1", "started 1", "exited 1 interrupt", "exited 0 success"]
-- The close that waits. H is fiber 1, W fiber 2 and the gate's opener fiber 3. The root's close
-- posts its helper (`scheduled 0 0`) and waits. The helper, fiber 4, wakes W, which exits with
-- its own interruption. W's exit resumes the opener, which opens H's gate. H's return posts
-- the next helper on H's dispatcher (`scheduled 1 0`). That helper, fiber 5, wakes the closer:
-- the root runs to its exit inside the helper's task.
#guard reduce (Api.run pPoolCloseWaits 1000).trace =
  ["started 0", "forked 0 1", "started 1", "parked 1", "forked 0 2", "started 2", "parked 2",
   "forked 0 3", "started 3", "parked 3", "scheduled 0 0", "parked 0", "ran 0", "started 4",
   "resumed 2", "started 2", "exited 2 interrupt", "resumed 3", "started 3", "resumed 1",
   "started 1", "scheduled 1 0", "exited 1 success", "exited 3 success", "exited 4 success",
   "ran 1", "started 5", "resumed 0", "started 0", "exited 0 success", "exited 5 success"]
-- The sync run of the same program stops where the closer waits: H's return has posted its
-- helper, and that task has not run.
#guard reduce (Api.runSync pPoolCloseWaits 1000).1.trace =
  ["started 0", "forked 0 1", "started 1", "parked 1", "forked 0 2", "started 2", "parked 2",
   "forked 0 3", "started 3", "parked 3", "scheduled 0 0", "parked 0", "ran 0", "started 4",
   "resumed 2", "started 2", "exited 2 interrupt", "resumed 3", "started 3", "resumed 1",
   "started 1", "scheduled 1 0", "exited 1 success", "exited 3 success", "exited 4 success"]
-- red control: the ten programs have ten answers and ten lists of compared rows.
#guard (poolPrograms.map fun p => (Api.run p 1000).exit).eraseDups.length = 10
#guard (poolPrograms.map fun p => reduce (Api.run p 1000).trace).eraseDups.length = 10
#guard Api.typeOf pOptionSome = some ⟨.prod .bool .nat, .never, Env.Requirement.empty⟩
#guard Api.typeOf pOptionNone = Api.typeOf pOptionSome
#guard (Api.run pOptionSome 1000).exit = some (.success (.list [.bool true, .nat 7]))
#guard (Api.run pOptionNone 1000).exit = some (.success (.list [.bool false, .nat 9]))
-- DI-17: mixed columns retain every possible failure; runtime selection is unchanged.
#guard Api.typeOf pTagHit =
  some ⟨.nat, .union .string (.prod (.lit "A") (.lit "m")), Env.Requirement.empty⟩
#guard Api.typeOf pTagMiss =
  some ⟨.nat, .union .string (.prod (.lit "A") (.lit "m")), Env.Requirement.empty⟩
#guard Api.typeOf pTagTwoFail =
  some ⟨.nat, .union (.prod (.lit "A") (.lit "m")) (.prod (.lit "B") (.lit "x")), Env.Requirement.empty⟩
#guard (Api.run pTagHit 1000).exit = some (.success (.nat 1))
#guard (Api.run pTagMiss 1000).exit = some (.failure (Cause.fail (.tagged "A" "m")))
#guard (Api.run pTagTwoFail 1000).exit =
  some (.failure ⟨[.fail (.tagged "B" "x") .empty, .fail (.tagged "A" "m") .empty]⟩)
-- S2 wire identities are distinct before any host comparison.
#guard errJson .boom == Lean.Json.mkObj [("boom", Lean.Json.null)]
#guard errJson (.text "boom") == Lean.Json.str "boom"
#guard errJson .boom != errJson (.text "boom")
-- a record payload (decisions row 120) is the codec's image, apart from the other four shapes
#guard ((Payload.image.ofVal (.ctor 0 [.list [.str "boom"], .list [.unit]])).map fun p =>
  errJson (.payload p) != errJson .boom && errJson (.payload p) ==
    Lean.Json.mkObj [("payload", Lean.Json.str (Effect4.Schema.Codec.payloadHex p))]) = some true
#guard defectJson (.error (.text "lost")) == Lean.Json.mkObj [("error", Lean.Json.str "lost")]
-- decisions row 120, part E2: the payload programs type at their record, print with their class,
-- read back, and the program's exit writes the payload through its error column (`errJsonAt`)
#guard (Api.typeOf pFailPayload).map (·.error) =
  some (.record [("_tag", false, .lit "NotFound"), ("id", false, .nat)])
#guard (Api.typeOf pTagPayload).map (·.answer) = some .nat
#guard Api.roundTrip pFailPayload = .ok pFailPayload
#guard Api.roundTrip pTagPayload = .ok pTagPayload
#guard (Api.printModule "main" pFailPayload).map (fun m =>
    String.join (m.decls.map (TypeScript.Render.decl house0))) = some
  ("export class NotFound extends Data.TaggedError(\"NotFound\")<{ readonly id: number }> {}\n" ++
   "export const main: Effect.Effect<never, NotFound, never> = Effect.fail(new NotFound({ id: 9 }))\n")
#guard ((Api.run pFailPayload 1000).exit.map fun e =>
    (exitJsonAt id ((Api.typeOf pFailPayload).map (·.error)) e).compress) =
  some "{\"failure\":{\"reasons\":[{\"fail\":{\"payload\":{\"_tag\":\"NotFound\",\"id\":9}}}]}}"
#guard (Api.run pTagPayload 1000).exit = some (.success (.nat 1))
-- untyped, a payload keeps the hexadecimal of its canonical bytes
#guard ((Api.run pFailPayload 1000).exit.map fun e =>
    (exitJsonAt id none e).compress == (exitJson id e).compress) = some true
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
-- the tagged failure types at the pair of its two literals (the literal rule, part 4: the
-- const-generic prelude `pair` infers `readonly ["SqlError", "boom"]`), evaluates to
-- `Err.tagged`, and reads back
#guard Api.typeOf pFailTagged =
  some ⟨.never, .prod (.lit "SqlError") (.lit "boom"), Env.Requirement.empty⟩
#guard (Api.run pFailTagged 1000).exit = some (.failure (Cause.fail (.tagged "SqlError" "boom")))
#guard Api.roundTrip pFailTagged = .ok pFailTagged
-- the join's fixtures are well-typed, so they cross as declarations
#guard Api.wellTyped pProvide
#guard Api.wellTyped pProvideMerge
#guard Api.wellTyped pProvideTwice
-- the host rows slice: the reference is well formed and typed by expansion, the diamond
-- prints as a two-declaration block, and both read back whole
#guard pDiamond.layerRefsWF
#guard (pDiamond.refSites []).length = 2
#guard (pProvideTwice.refSites []).isEmpty
#guard (Api.run pDiamond 1000).stores.refs = [.nat 1]
#guard (Api.run pProvideTwice 1000).stores.refs = [.nat 2]
#guard Api.wellTyped pDiamond
#guard Api.wellTyped pMergeAll
#guard (Api.printModule "main" pDiamond).map (·.decls.length) = some 2
#guard (Api.printModule "main" pMergeAll).map (·.decls.length) = some 1
#guard (Api.printModule "main" pDiamond).map Api.readModule = some (.ok pDiamond)
#guard (Api.printModule "main" pMergeAll).map Api.readModule = some (.ok pMergeAll)
#guard (Api.printModule "main" pProvideTwice).map Api.readModule = some (.ok pProvideTwice)

#guard LawfulTable acquireHandleTable
#guard Api.wellTyped pAcquireHandle acquireHandleTable
#guard (Api.run pAcquireHandle 1000 acquireHandleAnswers acquireHandleTable).exit =
  some (.success (.list [.handle 7 0, .nat 1]))
#guard (Api.run pAcquireHandle 1000 acquireHandleAnswers acquireHandleTable).stores.externals.allocated =
  ["Host.Resource"]

/-- P2b finite check of the amended observation equations on a final machine. The decision
reason names a runnable fiber or an armed owner (decisions row 201 (b), `awaitDecision_iff`). -/
def observesReasons (why : Exhaustion) (m : Api.Machine) : Bool :=
  let rs := Api.frontierReasons why m
  let host := rs.any fun | .awaitHost _ => true | _ => false
  let observation := Api.HostProtocol.observe m
  ((observation == .awaitingAsync) == host) &&
    ((observation == .terminated) == (!host && m.fibers.all (fun f => f.exit.isSome))) &&
    ((observation == .idle) == (!host && Api.hasRunnable m)) &&
    (rs.contains .awaitDecision == (why == .tape && (Api.hasRunnable m || !m.armed.isEmpty)))

#guard corpus.all fun (name, p) =>
  let (table, answers) := hostInputs name
  let m := (fixtureRun name p 1000 table answers).machine
  observesReasons .fuel m && observesReasons .tape m

-- The universal law instantiates at every corpus member, for any actual host replies.
example (p : Api.Program) (fuel : Nat) (answers : List Answer) (table : RowTable)
    (why : Exhaustion) :
    Api.HostProtocol.observe (Api.run p fuel answers table).machine = .awaitingAsync ↔
      ∃ key, .awaitHost key ∈ Api.frontierReasons why (Api.run p fuel answers table).machine :=
  (Api.observe_of_reasons why _).1

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
  if let ["--corpus", out, count, depth] := args then
    let count := count.toNat!
    let depth := depth.toNat!
    IO.FS.writeFile out ((OCaml5.Truth.corpusManifest fuel count depth).pretty 100 ++ "\n")
    IO.println s!"wrote {count} generated programs at depth {depth} to {out}"
    return
  let (out?, tapeDir) := match args with
    | [out, "--tapes", dir] => (some out, dir)
    | [out] => (some out, "harness/truth/tapes")
    | _ => (none, "harness/truth/tapes")
  let tapes ← readTapes tapeDir
  for (name, p) in OCaml5.Truth.corpus do
    let (table, builtIn) := OCaml5.Truth.hostInputs name
    let some runtimeTable := OCaml5.Truth.fixtureRuntimeTable name p table
      | throw (IO.userError s!"runtime call instance missing for {name}")
    let m := (OCaml5.Truth.fixtureRun name p fuel runtimeTable (builtIn ++ tapes name)).machine
    unless OCaml5.Truth.observesReasons .fuel m && OCaml5.Truth.observesReasons .tape m do
      throw (IO.userError s!"observation reasons disagree for {name}")
    -- the fiber numbers: the allocation order, or the pinned late sights (`lateSights`)
    unless OCaml5.Truth.moved m.trace == (OCaml5.Truth.lateSights.lookup name).getD [] do
      throw (IO.userError s!"the fiber numbering of {name} is not the one that `lateSights` pins")
  let text := (OCaml5.Truth.manifest fuel tapes).pretty 100 ++ "\n"
  match out? with
  | some out =>
    IO.FS.writeFile out text
    IO.println s!"wrote {OCaml5.Truth.corpus.length} programs to {out}"
  | _ => IO.println text
