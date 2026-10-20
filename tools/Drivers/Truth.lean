import Test.Counterexamples.Machine.Semantics.InterruptEscape
import Test.Codegen.TermRows
import Test.Program.MaskContract
import Test.Program.BoundsControls
import Compiler.Emit
import Test.Program.QueueMask
import Test.Program.SemaphoreScenarios
import Test.Program.PoolPublicData
import Test.Program.DefinitionsControls
import Test.Program.InvokeControls
import Test.Program.QueueDefs
import Test.Codegen.ServicesPrint
import Tools.ProfileJson
import Effect4.Api.Codegen
import Test.Api.HostList
import TypeScript.Render
import Lean.Data.Json

/-!
# Truth — the truth corpus: Lean's programs, their printed modules and their manifest

What it is: the hand corpus of `Eff` programs (`corpus`: `Effect4.Program.Wire.Corpus.all`,
`pTwo` of `git:14e6835:src/OCaml5/Bridge.lean`, and the fixtures below), each program's row table
and built-in host answers (`hostInputs`), and one writer of two outputs, under `Test/Corpus/`:

    lake env lean -M4096 --run tools/Drivers/Truth.lean --corpus Test/Corpus

`make gen-truth-corpus` runs it, with the native core loaded. No gate runs it.

* `generated/<name>.ts`, one module per program: the module text of every lane
  (`moduleOf`, over `Tools.Code.programModule`; decisions row 392, P1 (a)). It is the checked
  emission's file, its pieces printed typed, or, for a program the emission refuses, the
  program printed plain as `main`, with its imports from Lean data, the prelude's host
  namespaces (`hostImports`) from `ts/prelude/prelude.ts` (`preludePath`), and the compiler's
  layout under a lane's header (`Compiler.moduleFile`, `Compiler.generatedHeader`). The target lane
  (`tools/target/profile.ts`) and the reader lane (`ts/eff/check.ts`) read these modules.
* `corpus.json`, the manifest. At the top: `scopeKey`, the scope's service key, and `hostRows`,
  the host fixture's rows (`acquireHandleTable`). Per program: `name`; `type`
  (`{answer, error, requires}` as `Ty.render` spells them, `null` when ill-typed); and `run`.
  The target lane reads `type`, `scopeKey` and `hostRows` (`tools/target/profile.ts`,
  `tools/Tools/RowTypes.lean`). The OCaml engine's cross face reads `run`
  (`Corpora.truth_expectations`, `ocaml/engine/test/reference/corpora.ml`).

`run` is `Api.run p fuel`, or for a program with built-in host answers its run under a host that
answers from a list (`Test.Api.HostList`: the session, each answer a decision, DI-23):
`outcome` (`finished`, `frontier`, `stuck …`), `exit` (the root's exit in the wire below, `null`
while the root is live), `exitKind` and `fiberCount`. A canonical package fixture (`pSqlite`,
`pKv`, the four `pSql*` programs) has no built-in answers, so its run parks at its first host
call.

The value wire: `unit` ↦ `null`, `nat` ↦ number, `bool` ↦ boolean, a tuple / exit list ↦ JSON
array, `fiber k` ↦ `{"fiber":k}` (the machine's fiber id), `cell k` ↦ `{"ref":k}`, `promise k` ↦
`{"deferred":k}`, `scopeHandle k` ↦ `{"scope":k}`, `context` ↦ `{"context":true}`, a reified exit
↦ `{"success":v}` / `{"failure":cause}`; a cause is `{"reasons":[…]}` with
`{"fail":n|string|{"boom":null}|[tag,message]|{"payload":hex}}`, where the program's own exit
writes a payload through its error column, `{"fail":{"payload":{"_tag":…,…}}}` (`errJsonAt`,
decisions row 120, ruling (a)), `{"die":d}`, where `d` is the defect as rc.112's
`Schema.Defect()` writes the thrown value (`Schema.Codec.encodeDefect`, the owner's ruling R5),
and `{"interrupt":who|null}`. Annotations are dropped.

History. Until 2026-10-20 this file was the Lean face of the rc.112 truth differential: the
manifest also carried each module's text, the sync run, the observable schedule under the
recorder's fiber numbers and the machine's events, and the runner
(`git:8e93a284f:harness/truth/run-truth.ts`) ran every module on rc.112 and compared. The owner
retired the differential from the gates on 2026-10-18 and deleted it on 2026-10-20: the
comparison, the recorded results, the tapes, the ledgers and the release lane
(`git:fa7bdc304:tools/Drivers/Truth.lean`). The fixtures' docstrings below keep that history:
where one names an rc.112 run, a recorder row, a schedule or the runner's columns, it records the
retired differential's evidence.

Why one file: a `--run` tool can import only Lake modules, so the library half (`OCaml5.Truth`,
everything above `main`) and the thin driver (`main`) share this file. The library half is pure;
`main` only writes.

Behaviours held:

* deterministic — the outputs are a function of the corpus and the fuel (by construction: no IO
  above `main`);
* total under fuel — every run is `Api.run`, the U-01 replay or the list host's run, at the given
  fuel, a frontier when it runs out, never a hang (by construction);
* honest about refusals — a program whose module the printer refuses stops the driver, which
  names the refusal and writes nothing;
* one module per program — the names are unique (the guard at the end), and the driver removes
  every other module of the folder.
-/

open Lean (ToJson toJson)

/-- `Lean.Json`, named apart from `Effect4.Json` (the tree's own JSON carrier, which
`open Effect4` brings into scope). -/
abbrev J := Lean.Json

namespace OCaml5.Truth

open Effect4 Effect4.Api Effect4.Machine Effect4.Program

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

def strs (xs : List String) : Term := .app "strings" (xs.foldr (fun s t => .cons (.lit (.str s)) t) .nil)
def pairT (a b : Term) : Term := .app "pair" (.cons a (.cons b .nil))

/-- The sqlite fixture over the canonical `SqliteBun` table (host rows step 6): open the
`:memory:` client, create, insert through `strings` parameters (JSON text, decoded by the
host before binding), select, and close at the scope's end. rc.112's answers were its tape
(`git:fa7bdc304:harness/truth/tapes/pSqlite.jsonl`), deleted with the differential. -/
def pSqlite : Api.Program :=
  .scoped (.bind (.acquireRelease (.perform (.external 0) (.lit (.str ":memory:")))
                                  (.perform (.external 2) (.var 0)))
    (.bind (.perform (.external 1) (pairT (.var 0) (pairT (.lit (.str "CREATE TABLE t (a INTEGER, b TEXT)")) (strs []))))
      (.bind (.perform (.external 1) (pairT (.var 0) (pairT (.lit (.str "INSERT INTO t (a, b) VALUES (?, ?)")) (strs ["7", "\"x\""]))))
        (.perform (.external 1) (pairT (.var 0) (pairT (.lit (.str "SELECT a, b FROM t")) (strs [])))))))

/-- The key-value fixture over the canonical `KeyValueStoreMemory` table: make, set, get,
has, remove; the answer is the `(get, has)` pair. rc.112's answers were its tape
(`git:fa7bdc304:harness/truth/tapes/pKv.jsonl`), deleted with the differential. -/
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
defect, compared as represented error data). rc.112's answers were the tapes
`pSql*.jsonl` (`git:fa7bdc304:harness/truth/tapes`), deleted with the differential. -/

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
built-in host answers of a unit-declared fixture (`pAcquireHandle`). A canonical package
fixture has no built-in answers: its tape went with the differential (2026-10-20). -/
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
  guard ((Program.programCalls sig [] p).length == 1)
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

/-- **A fiber that the recorder sees late, named in an exit**: the differential's control of the
recorder's fiber numbers in an exit (`numbering`, `git:fa7bdc304:tools/Drivers/Truth.lean`). The
manifest now writes the machine's ids. The helper is the machine's fiber `1`: a
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

/-! ### Two outcomes that 4.0.1 changes (the alignment plan, 2026-10-12)

The probes `poisonNoHandler` and `closeInterruptedMidFinalizer` of seat A401
(`docs/research/2026-10-05-seat-A401/probes/backlog.mjs`), written in the language. They are the
truth programs of items 1 and 2 of `docs/research/2026-10-12-probe-alignment-plans.md`. The
release lane read the same program on 4.0.1 (`git:fa7bdc304:scripts/check-truth-release.py`).
Where the machine follows 4.0.1, the rc.112 lane signed the program (`LATEST` in
`git:8e93a284f:harness/truth/run-truth.ts`). -/

open Effect4.Program.Authoring in
/-- The source of `poisonNoHandler`. -/
def poisonNoHandlerSrc : Src NativeOp := eff do
  let d ← Deferred.make .nat .never
  let f ← fork (uninterruptible (eff do
    let _ ← Deferred.await d
    fail (nat 42)))
  let stop ← fork (withFiber (Action.interrupt f))
  let _ ← Deferred.succeed d (nat 7)
  let e ← await f
  let _ ← await stop
  return tuple [e, app "causeIsFail" [e], app "causeIsInterrupt" [e]]

/-- **A masked region fails after an interrupt was recorded, and no handler is above it.** A child
waits at a promise inside `Effect.uninterruptible`, then fails with `42`. A helper fiber
interrupts it while it waits, which only records the interrupt. The main fiber completes the
promise and awaits both. The program answers `[the child's exit, causeIsFail, causeIsInterrupt]`.
rc.112's walk skips the mask's restoring continuation and passes the cause on unchanged
(`vendor/effect-4.0.0-rc.112/src/internal/core.ts:529-547`): the child's exit is `Fail(42)`.
4.0.1 adds the recorded interrupt after the walk (`vendor/effect-4.0.1/src/internal/core.ts:580-608`):
`Fail(42), Interrupt(2)`, the helper under the recorder's number. The machine answers as 4.0.1:
the skipped restoring mask adds the recorded interrupt (`FrameFiber.skippedCause`,
`src/Effect4/Machine/Frames.lean`). A source that does not elaborate is a failure with a text,
never a patched program. -/
def poisonNoHandler : Api.Program :=
  match Effect4.Program.Authoring.elaborate poisonNoHandlerSrc with
  | .ok p => p
  | .error _ => .fail (.lit (.str "poisonNoHandler: the source does not elaborate"))

open Effect4.Program.Authoring in
/-- The source of `closeInterruptedMidFinalizer`. -/
def closeInterruptedMidFinalizerSrc : Src NativeOp := eff do
  let log ← Ref.make (nat 0)
  let d ← Deferred.make .nat .never
  let _ ← scope (eff do
    let _ ← acquireRelease "r" "x" (succeed unit) (Ref.update "l" (app "add" [var "l", nat 1]) log)
    let _ ← withFiber (Action.forkScoped (uninterruptible (Deferred.await d)) daemonOptions)
    let s ← service nativeScopeKey
    let v ← exit (succeed unit)
    let closer ← fork (withFiber (Action.closeScope s v))
    let stop ← fork (withFiber (Action.interrupt closer))
    let _ ← Deferred.succeed d (nat 7)
    let e ← await closer
    let _ ← await stop
    return app "causeIsInterrupt" [e])
  Ref.get log

/-- **An explicit `Scope.close` whose closer is interrupted while a finalizer runs.** Inside
`Effect.scoped` the scope holds two finalizers: a release that adds `1` to a log, registered
first, and the link of a daemon that waits at a promise under `Effect.uninterruptible`,
registered second. A forked closer runs `Scope.close` on the scope that `Scope.Scope` reads. The
close runs the link first: it interrupts the daemon, which only records the interrupt, and
awaits the daemon's exit. A helper fiber interrupts the closer during that wait. The main fiber
completes the promise and awaits both. The program answers the log. rc.112 closes at the
closer's own mask (`vendor/effect-4.0.0-rc.112/src/internal/effect.ts:3775-3776`): the interrupt
ends the close, the scope is already closed, and the release never runs, so the log is `0`.
4.0.1 masks the closer before it closes (`vendor/effect-4.0.1/src/internal/effect.ts:3929-3935`):
the close runs to its end, and the log is `1`. The machine answers as 4.0.1: it masks the
closer (`WithFiberAction.closeScope`, `src/Effect4/Machine/Fibers.lean`).

The interrupted finalizer is the link, not a release: the machine runs a capture's release
masked (`EffThunk.releaseMasked`, `src/Effect4/Program/Compile.lean`), so an interrupt inside a
release already differs from rc.112 (`docs/research/2026-10-12-close-mask-receipt.md`). A
source that does not elaborate is a failure with a text, never a patched program. -/
def closeInterruptedMidFinalizer : Api.Program :=
  match Effect4.Program.Authoring.elaborate closeInterruptedMidFinalizerSrc with
  | .ok p => p
  | .error _ => .fail (.lit (.str "closeInterruptedMidFinalizer: the source does not elaborate"))

/-! ### The Queue's first operations (decisions rows 219 to 222, 233, 238 and 240)

Five programs over the library's operations (`src/Effect4/Library/Queue/Ops.lean`): the first
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

Ten programs over the library's operations (`src/Effect4/Library/Semaphore/Ops.lean`): the
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
`git:8e93a284f:harness/truth/run-truth.ts`; decisions row 279, point 1). Until 2026-10-06 that
column took rc.112's sync exit whenever the sync run settled, and it was red for these two
programs. The two red rows of that rule are in
`docs/research/2026-10-06-seat-semw-evidence/README.md`. In a
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

Ten programs over the library's operations (`src/Effect4/Library/Pool/Ops.lean`): the first
host runs of Pool's expansion. Each is a case of `Test/Program/PoolPublicData.lean`, so the program
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
Queue's first operations, the ten programs of Semaphore's first operations, the ten
programs of Pool's first operations, the programs with a definition block (four plain ones, one
with a module layer, three whose body counts its own layer's builds, and three invocations with
programs), the Queue's scenario R4 over its definitions, the Queue and the Semaphore as
services, each with its client through the key, and the two programs of the alignment plan.
Every listed program contributes one manifest entry. -/
def pInterruptEscape : Api.Program := Test.Counterexamples.InterruptEscape.escape

/-- Four programs with a definition block (decisions row 328, slice PROC-3): one invocation,
two definitions that invoke each other to each answer, and an invocation inside a fork. Each
prints as a module: its definitions are constants before the main declaration. -/
def pDefsTwice : Api.Program := Test.Program.DefinitionsControls.twiceProg
def pDefsEven : Api.Program := Test.Program.DefinitionsControls.evenOdd 6
def pDefsOdd : Api.Program := Test.Program.DefinitionsControls.evenOdd 7
def pDefsFork : Api.Program := Test.Program.DefinitionsControls.forkProg

/-- A block with a module layer (decisions row 341, step 2): a definition's body and the main
program each provide the module's one layer by reference. It prints as a module whose layer is
one constant, `L_2_0`, named in both. -/
def pDefsModuleLayer : Api.Program := Test.Program.DefinitionsControls.moduleLayerProg

/-! ### A body's own layer, built once per call (decisions row 341, step 3; DI-71's counted builds)

Three blocks whose definition's body provides its own counted layer, `layerCount kA`. The counter
is the module's layer `[2, 0]`, `Layer.effect(kRef, Ref.make(0))`: the main program provides it
around the calls, and each body provides it again by reference, which finds the main program's
build, so every build of the counted layer bumps the one cell. No header needs a service, so a
call can pass a program that calls again (a callback that needs one is refused,
`callbackRequirement`). Each program answers the count. rc.112 builds one layer object per run
of the body, which the module prints as a body's layer in its suspension (`printDefs`). -/

/-- The module's counter: one cell, made by the module's one layer. -/
def counterLayers : LayerTerms NativeOp :=
  .cons (.effect kRef (.perform .refMake (.lit (.nat 0)))) .nil

/-- The body of `withCount`: the module's counter, then its own counted layer at `[0, 0, 1, 0]`,
around `inner`. -/
def countedBody (inner : NativeEff) : NativeEff :=
  .provideLayer (.ref [2, 0]) false (.provideLayer (layerCount kA) false inner)

/-- `withCount : number → number`. -/
def countedDecl : DefDecl := { name := "withCount", request := .nat, answer := .nat }

/-- **Two calls, one after the other, build twice**: the first call's build ends with its
provide, so the second builds its own. The count is `2` on both faces, under the key by path
alone or by path and call. -/
def pDefsBodyLayerCalls : Api.Program :=
  .defs [countedDecl] (.cons (countedBody (.service kA)) .nil)
    (.provideLayer (.ref [2, 0]) false
      (.bind (.perform (.call 0) (.lit (.nat 1)))
        (.bind (.perform (.call 0) (.lit (.nat 2)))
          (.bind (.service kRef) (.perform .refGet (.var 2))))))
    counterLayers

/-- **One call provides its layer twice, by a reference, and builds once**: the reference names
the body's own layer, the one object of the call's suspension, and the inner provide finds the
outer one's build. The count is `1`. -/
def pDefsBodyLayerShared : Api.Program :=
  .defs [countedDecl]
    (.cons (countedBody (.provideLayer (.ref [0, 0, 1, 0]) false (.service kA))) .nil)
    (.provideLayer (.ref [2, 0]) false
      (.bind (.perform (.call 0) (.lit (.nat 1)))
        (.bind (.service kRef) (.perform .refGet (.var 1)))))
    counterLayers

/-- `withCount : number → number`, which runs its parameter `f` inside its counted layer. -/
def countedParamDecl : DefDecl :=
  { countedDecl with params := [{ name := "f", request := .nat, answer := .nat }] }

/-- **A call nested in another, through the program the outer one passed, builds again**:
`withCount(1, (a0) => withCount(a0, (a1) => Effect.succeed(a1)))`. rc.112's inner run of the body
makes a new layer object, which the outer build's memo map does not hold, so the count is `2`;
the machine keys the build by its path and the running call (step 3a), and the two calls are
apart. A key by path alone would hand the inner call the outer build, and count `1`. -/
def pDefsBodyLayerNested : Api.Program :=
  .defs [countedParamDecl] (.cons (countedBody (.perform (.param 0) (.var 0))) .nil)
    (.provideLayer (.ref [2, 0]) false
      (.bind (.invoke 0 (.lit (.nat 1))
          (.cons (.invoke 0 (.var 0) (.cons (.succeed (.var 1)) .nil)) .nil))
        (.bind (.service kRef) (.perform .refGet (.var 1)))))
    counterLayers

/-- Invocations with programs (decisions row 340, slice HO-3b): `twice` runs its parameter on its
request and on the answer; `outer` passes its own parameter on to `twice`; `forked` runs its
parameter in a fork it joins. Each prints as the definition's name on the request and on the
program as an arrow. -/
def pInvokeTwice : Api.Program := Test.Program.InvokeControls.invokeProg
def pInvokeForward : Api.Program := Test.Program.InvokeControls.forwardProg
def pInvokeForked : Api.Program := Test.Program.InvokeControls.forkProg

/-- **The scenario R4 over the Queue's definitions** (decisions row 328, slice PROC-4): a second
offer waits at capacity one, and the take that frees room accepts it. Each operation is an
invocation of a definition of the module's block, and the printed module declares each
definition once. Its exit is `pQueueFull`'s. -/
def pQueueDefs : Api.Program :=
  match Effect4.Program.Authoring.elaborateModule
      (Test.Program.QueueDefs.mkDefs (Test.Program.QueueScenarios.r4With Test.Program.QueueDefs.invoked)) with
  | .ok p => p
  | .error _ => .fail (.lit (.str "pQueueDefs: the source does not elaborate"))

/-- **The Queue as a service** (decisions rows 338 and 339, slice CO-6b S3): the Queue's
definitions with their roles, so the module prints the service's key `NumberQueue` and its layer
`NumberQueueLayer` (`printServices`). Its main program is the client written over the
definitions: it builds the queue once, offers `1` and takes, and answers both. -/
def pQueueService : Api.Program :=
  Test.Codegen.ServicesPrint.queueProgram.getD
    (.fail (.lit (.str "pQueueService: the module does not build")))

/-- `fn(args)` of a dotted head, as the printer spells a head (`Effect.flatMap`). -/
def callOf (head : String) (args : List TypeScript.Expr) : TypeScript.Expr := .call (.ident head) args

/-- `(x) => body`. -/
def arrowOf (x : String) (body : TypeScript.Expr) : TypeScript.Expr := .lambda [{ name := x }] body

/-- The same client through the service's key, in TypeScript syntax: the layer builds the queue
once, and the client reaches it only through the methods. The module holds it after `main`
(`moduleOf`), so its imports cover it, tsgo checks it against the printed key, and the runner
runs it on rc.112 beside `main`:
`Effect.provide(Effect.flatMap(NumberQueue, (q) => Effect.flatMap(q.offer(1), (a) =>
Effect.map(q.take(), (x) => tuple(a, x)))), NumberQueueLayer)`. -/
def queueServiceClient : TypeScript.Expr :=
  callOf "Effect.provide"
    [ callOf "Effect.flatMap" [.ident "NumberQueue", arrowOf "q" (callOf "Effect.flatMap"
        [ .method (.ident "q") "offer" [.int 1]
        , arrowOf "a" (callOf "Effect.map"
            [.method (.ident "q") "take" [], arrowOf "x" (callOf "tuple" [.ident "a", .ident "x"])]) ])]
    , .ident "NumberQueueLayer" ]

/-- **The Semaphore as a service** (decisions rows 338 and 339, slice CO-6b): two permits; the
main program takes two, tries to take one, and releases one, each through a definition. The
calls tell one captured semaphore from fresh state (CO6B-SEMAPHORE-CAPTURE). -/
def pSemaphoreService : Api.Program :=
  Test.Codegen.ServicesPrint.semaphoreProgram.getD
    (.fail (.lit (.str "pSemaphoreService: the module does not build")))

/-- The same client through the `Permits` key, in TypeScript syntax:
`Effect.provide(Effect.flatMap(Permits, (s) => Effect.flatMap(s.take(2), (a) =>
Effect.flatMap(s.takeIfAvailable(1), (b) => Effect.map(s.release(1), (c) => tuple(a, b, c))))),
PermitsLayer)`. -/
def semaphoreServiceClient : TypeScript.Expr :=
  callOf "Effect.provide"
    [ callOf "Effect.flatMap" [.ident "Permits", arrowOf "s" (callOf "Effect.flatMap"
        [ .method (.ident "s") "take" [.int 2]
        , arrowOf "a" (callOf "Effect.flatMap"
            [ .method (.ident "s") "takeIfAvailable" [.int 1]
            , arrowOf "b" (callOf "Effect.map"
                [ .method (.ident "s") "release" [.int 1]
                , arrowOf "c" (callOf "tuple" [.ident "a", .ident "b", .ident "c"]) ]) ]) ])]
    , .ident "PermitsLayer" ]

/-- The programs whose module exports a service, each with its client through the key. -/
def serviceClients : List (String × TypeScript.Expr) :=
  [("pQueueService", queueServiceClient), ("pSemaphoreService", semaphoreServiceClient)]

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
    ("pPoolClosing", pPoolClosing),
    ("pDefsTwice", pDefsTwice), ("pDefsEven", pDefsEven), ("pDefsOdd", pDefsOdd),
    ("pDefsFork", pDefsFork), ("pDefsModuleLayer", pDefsModuleLayer),
    ("pDefsBodyLayerCalls", pDefsBodyLayerCalls), ("pDefsBodyLayerShared", pDefsBodyLayerShared),
    ("pDefsBodyLayerNested", pDefsBodyLayerNested),
    ("pInvokeTwice", pInvokeTwice), ("pInvokeForward", pInvokeForward),
    ("pInvokeForked", pInvokeForked), ("pQueueDefs", pQueueDefs),
    ("pQueueService", pQueueService),
    ("pSemaphoreService", pSemaphoreService),
    ("poisonNoHandler", poisonNoHandler),
    ("closeInterruptedMidFinalizer", closeInterruptedMidFinalizer)]

/-! ## The value wire -/

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

/-- A defect as rc.112's `Schema.Defect()` writes the thrown value: the codec's encoding
(`Schema.Codec.encodeDefect`) under the program's key names, which the table that prints the
program's module gives its keys (`(nativeSignature table).keyNames`), so a missing service's
message names the key as the printed module's tag does. A defect that the codec refuses, outside
the canonical alphabet or past the bound, is named, never rounded. -/
def defectJson (names : KeyNames) (d : Defect) : J :=
  match Effect4.Schema.Codec.encodeDefect names d with
  | some j => leanJson j
  | none => Lean.Json.mkObj [("refused", Lean.Json.str "no canonical defect image")]

/-! A fiber in the wire is a number. Each function below that can meet a fiber takes `fiber`,
the number that the wire writes for a machine fiber id. The manifest's run passes `id`, the
machine's own ids. Three fields hold a fiber: an interruptor, a fiber handle and the handles
of a snapshot. -/

def reasonJson (names : KeyNames) (fiber : Nat → Nat) : Reason Err Defect FiberId Ann → J
  | .fail e _ => Lean.Json.mkObj [("fail", errJson e)]
  | .die d _ => Lean.Json.mkObj [("die", defectJson names d)]
  | .interrupt none _ => Lean.Json.mkObj [("interrupt", Lean.Json.null)]
  | .interrupt (some who) _ => Lean.Json.mkObj [("interrupt", toJson (fiber who.value))]

def causeJson (names : KeyNames) (fiber : Nat → Nat) (c : CauseV) : J :=
  Lean.Json.mkObj [("reasons", Lean.Json.arr (c.reasons.map (reasonJson names fiber)).toArray)]

/-- Values in the wire, on the shared carrier (`Machine/Value.lean`'s table): a handle by its
kind byte, a reified exit by its constructor index with the cause read back through
`causeImage`, the snapshot by its fibers, a `list` as one array. A shape the machine never
produces renders deterministically under `"raw"`, so the wire stays total. A fiber is written
as `fiber` numbers it. -/
partial def valJson (names : KeyNames) (fiber : Nat → Nat) : Val → J
  | .unit => Lean.Json.null
  | .nat n => toJson n
  | .bool b => Lean.Json.bool b
  -- strings are machine values since DB-15; the host wires a string as itself, an option as
  -- rc.112's `Option` (`{"some":v}` / `{"none":true}`, the runner's wire of `_tag`)
  | .str s => Lean.Json.str s
  | .some v => Lean.Json.mkObj [("some", valJson names fiber v)]
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
  | Val.exitOk v => Lean.Json.mkObj [("success", valJson names fiber v)]
  | Value.exitErr written =>
    Lean.Json.mkObj [("failure",
      ((causeImage.ofVal written).map (causeJson names fiber)).getD Lean.Json.null)]
  | .list values => Lean.Json.arr (values.map (valJson names fiber)).toArray
  | other => Lean.Json.mkObj [("raw", Lean.Json.str (toString (repr other)))]

def exitJson (names : KeyNames) (fiber : Nat → Nat) : ExitV → J
  | .success v => Lean.Json.mkObj [("success", valJson names fiber v)]
  | .failure c => Lean.Json.mkObj [("failure", causeJson names fiber c)]

/-- A typed failure's error at the program's error column (decisions row 120, ruling (a), part
E2): a payload through the type-directed codec (`Schema.encode`), under the one key `payload`,
its objects' keys in UTF-8 byte order (`leanJson`). That is the JSON rc.112 writes for the
printed class's instance (`Data.Error`'s `toJSON`, `{ ...plainArgs, ...this }`,
`vendor/effect-4.0.0-rc.112/src/internal/core.ts:602-604`), which the deleted runner sorted the
same way (`git:8e93a284f:harness/truth/run-truth.ts`). Any other error, and a payload the codec does
not write (a `number`, `null`, `undefined` or byte field), is `errJson`'s. -/
def errJsonAt (names : KeyNames) (errorTy : Option Ty) : Err → J
  | .payload p =>
    match errorTy.bind fun t => Effect4.Schema.encode names t p.val with
    | some j => Lean.Json.mkObj [("payload", leanJson j)]
    | none => errJson (.payload p)
  | e => errJson e

/-- `reasonJson` with the failure's error at the program's error column (`errJsonAt`). -/
def reasonJsonAt (names : KeyNames) (fiber : Nat → Nat) (errorTy : Option Ty) :
    Reason Err Defect FiberId Ann → J
  | .fail e _ => Lean.Json.mkObj [("fail", errJsonAt names errorTy e)]
  | r => reasonJson names fiber r

/-- The program's own exit, its failures typed by its error column: the manifest's `run.exit`.
Its fibers are written as `fiber` numbers them. A child fiber's exit keeps `exitJson`. -/
def exitJsonAt (names : KeyNames) (fiber : Nat → Nat) (errorTy : Option Ty) : ExitV → J
  | .success v => exitJson names fiber (.success v)
  | .failure c => Lean.Json.mkObj [("failure",
      Lean.Json.mkObj [("reasons",
        Lean.Json.arr (c.reasons.map (reasonJsonAt names fiber errorTy)).toArray)])]

/-- The kind of an exit, with the archived tracer's precedence (`outcomeWire`): a `Fail`
reason wins, then an `Interrupt`, then a `Die`; an empty cause is its own kind. -/
def exitKind : ExitV → String
  | .success _ => "success"
  | .failure c =>
    if c.reasons.any (fun | .fail _ _ => true | _ => false) then "fail"
    else if c.reasons.any (fun | .interrupt _ _ => true | _ => false) then "interrupt"
    else if c.reasons.any (fun | .die _ _ => true | _ => false) then "die"
    else "empty"

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

/-- The program's type as the target lane reads it (`tools/target/profile.ts`): the answer, the
error and each required key. -/
def typeJson (sig : Signature NativeOp) (ty : EffTy) : J :=
  Lean.Json.mkObj
    [ ("answer", Lean.Json.str ty.answer.render)
    , ("error", Lean.Json.str ty.error.render)
    , ("requires", Lean.Json.arr (ty.requires.elems.map (requireJson sig)).toArray) ]

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
  | .callbackRequirement path => s!"callback requirement at {path}"
  | .invocation definition => s!"invocation of definition {definition}"
  | .emptyBlock => "an empty definition block"
  | .bodies position => s!"declarations and bodies part at definition {position}"
  | .serviceName name => s!"service name {name} declared twice"
  | .strayMethod definition service => s!"method {definition} of undeclared service {service}"
  | .service name => s!"service {name}"
  | .serviceMethod service method => s!"method {service}.{method}"
  | .declarations services types =>
    s!"an application that declares {services} services and {types} named types"

/-- The exits of a list of host answers. -/
def exitsOf (answers : List (Completion Val Err Defect FiberId Ann)) : List ExitV :=
  answers.filterMap fun | .ofExit ex => some ex | .ofRefGet _ => none

/-- U-01 replays the same explicit decisions as the counterexample; the host recorder executes
these decisions at the masked park. A fixture with host answers runs under a host that answers
from a list (`Test.Api.HostList`): each answer is a decision of the session, taken in the order
the session meets the calls (DI-23). Other fixtures use ordinary run/flush. -/
def fixtureRun (name : String) (p : Api.Program) (fuel : Nat) (table : RowTable)
    (answers : List (Completion Val Err Defect FiberId Ann)) : Api.Inspection :=
  if name == "pInterruptEscape" then
    Api.replay p fuel Test.Counterexamples.InterruptEscape.poisoned table
  else if answers.isEmpty then Api.run p fuel table
  else
    match Test.Api.HostList.run p table (exitsOf answers) { fuel, compileFuel := fuel } with
    | some run => run.inspect
    | none => Api.run p fuel table

/-- Lean's run of the program at `fuel`: its outcome, its exit, the exit's kind and its number
of fibers, the four fields that the OCaml engine's cross face reads
(`Corpora.truth_expectations`, `ocaml/engine/test/reference/corpora.ml`). The exit's fibers are
the machine's ids. -/
def runJson (names : KeyNames) (p : Api.Program) (fuel : Nat) (table : RowTable)
    (answers : List (Completion Val Err Defect FiberId Ann)) (name : String) : J :=
  let r := fixtureRun name p fuel table answers
  let errorTy := (Api.typeOf p table).map (·.error)
  Lean.Json.mkObj
    [ ("outcome", Lean.Json.str (outcomeText r.outcome))
    , ("exit", match r.exit with
        | some e => exitJsonAt names id errorTy e
        | none => Lean.Json.null)
    , ("exitKind", match r.exit with | some e => Lean.Json.str (exitKind e) | none => Lean.Json.null)
    , ("fiberCount", toJson r.fiberCount) ]

/-- The path a truth module imports its prelude from: `ts/prelude/prelude.ts`, from the modules'
folder `Test/Corpus/generated/`. -/
def preludePath : String := "../../../ts/prelude/prelude.ts"

/-- **The truth lane's host is its prelude.** A module file leaves free each namespace of the
table's rows that is no service (`ModuleEmission.file`: a row that is no service row is the
host's), and the prelude binds those this lane's fixtures name: `Host`, `L`, `Sql` and `Kv` of
`ts/prelude/prelude.ts`. So a module imports from the prelude each such namespace that it names,
in one import after the file's own, read off the table (`serviceParts`): no list of names. -/
def hostImports (table : RowTable) (m : TypeScript.Module) : TypeScript.Module :=
  let spaces := ((table.filter fun row => row.serviceCall?.isNone).filterMap fun row =>
    (serviceParts row.spelling).map (·.1)).eraseDups
  let free := (Effect4.Codegen.freeNames m).filter fun p => spaces.contains p.1
  if free.isEmpty then m
  else { m with imports := m.imports ++
    [.named (free.map fun p => { imported := p.1, localName := p.1, typeOnly := p.2 }) preludePath false] }

/-- **One program's module, as the lane writes it**: the one writer of every lane
(`Tools.Code.programModule`): the checked emission's file, its pieces printed typed, or the
unchecked file of a program the emission refuses, with the host's imports (`hostImports`) and
the lane's header. The flag says whether the module is the checked emission's. -/
def moduleOf (header : List String) (name : String) (p : Api.Program) :
    Except PrintRefusal (TypeScript.Module × Bool) :=
  let (table, _) := hostInputs name
  (Tools.Code.programModule preludePath p table).map fun (m, checked) =>
    -- a service's client is a declaration of the module, so the file's imports cover it
    let m := match serviceClients.lookup name with
      | some client => Effect4.Codegen.fileOf preludePath
          { m with decls := m.decls ++ [.const { doc := [], name := "client", value := client }] }
      | none => m
    ({ hostImports table m with header }, checked)

/-- The header of every printed module: a lane's (`Compiler.generatedHeader`). -/
def truthHeader : List String :=
  Compiler.generatedHeader "tools/Drivers/Truth.lean from the truth corpus" "make gen-truth-corpus"

/-- A program's module text, laid out by the compiler (`Compiler.moduleFile`), or the printer's
refusal. -/
def moduleText (name : String) (p : Api.Program) : Except PrintRefusal String :=
  (moduleOf truthHeader name p).map fun (m, _) => Compiler.moduleFile m

/-- One program's manifest entry: its name, Lean's type under its table, and Lean's run. -/
def entry (fuel : Nat) (name : String) (p : Api.Program) : J :=
  let (table, answers) := hostInputs name
  -- the key names of the table that prints the module: a missing service's defect spells its key
  -- as the module's tag does (`defectJson`)
  let names := (nativeSignature table).keyNames
  Lean.Json.mkObj
    [ ("name", Lean.Json.str name)
    , ("type", match Api.typeOf p table with
        | some t => typeJson (nativeSignature table) t
        | none => Lean.Json.null)
    , ("run", ((fixtureRuntimeTable name p table).map fun rows =>
        runJson names p fuel rows answers name).getD Lean.Json.null) ]

/-- The manifest: the generated mark, the scope's key, the host fixture's rows and one entry
per program of the corpus, in its order. -/
def manifest (fuel : Nat) : J :=
  Lean.Json.mkObj
    [ ("generated", Lean.Json.str "GENERATED by tools/Drivers/Truth.lean — do not edit")
    , ("scopeKey", Tools.ProfileJson.flatKeyJson nativeScopeKey)
    , ("hostRows", Lean.Json.arr (acquireHandleTable.map Tools.ProfileJson.rowJson).toArray)
    , ("programs", Lean.Json.arr (corpus.map fun (name, p) => entry fuel name p).toArray) ]

/-! ## Receipts -/

-- One module file per program: the corpus's names are unique.
#guard (corpus.map (·.1)).eraseDups.length = corpus.length

end OCaml5.Truth

/-- The driver: `--corpus <dir>` writes the manifest to `<dir>/corpus.json` and each program's
module to `<dir>/generated/<name>.ts`, and it removes every other `.ts` file of that folder. A
program whose module the printer refuses stops the driver before it writes. The fuel is fixed
at `1000`, enough for every corpus program to settle or park. -/
def main (args : List String) : IO UInt32 := do
  let ["--corpus", dir] := args | do
    IO.eprintln "usage: lake env lean --run tools/Drivers/Truth.lean --corpus <dir>"; return 2
  let fuel := 1000
  let mut modules : Array (String × String) := #[]
  for (name, p) in OCaml5.Truth.corpus do
    match OCaml5.Truth.moduleText name p with
    | .ok text => modules := modules.push (name, text)
    | .error why => do
      IO.eprintln s!"FAIL truth corpus: the printer refuses {name}: {OCaml5.Truth.refusalText why}"
      return 1
  let generated := (dir : System.FilePath) / "generated"
  IO.FS.createDirAll generated
  for file in ← generated.readDir do
    if file.fileName.endsWith ".ts" && !modules.any (·.1 ++ ".ts" == file.fileName) then
      IO.FS.removeFile file.path
  for (name, text) in modules do
    IO.FS.writeFile (generated / (name ++ ".ts")) text
  IO.FS.writeFile ((dir : System.FilePath) / "corpus.json")
    ((OCaml5.Truth.manifest fuel).pretty 100 ++ "\n")
  IO.println s!"wrote {modules.size} programs to {dir}: corpus.json and generated/"
  return 0
