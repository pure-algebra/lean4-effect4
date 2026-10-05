import Test.Program.Gen
import Test.Api.ExternalContract

/-!
# Test.Program.TypedCorpus — the typed coverage corpus

One checker-typed program per source construct, fiber action, layer form, generator statement
and performed operation (`raw`), and each of them in a set of type-preserving contexts
(`contexts`): masks, fork and join, fork-interrupt-join, races with and without a sleeper,
finalizers, catches, resources, generators and services. The random corpus
(`Test/Program/Gen.lean`) is drawn for the printer and reader and is well typed about one time in
three; its typed programs miss 21 constructs and all but one operation (measured 2026-09-23,
`docs/research/2026-09-23-typed-state-admission-audit.md`). This corpus is the typed complement:
the dynamic exit-type lane (`Test/Program/ExitTypeLane.lean`) runs it and the admission census
(`Test/Program/AdmissionCensus.lean`) reads its loaded code.

The pins below state that every entry and every kept context program is well typed and that
the typed programs cover every constructor of the program syntax and of `NativeOp`.
-/

set_option autoImplicit false
namespace Test.Program.TypedCorpus
open Effect4 Effect4.Program Effect4.Machine

abbrev E := Eff NativeOp
def ts : List Term → Terms | [] => .nil | t :: r => .cons t (ts r)
def es : List E → Effs NativeOp | [] => .nil | e :: r => .cons e (es r)
def ss : List (Stmt NativeOp) → Stmts NativeOp | [] => .nil | s :: r => .cons s (ss r)
def n (i : Nat) : Term := .lit (.nat i)
def u : Term := .lit .unit
def bl (x : Bool) : Term := .lit (.bool x)
def v (i : Nat) : Term := .var i
def ap (a : String) (xs : List Term) : Term := .app a (ts xs)
def opts : Supervision.ForkOptions := ⟨true, false, .inherit⟩
def key : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩
def key2 : ServiceKey := ⟨⟨5⟩, ⟨4⟩⟩
def forked : E := .withFiber (.fork (.succeed (n 1)) opts)
def withCell (k : E) : E := .bind (.perform .refMake (n 1)) k
def withPromise (k : E) : E := .bind (.perform (.deferredMakeOf .nat .nat) u) k
def withScope (k : E) : E := .bind (.perform (.scopeMake .sequential) u) k
/-- A corpus program with the row table it is checked and run under. -/
structure Entry where
  name : String
  program : E
  table : RowTable := []

def raw : List (String × E × RowTable) := [
  ("succeed", .succeed (n 1), []), ("fail", .fail (n 7), []),
  ("failCause.fail", .failCause (.fail (n 7)), []), ("failCause.interrupt", .failCause (.interrupt none), []),
  ("failCause.die", .failCause (.die (n 3)), []),
  ("sync", .sync (n 1), []), ("suspend", .suspend (.succeed (n 1)), []),
  ("bind", .bind (.succeed (n 1)) (.succeed (ap "succ" [v 0])), []),
  ("gen", .gen (ss [.bindYield (.succeed (n 1)), .ret (v 0)]), []),
  ("gen.loop", .gen (ss [.whileTrue (ss [.yieldDiscard (.succeed (n 1)), .breakLoop]), .ifElse (bl true) (ss [.ret (n 1)]) (ss [.ret (n 2)])]), []),
  ("catchCause", .catchCause (.fail (n 7)) (.succeed (n 0)), []),
  ("matchCause", .matchCause (.succeed (n 1)) (.succeed (v 0)) (.succeed (n 0)), []),
  ("onExit", .onExit (.succeed (n 1)) (.succeed u), []),
  ("exit", .exit (.fail (n 7)), []),
  ("uninterruptible", .uninterruptible (.succeed (n 1)), []), ("interruptible", .interruptible (.succeed (n 1)), []),
  ("yieldNow", .yieldNow 0, []),
  ("awaitFiber.join", .bind forked (.awaitFiber (v 0) .joinEffect), []),
  ("awaitFiber.value", .bind forked (.awaitFiber (v 0) .awaitValue), []),
  ("scoped", .scoped (.succeed (n 1)), []),
  ("acquireRelease", .scoped (.bind (.acquireRelease (.succeed (n 7)) (.succeed u)) (.succeed (v 0))), []),
  ("provideService", .provideService key (n 100) (.service key), []),
  ("provideLayer.succeed", .provideLayer (.succeed key (.nat 100)) false (.service key), []),
  ("provideLayer.local", .provideLayer (.succeed key (.nat 100)) true (.service key), []),
  ("layer.effect", .scoped (.provideLayer (.effect key (.succeed (n 1))) false (.service key)), []),
  ("layer.effectDiscard", .provideLayer (.merge (.effectDiscard (.succeed u)) (.succeed key (.nat 1))) false (.service key), []),
  ("layer.provide", .provideLayer (.provide (.succeed key (.nat 1)) (.succeed key2 (.nat 2))) false (.service key), []),
  ("layer.provideMerge", .provideLayer (.provideMerge (.succeed key (.nat 1)) (.succeed key2 (.nat 2))) false (.service key), []),
  ("layer.merge", .provideLayer (.merge (.succeed key (.nat 1)) (.succeed key2 (.nat 2))) false (.service key2), []),
  ("layer.fresh", .provideLayer (.fresh (.succeed key (.nat 1))) false (.service key), []),
  ("layer.orDie", .scoped (.provideLayer (.orDie (.effect key (.fail (n 3)))) false (.service key)), []),
  ("layer.mergeAll", .provideLayer (.mergeAll (.cons (.succeed key (.nat 1)) .nil)) false (.service key), []),
  ("layer.ref", .bind (.provideLayer (.succeed key (.nat 7)) false (.service key)) (.provideLayer (.ref [0, 0]) false (.service key)), []),
  ("catchIf", .catchIf (bl true) (.fail (n 7)) (.succeed (n 0)), []),
  ("select.bool", .select (bl true) .bool (.succeed (n 10)) (.succeed (n 20)), []),
  ("select.option", .select (ap "some" [n 4]) .option (.succeed (n 0)) (.succeed (v 0)), []),
  ("failCause.both", .failCause (.both (.fail (n 7)) (.interrupt none)), []),
  ("iterate", .iterate none (n 0) (ap "lt" [v 0, n 3]) (ap "succ" [v 0]) (v 0) (.succeed u), []),
  ("iterate.typed", .iterate (some .nat) (n 0) (ap "lt" [v 0, n 3]) (ap "succ" [v 0]) (v 0) (.succeed u), []),
  ("fork", forked, []),
  ("forkIn", withScope (.withFiber (.forkIn (.succeed (n 1)) opts (v 0))), []),
  ("forkScoped", .scoped (.withFiber (.forkScoped (.succeed (n 1)) opts)), []),
  ("runIn", .bind forked (withScope (.withFiber (.runIn (v 0) (v 1)))), []),
  ("interrupt", .bind forked (.withFiber (.interrupt (v 0))), []),
  ("interruptScoped", .bind forked (.withFiber (.interruptScoped (v 0))), []),
  ("interruptAll", .bind forked (.withFiber (.interruptAll (ap "cons" [v 0, ap "nil" []]) none)), []),
  ("awaitAll", .bind forked (.withFiber (.awaitAll (ap "cons" [v 0, ap "nil" []]))), []),
  ("awaitAllFailFast", .bind forked (.withFiber (.awaitAllFailFast (ap "cons" [v 0, ap "nil" []]))), []),
  ("snapshotChildren", .withFiber .snapshotChildren, []),
  ("awaitNewChildren", .bind (.withFiber .snapshotChildren) (.withFiber (.awaitNewChildren (v 0))), []),
  ("raceAll", .withFiber (.raceAll (es [.succeed (n 1), .succeed (n 2)])), []),
  ("getContext", .withFiber .getContext, []),
  ("setContext", .bind (.withFiber .getContext) (.withFiber (.setContext (v 0))), []),
  ("getId", .withFiber .getId, []),
  ("closeScope", .bind (.exit (.succeed u)) (withScope (.withFiber (.closeScope (v 1) (v 0)))), []),
  ("refGet", withCell (.perform .refGet (v 0)), []),
  ("refSet", withCell (.perform .refSet (ap "pair" [v 0, n 2])), []),
  ("refModify", withCell (.perform (.refModifyWith (FnName.image .modify 1 .incr)) (v 0)), []),
  ("refGetAndSet", withCell (.perform .refGetAndSet (ap "pair" [v 0, n 2])), []),
  ("refSetAndGet", withCell (.perform .refSetAndGet (ap "pair" [v 0, n 2])), []),
  ("refUpdate", withCell (.perform (.refUpdateWith (FnName.image .update 1 .incr)) (v 0)), []),
  ("refGetAndUpdate", withCell (.perform (.refGetAndUpdateWith (FnName.image .update 1 .double)) (v 0)), []),
  ("refUpdateAndGet", withCell (.perform (.refUpdateAndGetWith (FnName.image .update 1 .incr)) (v 0)), []),
  ("refUpdateSome", withCell (.perform (.refUpdateSomeWith (FnName.image .updateSome 1 .zeroWhenPositive)) (v 0)), []),
  ("refGetAndUpdateSome", withCell (.perform (.refGetAndUpdateSomeWith (FnName.image .updateSome 1 .zeroWhenPositive)) (v 0)), []),
  ("refUpdateSomeAndGet", withCell (.perform (.refUpdateSomeAndGetWith (FnName.image .updateSome 1 .zeroWhenPositive)) (v 0)), []),
  ("refModifySome", withCell (.perform (.refModifySomeWith (FnName.image .modifySome 1 .takeAndBump)) (v 0)), []),
  ("deferredIsDone", withPromise (.perform .deferredIsDone (v 0)), []),
  ("deferredFail", withPromise (.bind (.perform .deferredFail (ap "pair" [v 0, n 3])) (.perform .deferredAwait (v 0))), []),
  ("deferredAwait.fork", withPromise (.bind (.withFiber (.fork (.perform .deferredSucceed (ap "pair" [v 0, n 3])) opts)) (.perform .deferredAwait (v 0))), []),
  ("scopeMake", .perform (.scopeMake .sequential) u, []),
  ("scopeMake.parallel", .perform (.scopeMake .parallel) u, []),
  ("deferredAwait", withPromise (.bind (.perform .deferredSucceed (ap "pair" [v 0, n 3])) (.perform .deferredAwait (v 0))), []),
  ("deferredPoll", withPromise (.perform .deferredPoll (v 0)), []),
  ("sleep", .perform .sleep (n 1), []), ("clockNow", .perform .clockNow u, []),
  ("external", .perform (.external 0) (n 1), Test.Api.ExternalContract.table)]

def entries : List Entry := raw.map fun (name, program, table) => { name, program, table }

def ctxs : List (String × (E → E)) := [
  ("id", id), ("mask", .uninterruptible), ("unmask", .interruptible), ("suspend", .suspend), ("scoped", .scoped),
  ("then", fun e => .bind e (.succeed (v 0))),
  ("forkJoin", fun e => .bind (.withFiber (.fork e opts)) (.awaitFiber (v 0) .joinEffect)),
  ("forkValue", fun e => .bind (.withFiber (.fork e opts)) (.awaitFiber (v 0) .awaitValue)),
  ("forkInterrupt", fun e => .bind (.withFiber (.fork e opts)) (.bind (.withFiber (.interrupt (v 0))) (.awaitFiber (v 0) .joinEffect))),
  ("race2", fun e => .withFiber (.raceAll (es [e, e]))),
  ("raceSleep", fun e => .withFiber (.raceAll (es [e, .bind (.perform .sleep (n 5)) e]))),
  ("onExit", fun e => .onExit e (.succeed u)), ("onExitSleep", fun e => .onExit e (.perform .sleep (n 1))),
  ("catchSelf", fun e => .catchCause e e), ("exit", .exit),
  ("maskedSleepThen", fun e => .catchCause (.uninterruptible (.bind (.perform .sleep (n 1)) e)) e),
  ("acquire", fun e => .scoped (.bind (.acquireRelease e (.succeed u)) (.succeed (v 0)))),
  ("gen", fun e => .gen (ss [.bindYield e, .ret (v 0)])),
  ("service", fun e => .provideService key2 (n 9) e)]

/-- The contexts under which each entry is kept when the checker still types it. -/
def contexts : List (String × (E → E)) := ctxs

/-- Every entry in every context the checker types, the entry itself first. -/
def programs : List Entry :=
  entries.flatMap fun e => contexts.filterMap fun (cn, c) =>
    let p := c e.program
    if Api.wellTyped p e.table then some { e with name := cn ++ "/" ++ e.name, program := p } else none

/-- The contexts that move interrupts, masks, timers and finalizers against each other. -/
def interleaving : List String :=
  ["mask", "unmask", "scoped", "forkJoin", "forkInterrupt", "race2", "raceSleep", "onExitSleep",
   "catchSelf", "maskedSleepThen", "acquire"]

/-- Every entry under every ordered pair of interleaving contexts the checker types. -/
def pairPrograms : List Entry :=
  let inner := contexts.filter fun c => interleaving.contains c.1
  entries.flatMap fun e => inner.flatMap fun (a, f) => inner.filterMap fun (b, g) =>
    let p := f (g e.program)
    if Api.wellTyped p e.table then some { e with name := a ++ "." ++ b ++ "/" ++ e.name, program := p }
    else none

/-! ## Pins -/

#guard entries.all fun e => Api.wellTyped e.program e.table
#guard (entries.map (·.name)).eraseDups.length == entries.length
#guard programs.length ≥ 1300
#guard pairPrograms.length ≥ 7000

section Coverage
open Test.Program.Gen (heads casesOf)
open Effect4.Store.ProgramGen.EffC (EffShape StmtShape ActionTermShape LayerTermShape)

/-- Every case of the program syntax, as `family.constructor`. -/
def allCases : List (Test.Program.Gen.Head × String) :=
  casesOf "Eff" EffShape ++ casesOf "Stmt" StmtShape ++ casesOf "ActionTerm" ActionTermShape ++
    casesOf "LayerTerm" LayerTermShape

/-- The cases no typed program of this corpus uses. -/
def missing : List String :=
  let covered := (programs.flatMap fun e => heads e.program).eraseDups
  (allCases.filter fun c => !covered.contains c.1).map fun c => c.1.1 ++ "." ++ c.2

#guard missing = []
end Coverage

/-- The operations the typed programs perform, by constructor index. -/
def performed : List Nat :=
  (programs.flatMap fun e =>
    foldMap_eff [] (· ++ ·) e.program (f_eff := fun | .perform op _ => [op.ctorIdx] | _ => [])).eraseDups

-- Every `NativeOp` constructor is performed by some typed program.
run_cmd do
  let env ← Lean.getEnv
  let some (.inductInfo info) := env.find? ``Effect4.Program.NativeOp
    | throwError "NativeOp is not an inductive"
  let absent := (info.ctors.zipIdx.filter fun (_, i) => !performed.contains i).map (·.1)
  unless absent.isEmpty do throwError "typed corpus: operations never performed: {absent}"

end Test.Program.TypedCorpus
