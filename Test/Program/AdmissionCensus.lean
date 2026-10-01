import Test.Program.TypedCorpus
import Test.Counterexamples.Machine.Semantics.TrivialPosts

/-!
# Test.Program.AdmissionCensus — which protocol rows the generated code reaches

The admission census of decision row 89. For every typed-corpus program it loads the reference
machine (`loadR`) and walks the root's code, answering each operation with a realistic answer
(a handle for an allocation, a fiber for a fork, a successful exit otherwise), and records the
protocol rows reached.

First phase (2026-09-23, before the repair): 33 of the 77 entries reached a row whose post was
`True`, which refuses every program consuming its answer (`E4-SCHED-CE-013`). After the repair
(typed-state admission audit §6) no consumed row has a `True` post; `fiberPostTrivial_sound`
checks the two that keep one (`suspend`, `refuse`) against the protocol. The shape-only rows the
repair left (the context read, the memo lookup) were closed by decision row 90 (2026-09-24). The
census now reports the rows reached and the correlated ones, whose certified type the state
predicate or the host protocol pins.

This is a report, not a proof: the walk follows one answer per operation and under-approximates
the rows a program reaches, and a program the report calls clear is a candidate, not an
admitted program. The repaired shapes' admission is checked in
`Test/Counterexamples/Machine/Semantics/TrivialPosts.lean` and `Test/Program/TypedControl.lean`.
-/

set_option autoImplicit false
namespace Test.Program.AdmissionCensus
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Program.Typed Test.Program.TypedCorpus
abbrev W := Effect4.Program.Typed.World

/-- Rows whose postcondition in `Typed/Residual.lean` is still `True`: `suspend`, whose
continuation ignores its answer, and `refuse`, refused by its precondition. -/
def fiberPostTrivial : FiberOp → Bool
  | .refuse _ | .suspend _ => true
  | _ => false

theorem fiberPostTrivial_sound : (op : FiberOp) → fiberPostTrivial op = true →
    ∀ (w : W) (cert : FiberCert op) ans, fiberPost w op cert ans
  | .fork _ _ _, h => Bool.noConfusion h
  | .forkIn _ _ _ _, h => Bool.noConfusion h
  | .forkScoped _ _ _, h => Bool.noConfusion h
  | .await _ _, h => Bool.noConfusion h
  | .awaitAll _, h => Bool.noConfusion h
  | .awaitAllFailFast _, h => Bool.noConfusion h
  | .yieldNow _, h => Bool.noConfusion h
  | .async _ _, h => Bool.noConfusion h
  | .interrupt _, h => Bool.noConfusion h
  | .interruptAs _ _, h => Bool.noConfusion h
  | .interruptScoped _, h => Bool.noConfusion h
  | .interruptAll _ _, h => Bool.noConfusion h
  | .mask _ _, h => Bool.noConfusion h
  | .closeScope _ _, h => Bool.noConfusion h
  | .scoped _, h => Bool.noConfusion h
  | .scopeExit _ _ _, h => Bool.noConfusion h
  | .foreignRelease _ _, h => Bool.noConfusion h
  | .raceAll _ _, h => Bool.noConfusion h
  | .raceRegister _, h => Bool.noConfusion h
  | .cancelRace _, h => Bool.noConfusion h
  | .getId, h => Bool.noConfusion h
  | .getContext, h => Bool.noConfusion h
  | .setContext _, h => Bool.noConfusion h
  | .snapshotChildren, h => Bool.noConfusion h
  | .awaitNewChildren _, h => Bool.noConfusion h
  | .runIn _ _, h => Bool.noConfusion h
  | .dropObservers _, h => Bool.noConfusion h
  | .refuse _, _ => fun _ _ _ => trivial
  | .ambientScope, h => Bool.noConfusion h
  | .closeWalk _ _ _, h => Bool.noConfusion h
  | .closeIter _ _ _, h => Bool.noConfusion h
  | .frontier _ _, h => Bool.noConfusion h
  | .guard_ _, h => Bool.noConfusion h
  | .unguard _, h => Bool.noConfusion h
  | .finishFinalizer _, h => Bool.noConfusion h
  | .suspend _, _ => fun _ _ _ => trivial
  | .sync _, h => Bool.noConfusion h
  | .gen _, h => Bool.noConfusion h
  | .loop _ _, h => Bool.noConfusion h
  | .construction, h => Bool.noConfusion h

/-- How a reached row bears on admission. `correlated`: the answer's certified type is pinned
by the state predicate or the host protocol, not by the row's precondition (a race's
registration, a host slot's park); admission holds, adequacy is theirs. `clear`: otherwise.
The shape-only class of the protocol repair (the context read, the memo lookup) closed with
decision row 90 (2026-09-24): a context handle carries its services' typing and a memo lookup
certifies its layer's error type. -/
inductive Bearing | correlated | clear
deriving BEq, DecidableEq

/-- A row reached: store or fiber, its constructor index, and its bearing. -/
structure Reach where
  store : Bool
  index : Nat
  bearing : Bearing
deriving BEq

def fiberBearing (op : FiberOp) : Bearing := match op with
  | .raceRegister _ | .async (.store (.externalRegister _)) _ => .correlated
  | _ => .clear

def storeBearing (_ : SyncOp) : Bearing := .clear

/-- The machine's answer for each store row (decisions row 136: the census walks what the
store answers, not what a post says), so the walk takes the branch the machine takes: a fresh
handle for an allocation, a number for a read, a flag for a query, `unit` for `scopeAdd` on an
open scope, `scopeRemove`, `deferredAwaitCleanup` and the rest. -/
def storeAnswer : SyncOp → Val
  | .refMake _ => Val.cell ⟨0⟩
  | .refSet cell _ => Val.cell cell
  | .deferredMake => Val.promise ⟨0⟩
  | .scopeMake _ | .scopeFork _ _ | .memoBuild _ _ => Val.scopeHandle 1
  | .memoFork _ => Val.memoMap ⟨0⟩
  | .refGet _ | .refGetAndSet _ _ | .refSetAndGet _ _ | .refGetAndUpdate _ _
  | .refUpdateAndGet _ _ | .refGetAndUpdateSome _ _ | .refUpdateSomeAndGet _ _
  | .refModify _ _ | .refModifySome _ _ | .clockNow => Val.nat 0
  | .deferredIsDone _ | .deferredPoll _ | .deferredCompleteWith _ _ | .deferredInterruptWith _ _
  | .scopeIsClosed _ => Val.bool true
  | _ => Val.unit

/-- A realistic answer for each fiber row: a fiber handle for a fork, the root's id, an empty
child list, a successful exit for an exit-answering row, body entry for a guard. -/
def fiberAnswer : (op : FiberOp) → op.answer
  | .fork _ _ _ => Val.fiber ⟨1⟩
  | .forkIn _ _ _ _ => Val.fiber ⟨1⟩
  | .getId => Val.nat 0
  | .snapshotChildren => Val.list []
  | op => op.defaultAnswer

/-- The rows the code reaches along realistic answers, to a depth. -/
def rowsOf : Nat → RProgram → List Reach
  | 0, _ => []
  | _ + 1, .pure _ => []
  | f + 1, .vis (.inl op) k => ⟨true, op.ctorIdx, storeBearing op⟩ :: rowsOf f (k (storeAnswer op))
  | f + 1, .vis (.inr op) k => ⟨false, op.ctorIdx, fiberBearing op⟩ :: rowsOf f (k (fiberAnswer op))

/-- The loaded root code of an entry. -/
def loaded (e : Entry) : Option RProgram :=
  ((loadR e.program 400 400).fiber? Api.root).map (·.frame.current)

def footprint (e : Entry) : List Reach :=
  match loaded e with
  | some code => (rowsOf 200 code).eraseDups
  | none => []

#guard programs.all fun e => (loaded e).isSome

/-- Entries whose code reaches a correlated row. -/
def correlatedEntries : List String :=
  (entries.filter fun e => (footprint e).any (·.bearing == .correlated)).map (·.name)

-- The census report: the rows the corpus reaches, and the entries reaching a correlated row.
-- Printed, not pinned.
run_cmd do
  let env ← Lean.getEnv
  let names (n : Lean.Name) : List String := match env.find? n with
    | some (.inductInfo info) => info.ctors.map fun c => c.componentsRev.head!.toString
    | _ => []
  let fiber := names ``Effect4.Program.Sched.FiberOp
  let store := names ``Effect4.Machine.SyncOp
  let label (r : Reach) := if r.store then "store." ++ store.getD r.index "?" else "fiber." ++ fiber.getD r.index "?"
  let rows := (programs.flatMap fun e => (footprint e).map label).eraseDups
  Lean.logInfo m!"admission census: {programs.length} programs reach {rows.length} protocol rows, none with a consumed `True` post\nentries reaching a correlated row: {correlatedEntries}"

end Test.Program.AdmissionCensus
