import Test.Program.TypedCorpus
import Test.Counterexamples.Machine.Semantics.TrivialPosts

/-!
# Test.Program.AdmissionCensus — which protocol rows the generated code reaches

The admission census of decision row 89, first phase. For every typed-corpus program it loads
the reference machine (`loadR`) and walks the root's code, answering each operation with its
placeholder answer (`FiberOp.defaultAnswer`, and `unit` for a store operation), and records the
protocol rows reached. A row whose postcondition is `True` is reported: under the landed judgment
a program whose code feeds such a row's answer into its result is untypable
(`E4-SCHED-CE-013`, whose four witnesses are the checked refusals). `suspend`, whose continuation
ignores its answer, and `refuse`, refused by its precondition, are not counted against a program.

What is checked: the triviality tables agree with the protocol in the direction the report
uses (`fiberPostTrivial_sound`, `storePostTrivial_sound`: a row the census calls trivial has a
`True` post), every program is walked, and the report is printed. What is a report and not a
proof: the walk follows one answer per operation, so it under-approximates the rows a program
reaches; a program reported clear is a candidate for admission, not an admitted program. The
second phase, landed with the repair, replaces the report by an admission theorem per entry.
-/

set_option autoImplicit false
namespace Test.Program.AdmissionCensus
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Program.Typed Test.Program.TypedCorpus
abbrev W := Effect4.Program.Typed.World

/-- Rows whose postcondition in `Typed/Residual.lean` is `True`. -/
def fiberPostTrivial : FiberOp → Bool
  | .forkScoped _ _ _ | .awaitAll _ | .awaitAllFailFast _ | .async _ _ | .scoped _ | .raceAll _ _ | .raceRegister _ | .getContext | .snapshotChildren | .awaitNewChildren _ | .refuse _ | .frontier _ _ | .suspend _ | .gen _ | .loop _ _ | .construction => true
  | _ => false

def storePostTrivial : SyncOp → Bool
  | .refModify _ _ | .refModifySome _ _ | .deferredPoll _ | .memoGet _ _ | .memoBuild _ _ => true
  | _ => false

theorem fiberPostTrivial_sound : (op : FiberOp) → fiberPostTrivial op = true →
    ∀ (w : W) (cert : FiberCert op) ans, fiberPost w op cert ans
  | .fork _ _ _, h => Bool.noConfusion h
  | .forkIn _ _ _ _, h => Bool.noConfusion h
  | .forkScoped _ _ _, _ => fun _ _ _ => trivial
  | .await _ _, h => Bool.noConfusion h
  | .awaitAll _, _ => fun _ _ _ => trivial
  | .awaitAllFailFast _, _ => fun _ _ _ => trivial
  | .yieldNow _, h => Bool.noConfusion h
  | .async _ _, _ => fun _ _ _ => trivial
  | .interrupt _, h => Bool.noConfusion h
  | .interruptAs _ _, h => Bool.noConfusion h
  | .interruptScoped _, h => Bool.noConfusion h
  | .interruptAll _ _, h => Bool.noConfusion h
  | .mask _ _, h => Bool.noConfusion h
  | .closeScope _ _, h => Bool.noConfusion h
  | .scoped _, _ => fun _ _ _ => trivial
  | .scopeExit _ _ _, h => Bool.noConfusion h
  | .foreignRelease _ _, h => Bool.noConfusion h
  | .raceAll _ _, _ => fun _ _ _ => trivial
  | .raceRegister _, _ => fun _ _ _ => trivial
  | .cancelRace _, h => Bool.noConfusion h
  | .getId, h => Bool.noConfusion h
  | .getContext, _ => fun _ _ _ => trivial
  | .setContext _, h => Bool.noConfusion h
  | .snapshotChildren, _ => fun _ _ _ => trivial
  | .awaitNewChildren _, _ => fun _ _ _ => trivial
  | .runIn _ _, h => Bool.noConfusion h
  | .dropObservers _, h => Bool.noConfusion h
  | .refuse _, _ => fun _ _ _ => trivial
  | .ambientScope, h => Bool.noConfusion h
  | .closeWalk _ _ _, h => Bool.noConfusion h
  | .closeIter _ _ _, h => Bool.noConfusion h
  | .frontier _ _, _ => fun _ _ _ => trivial
  | .guard_ _, h => Bool.noConfusion h
  | .unguard _, h => Bool.noConfusion h
  | .finishFinalizer _, h => Bool.noConfusion h
  | .suspend _, _ => fun _ _ _ => trivial
  | .sync _, h => Bool.noConfusion h
  | .gen _, _ => fun _ _ _ => trivial
  | .loop _ _, _ => fun _ _ _ => trivial
  | .construction, _ => fun _ _ _ => trivial

theorem storePostTrivial_sound : (op : SyncOp) → storePostTrivial op = true →
    ∀ (w : W) (cert : StoreCert op) ans, storePost w op cert ans
  | .refMake _, h => Bool.noConfusion h
  | .refGet _, h => Bool.noConfusion h
  | .refSet _ _, h => Bool.noConfusion h
  | .refGetAndSet _ _, h => Bool.noConfusion h
  | .refSetAndGet _ _, h => Bool.noConfusion h
  | .refUpdate _ _, h => Bool.noConfusion h
  | .refGetAndUpdate _ _, h => Bool.noConfusion h
  | .refUpdateAndGet _ _, h => Bool.noConfusion h
  | .refUpdateSome _ _, h => Bool.noConfusion h
  | .refGetAndUpdateSome _ _, h => Bool.noConfusion h
  | .refUpdateSomeAndGet _ _, h => Bool.noConfusion h
  | .refModify _ _, _ => fun _ _ _ => trivial
  | .refModifySome _ _, _ => fun _ _ _ => trivial
  | .deferredMake, h => Bool.noConfusion h
  | .deferredIsDone _, h => Bool.noConfusion h
  | .deferredPoll _, _ => fun _ _ _ => trivial
  | .deferredCompleteWith _ _, h => Bool.noConfusion h
  | .deferredInterruptWith _ _, h => Bool.noConfusion h
  | .deferredAwaitCleanup _ _ _, h => Bool.noConfusion h
  | .clockNow, h => Bool.noConfusion h
  | .sleepCancel _ _, h => Bool.noConfusion h
  | .scopeMake _, h => Bool.noConfusion h
  | .scopeAdd _ _, h => Bool.noConfusion h
  | .scopeRemove _ _, h => Bool.noConfusion h
  | .scopeIsClosed _, h => Bool.noConfusion h
  | .scopeFork _ _, h => Bool.noConfusion h
  | .memoFork _, h => Bool.noConfusion h
  | .memoGet _ _, _ => fun _ _ _ => trivial
  | .memoBuild _ _, _ => fun _ _ _ => trivial
  | .memoComplete _ _ _, h => Bool.noConfusion h
  | .memoRelease _ _, h => Bool.noConfusion h

/-- How a reached row bears on admission. `blocking`: a `True` post and a continuation that
consumes the answer. `conditional`: `construction`, whose answer (the completed exits) only
matters when the continuation reads a completed fiber's exit (audit A9). `clear`: otherwise. -/
inductive Bearing | blocking | conditional | clear
deriving BEq, DecidableEq

/-- A row reached: store or fiber, its constructor index, and its bearing. -/
structure Reach where
  store : Bool
  index : Nat
  bearing : Bearing
deriving BEq

def fiberBearing (op : FiberOp) : Bearing := match op with
  | .suspend _ | .refuse _ => .clear
  | .construction => .conditional
  | op => if fiberPostTrivial op then .blocking else .clear

def storeBearing (op : SyncOp) : Bearing := if storePostTrivial op then .blocking else .clear

/-- A realistic answer for each store row, so the walk takes the branch the machine takes: a
fresh handle for an allocation, a number for a read, `unit` otherwise. -/
def storeAnswer : SyncOp → Val
  | .refMake _ => Val.cell ⟨0⟩
  | .deferredMake => Val.promise ⟨0⟩
  | .scopeMake _ | .scopeFork _ _ => Val.scopeHandle 1
  | .refGet _ | .refGetAndSet _ _ | .refSetAndGet _ _ | .refGetAndUpdate _ _
  | .refUpdateAndGet _ _ | .refGetAndUpdateSome _ _ | .refUpdateSomeAndGet _ _ | .clockNow => Val.nat 0
  | .deferredIsDone _ | .deferredCompleteWith _ _ | .deferredInterruptWith _ _
  | .deferredAwaitCleanup _ _ _ | .scopeAdd _ _ | .scopeRemove _ _ | .scopeIsClosed _ => Val.bool true
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

/-- The programs the report calls clear: no blocking row reached. -/
def blocked (e : Entry) : Bool := (footprint e).any (·.bearing == .blocking)

def clear : List String := (programs.filter fun e => !blocked e).map (·.name)

/-- Entries (no context) the report calls clear. -/
def clearEntries : List String := (entries.filter fun e => !blocked e).map (·.name)

/-- Clear entries that reach `construction`: admission depends on audit A9. -/
def conditionalEntries : List String :=
  (entries.filter fun e => !blocked e && (footprint e).any (·.bearing == .conditional)).map (·.name)

-- The census report: per blocking row, the number of corpus programs that reach it; then the
-- entries the walk finds clear. Printed, not pinned: it changes when the repair lands.
run_cmd do
  let env ← Lean.getEnv
  let names (n : Lean.Name) : List String := match env.find? n with
    | some (.inductInfo info) => info.ctors.map fun c => c.componentsRev.head!.toString
    | _ => []
  let fiber := names ``Effect4.Program.Sched.FiberOp
  let store := names ``Effect4.Machine.SyncOp
  let label (r : Reach) := if r.store then "store." ++ store.getD r.index "?" else "fiber." ++ fiber.getD r.index "?"
  let blockingOf (e : Entry) := ((footprint e).filter (·.bearing == .blocking)).map label
  let rows := (programs.flatMap blockingOf).eraseDups
  let counts := rows.map fun r => s!"{r} {(programs.filter fun e => (blockingOf e).contains r).length}"
  let perEntry := (entries.filter blocked).map fun e => s!"{e.name}: {(blockingOf e).eraseDups}"
  Lean.logInfo m!"admission census: {programs.length} programs, {clear.length} clear, {programs.length - clear.length} reach a blocking row\nblocking rows (programs reaching each): {counts}\nclear entries ({clearEntries.length} of {entries.length}): {clearEntries}\nof which conditional on construction: {conditionalEntries}\nblocked entries: {perEntry}"

end Test.Program.AdmissionCensus
