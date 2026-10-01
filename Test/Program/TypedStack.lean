import Test.Program.TypedControl
import Effect4.Laws.Program.Typed.Assembly
import Effect4.Laws.Machine.Keeps

/-!
# Test.Program.TypedStack — slice 5's controls

The stack walk on concrete typed stacks (`popR_typed_interpR`): an error-removing catch that runs,
a preempted catch whose walk completes with the sanitized cause at `never`, a stack whose frames
do not compose (refused), a stale resume that changes nothing, and the assembled typed state
elaborating over a real reachable machine.
-/

set_option autoImplicit false
namespace Test.Program.TypedStack
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Program.Typed Effect4.Program.Typed.Contracts
open Test.Program.TypedControl (natErr natErr_exitOk exitOk_nat)
abbrev W := Effect4.Program.Typed.World

def sleeping : NativeEff := .perform .sleep (.lit (.nat 1))
def natNat : EffTy := { EffTy.pure .nat with error := .nat }

/-- An error-removing catch: a failure runs the handler, which answers 0. -/
def catchFrame : ScopeFrame := .resume .onFailure fun _ => .pure (.success (.nat 0))

theorem catch_accepted (root : ProgramSource) (w : W) :
    StackAccepts (TypedProg root) ExitOk (frameProtocols root) w natNat (EffTy.pure .nat)
      [catchFrame] := by
  refine .cons (.resume _ _ (fun w' _ _ _ _ => TypedProg.pure (exitOk_nat w' _ 0 rfl)) ?_) (.nil _)
  intro _ _ ex hex miss
  cases ex with
  | success v => exact hex
  | failure c => exact Bool.noConfusion miss

def quiet : RSaved :=
  { current := .pure (.success .unit), stack := [], interruptible := true, interruptedCause := none,
    deferredInterrupt := false }

theorem quiet_provenance : InterruptProvenance quiet := ⟨(fun _ h => nomatch h), fun h => nomatch h⟩

/-- The walk runs the handler: typed code installed over the empty remainder. -/
theorem catch_walk (w : W) :
    WalkTyped (sleeping : ProgramSource) (frameProtocols sleeping) w (EffTy.pure .nat)
      (popR (interpR sleeping) (.failure (natErr 7)) [catchFrame] quiet) :=
  popR_typed_interpR sleeping w _ _ _ _ _ (catch_accepted _ w) (natErr_exitOk w _ 7 rfl) quiet_provenance

/-- The same catch with a recorded interrupt: preempted, the walk passes the sanitized cause. -/
def preempted : RSaved := { quiet with interruptedCause := some (Cause.interrupt none) }

theorem preempted_provenance : InterruptProvenance preempted := by
  refine ⟨fun c hc r hr => ?_, fun _ => rfl⟩
  cases hc
  simp only [Cause.interrupt, List.mem_singleton] at hr
  subst hr
  rfl

#guard (popR (interpR sleeping) (.failure (natErr 7)) [catchFrame] preempted).2.isSome

/-- The completed exit is the sanitized cause, typed at `never` by the walk theorem. -/
theorem preempted_walk (w : W) :
    WalkTyped (sleeping : ProgramSource) (frameProtocols sleeping) w (EffTy.pure .nat)
      (popR (interpR sleeping) (.failure (natErr 7)) [catchFrame] preempted) :=
  popR_typed_interpR sleeping w _ _ _ _ _ (catch_accepted _ w) (natErr_exitOk w _ 7 rfl)
    preempted_provenance

/-- A pass-through frame from `nat`/`nat` to `nat`/`never` is refused: its miss would pass a
Nat failure out. -/
def passFrame : ScopeFrame := .resume .onSuccess fun ex => .pure ex

theorem wrong_middle (root : ProgramSource) (w : W) :
    ¬ StackAccepts (TypedProg root) ExitOk (frameProtocols root) w natNat (EffTy.pure .nat)
      [passFrame] := by
  intro h
  cases h with
  | cons head tail =>
    cases tail
    cases head with
    | resume kind next run skip =>
      have failed := (fitsExit_failure_iff w (EffTy.pure .nat) (natErr 7)).mp
        (skip w (leHost_refl w) (.failure (natErr 7)) (natErr_exitOk w _ 7 rfl) rfl).1
      obtain ⟨v, _, hv⟩ := failed (.fail (.tag 7) .empty) (List.mem_singleton_self _)
      exact hv

/-! ### A changing middle type

Moved from `Contracts.Example` (`src/`, plan item T3): a finite relation used solely to witness
the interface's changing middle type. Nat → Bool → Unit uses two answer frames, with a middle
distinct from both ends. A kernel-checked interface example, not an evaluator theorem. -/

def middlePrograms (_w : W) (ty : EffTy) (code : RProgram) : Prop :=
  (ty = EffTy.pure .bool ∧ code = .pure (.success (.bool true))) ∨
  (ty = EffTy.pure .unit ∧ code = .pure (.success .unit))

theorem changing_middle (Exits : W → EffTy → ExitV → Prop) (w : W) (hooks : FrameProtocols) :
    StackAccepts middlePrograms Exits hooks w (EffTy.pure .nat) (EffTy.pure .unit)
      [.answer (fun _ => .pure (.success (.bool true))),
       .answer (fun _ => .pure (.success .unit))] :=
  .cons (.answer _ (fun _ _ _ _ => Or.inl ⟨rfl, rfl⟩))
    (.cons (.answer _ (fun _ _ _ _ => Or.inr ⟨rfl, rfl⟩)) (.nil _))

theorem middle_differs : EffTy.pure .bool ≠ EffTy.pure .nat ∧
    EffTy.pure .bool ≠ EffTy.pure .unit := by
  constructor <;> intro h <;> cases h

/-- A resume at a stale token leaves a real parked machine and its queue as they were. -/
def parked : RState := (replayR sleeping 20 [.evaluate Api.root]).machine

theorem stale_is_inert (code : RProgram) (rest : List RCmd) :
    (letI := termEvaluatorFor sleeping
     driveStep (interpR sleeping) parked (.resume Api.root 1 code) rest) = (parked, rest) := rfl

/-- The assembled typed state elaborates over a reachable machine and an admitted decision. -/
def stateClaim (w : W) : Prop :=
  TypedState (sleeping : ProgramSource) (EffTy.pure .unit) w parked ∧
  RReachable (sleeping : ProgramSource) 20 parked ∧ AnswerOk w parked Api.evaluate

theorem parked_reachable : RReachable (sleeping : ProgramSource) 20 parked := by
  refine ⟨[.evaluate Api.root], ?_, rfl⟩
  intro d hd
  simp only [List.mem_singleton] at hd
  subst d
  trivial

#print axioms popR_typed
#print axioms popR_typed_interpR
#print axioms hookLaws_interpR
#print axioms saveAnswerR_typed
#print axioms deliver_active
#print axioms deliver_stale
#print axioms capture_lookup
#print axioms catch_walk
#print axioms preempted_walk
#print axioms wrong_middle
#print axioms stale_is_inert
#print axioms changing_middle
#print axioms middle_differs
#print axioms Effect4.Machine.RunMachine.fiber?_update_other
#print axioms Effect4.Machine.RunMachine.fiber?_update_self
end Test.Program.TypedStack
