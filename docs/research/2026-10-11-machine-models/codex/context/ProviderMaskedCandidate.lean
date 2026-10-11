import Effect4.Program.Compile
import Effect4.Program.Admission
import Effect4.Laws.Auto.KernelRfl

set_option autoImplicit false
namespace Test.ProviderMaskedCandidate
open Effect4 Effect4.Machine Effect4.Program

def key : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩
def source : NativeEff := .provideService key (.lit (.nat 1)) (.yieldNow 0)
def seed :=
  letI := evaluatorFor source
  (runFork (interpOf source) 0 (RunMachine.empty Stores.empty) (compile source 1024) emptyCtx).1

def cut (fuel : Nat) :=
  letI := evaluatorFor source
  driveState (interpOf source) fuel seed [.evaluate ⟨0⟩, .drainDue]

def interruptedCut (fuel : Nat) :=
  letI := evaluatorFor source
  let stopped := stepDecision (interpOf source) 96 (cut fuel).1 (.interruptFrom none .empty ⟨0⟩)
  (driveState (interpOf source) 96 stopped (cut fuel).2).1

def writes (events : List (RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx))
    (chosen : ServiceKey) : List (Option Val) :=
  events.filterMap fun event => match event with
    | .contextSet _ context => some (context.services.getV chosen)
    | _ => none

example (update : Env.ContextUpdate) (body : Region) :
    updateContextAt update body =
      .onSuccess (.withFiber .captureMask) (.provideMask update body) := by rfl

example (root : NativeEff) (update : Env.ContextUpdate) (body : Region) (flag : Bool) :
    Program.contAOf root (.provideMask update body) (Val.savedMask flag) =
      .withFiber (.provideMasked update body flag) := by
  simp only [Program.contAOf, Val.savedMask?_savedMask]

example (root : NativeEff) (update : Env.ContextUpdate) (body : Region)
    (flag : Bool) (previous : Ctx) :
    updateThenK root update body flag (Val.context previous) =
      if updateKeepsIdentity update previous.services then .withFiber (.restoreRegion body flag)
      else .onSuccess (.withFiber (.setCtx (Ctx.withServices (update.apply previous.services))))
        (.bodyThen body previous flag) := by
  simp only [updateThenK, Val.context?_context]

example (root : NativeEff) (body : Region) (flag : Bool) (previous : Ctx) (value : Val) :
    Program.contAOf root (.bodyThen body previous flag) value =
      .onExit (.withFiber (.restoreRegion body flag)) (.restoreCtx previous) false := by rfl

example (root : NativeEff) (update : Env.ContextUpdate) (body : Region) (flag : Bool) :
    (interpOf root).withFiberOf (.provideMasked update body flag) =
      some (.setInterruptible
        (.onSuccess (.withFiber .getCtx) (.updateThen update body flag)) false) := by rfl

example (root : NativeEff) (body : Region) (flag : Bool) :
    (interpOf root).withFiberOf (.restoreRegion body flag) =
      some (.setInterruptible (regionCode root body) flag) := by rfl

-- The surrounding source mask is admitted. The returned saved flag observes the body's mask.
def observedSource (flag : Bool) : NativeEff :=
  let body := .bind (.provideService key (.lit (.nat 1)) (.sync (.lit .unit))) (.withFiber .getInterruptible)
  if flag then .interruptible body else .uninterruptible body
def observed (flag : Bool) :=
  let root := observedSource flag
  letI := evaluatorFor root
  let initial := (runFork (interpOf root) 0 (RunMachine.empty Stores.empty) (compile root 1024) emptyCtx).1
  (driveState (interpOf root) 128 initial [.evaluate ⟨0⟩, .drainDue]).1
#guard (admitProgram source).toOption.isSome
#guard (admitProgram (observedSource true)).toOption.isSome
#guard (admitProgram (observedSource false)).toOption.isSome
example : writes (interruptedCut 2).trace key = [] := by kernel_rfl
-- The capture getter's own restoring slot is still a distinct pre-entry cut.
example : writes (interruptedCut 3).trace key = [] := by kernel_rfl
example : writes (interruptedCut 4).trace key = [] := by kernel_rfl
-- Interruption inside masked entry waits for installation and finalizer placement.
example : writes (interruptedCut 8).trace key = [some (.nat 1), none] := by kernel_rfl
example : writes (cut 10).1.trace key = [some (.nat 1)] := by kernel_rfl
example : writes (interruptedCut 10).trace key = [some (.nat 1), none] := by kernel_rfl
#guard ((cut 10).1.fiber? ⟨0⟩).map (fun fiber => fiber.context.services.getV key) = some (some (.nat 1))
-- Completed exits record the actual saved flag returned by the body continuation.
example : (observed true).completedExits = [(⟨0⟩, .success (Val.savedMask true))] := by kernel_rfl
example : (observed false).completedExits = [(⟨0⟩, .success (Val.savedMask false))] := by kernel_rfl
example : writes (observed true).trace key = [some (.nat 1), none] := by kernel_rfl
example : writes (observed false).trace key = [some (.nat 1), none] := by kernel_rfl
end Test.ProviderMaskedCandidate
