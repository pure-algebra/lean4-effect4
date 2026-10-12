import Effect4.Program.Compile
import Effect4.Program.Admission
import Effect4.Laws.Auto.KernelRfl

/-!
Concept: scope-lifetime-finalization, R11; control for the provider region instance.
Reach: finite actual native command prefixes and an ordinary budget-induced yield.
The trace records context writes before finished-fiber clearing resets its context.
This control does not establish a public Run.HistoryOf derivation or runtime agreement.
Consumer: the approved context provider's shared region bracket, then closed M5.
-/
set_option autoImplicit false
namespace Test.ProviderBracketCandidate
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
  let stopped := stepDecision (interpOf source) 32 (cut fuel).1 (.interruptFrom none .empty ⟨0⟩)
  (driveState (interpOf source) 32 stopped (cut fuel).2).1

-- Finite trace reader; no additional source or executor representation.
def writes (events : List (RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx))
    (chosen : ServiceKey) : List (Option Val) :=
  events.filterMap fun event => match event with
    | .contextSet _ context => some (context.services.getV chosen)
    | _ => none

-- Check only after applying ProviderBracketCandidate.patch to the temporary compiler copy.
-- The production compiler and reference program remain unchanged.
example (root : NativeEff) (update : Env.ContextUpdate) (body : Region) (previous : Ctx) :
    updateThenK root update body (Val.context previous) =
      if updateKeepsIdentity update previous.services then regionCode root body
      else .onExit
        (.onSuccess (.withFiber (.setCtx (Ctx.withServices (update.apply previous.services))))
          (.bodyThen body previous)) (.restoreCtx previous) false := by
  simp only [updateThenK, Val.context?_context]

example (root : NativeEff) (body : Region) (previous : Ctx) (value : Val) :
    contAOf root (.bodyThen body previous) value = regionCode root body := by rfl

#guard (admitProgram source).toOption.isSome
-- Interruption before any write leaves the physical previous context untouched.
example : writes (interruptedCut 4).trace key = [] := by kernel_rfl
-- An installed restoring frame may write the previous context even before the setter runs.
example : writes (interruptedCut 5).trace key = [none] := by kernel_rfl
example : writes (interruptedCut 6).trace key = [none] := by kernel_rfl
-- The former post-write gap and the fuel-eight cut now both restore the previous context.
example : writes (interruptedCut 7).trace key = [some (.nat 1), none] := by kernel_rfl
example : writes (interruptedCut 8).trace key = [some (.nat 1), none] := by kernel_rfl
#guard ((cut 7).1.fiber? ⟨0⟩).map (fun fiber => fiber.context.services.getV key) = some (some (.nat 1))
end Test.ProviderBracketCandidate
