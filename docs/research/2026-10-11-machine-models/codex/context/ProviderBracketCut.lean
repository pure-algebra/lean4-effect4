import Effect4.Program.Provision
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
namespace Test.ProviderBracketCut
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

#guard ((cut 6).1.fiber? ⟨0⟩).map (fun fiber => fiber.context.services.getV key) = some (some (.nat 1))
#guard (admitProgram source).toOption.isSome
example : writes (interruptedCut 6).trace key = [some (.nat 1)] := by kernel_rfl
example : writes (interruptedCut 7).trace key = [some (.nat 1)] := by kernel_rfl
example : writes (interruptedCut 8).trace key = [some (.nat 1), none] := by kernel_rfl

-- This raw source yields at the same interval, but admission refuses its reserved service.
def budgetSource : NativeEff := .provideService Env.maxOpsKey (.lit (.nat 5)) (.yieldNow 0)
def started :=
  letI := evaluatorFor budgetSource
  (runFork (interpOf budgetSource) 128 (RunMachine.empty Stores.empty)
    (compile budgetSource 1024) emptyCtx).1

def cancelled :=
  letI := evaluatorFor budgetSource
  stepDecision (interpOf budgetSource) 128 started (.interruptFrom none .empty ⟨0⟩)

example : admitProgram budgetSource = .error .illTyped := by kernel_rfl
#guard !(admitProgram budgetSource).toOption.isSome
#guard !(typeOfProgram (nativeSignature []) budgetSource).isSome
#guard (started.fiber? ⟨0⟩).map (fun fiber => (fiber.running, fiber.exit.isSome)) = some (false, false)
#guard (cancelled.fiber? ⟨0⟩).map (fun fiber => fiber.exit.isSome) = some true
example : writes cancelled.trace Env.maxOpsKey = [some (.nat 5)] := by kernel_rfl
end Test.ProviderBracketCut
