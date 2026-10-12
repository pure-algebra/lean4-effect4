import Effect4.Program.Compile
import Effect4.Program.Admission
import Effect4.Laws.Auto.KernelRfl

set_option autoImplicit false
namespace Test.ProviderBaselineR2Control
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

#guard (admitProgram source).toOption.isSome
example : writes (interruptedCut 6).trace key = [some (.nat 1)] := by kernel_rfl
example : writes (interruptedCut 7).trace key = [some (.nat 1)] := by kernel_rfl
example : writes (interruptedCut 8).trace key = [some (.nat 1), none] := by kernel_rfl
end Test.ProviderBaselineR2Control
