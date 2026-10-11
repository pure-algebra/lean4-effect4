import Effect4.Laws.Run.CallTree
import Effect4.Author
import Effect4.Laws.Auto.KernelRfl

/-!
Counterexample E4-HOST-CE-010.
Concept: translation-simulation R6, boundary of `recorded-call-tree-prefix`.
An outside clock advance changes a clock-dependent request without adding a host reply.
A reply-only local tape cannot represent that advance.
This control concerns the general helper; Routing itself never reads the clock.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Test.Counterexamples.HostClockPrefix
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Program.Denote Effect4.Laws.Auto Effect4.Run.CallTree

def table : RowTable := RowDef.table
  [Row.host "clock-output" .nat .unit .never "clock-prefix-control"]
def program : NativeEff := .bind (.perform .clockNow (.lit .unit)) (.perform (.external 0) (.var 0))
def initial : NativeMachine := Api.load program 16
def advanced : NativeMachine := steppedBy program 100 table initial (.advance 17)
def waiting : NativeMachine := steppedBy program 100 table advanced (.evaluate Api.root)

theorem fragment_admitted : StraightRows table program = true := by decide
theorem no_cause_handler : NoCauseHandler program = true := by decide
theorem advanced_request : requestOf waiting Api.root 0 = some (.external 0, .nat 17) := by kernel_rfl
theorem reply_tree_request : treeWaits table program [] = .waiting 0 (.nat 0) := by kernel_rfl

theorem clock_read_refused : NoClockRead program = false := by decide

end Test.Counterexamples.HostClockPrefix
