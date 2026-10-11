import Effect4.Laws.Program.ReleaseCustody.CommandDebit

/-!
Reader: execute the first native command of an actually loaded source.
This applies the local command debit at the compiler's checked initial funding.
It asserts no whole-history release bound or progress.
-/
set_option autoImplicit false
namespace Test.Program.CommandDebit
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.ReleaseCustody.Control

example (root : NativeEff) (fuel : Nat) (table : RowTable) (q : List Nat) :
    letI := evaluatorFor root table
    let out := driveStep (interpOf root table) (Api.load root fuel) (.evaluate Api.root) []
    Funded q out.1 out.2 := by
  apply ReleaseCustody.CommandDebit.evaluate root table q (Api.load root fuel) Api.root []
    (Guard.guardState_load root fuel).fiberIds
  simpa only [Funded, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, commandCredits,
    Nat.zero_add] using load_funded q root fuel

end Test.Program.CommandDebit
