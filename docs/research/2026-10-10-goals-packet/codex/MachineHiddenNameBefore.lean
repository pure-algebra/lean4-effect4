import Effect4.Laws.Program.ReleaseCustody.Control
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.ReleaseCustody Effect4.Program.ReleaseCustody.Control
#check ProgName.rec
example (root : NativeEff) (q : List Nat) (c : Capture) (exit : ExitV) :
    currentCredits q (.suspend (.store (.body (.finalizerOf (.foreign c) exit)))) = 0 ∧
    currentCredits q (suspendBodyAt root (.store (.body (.finalizerOf (.foreign c) exit)))) =
      credit q (.foreign c) := ⟨rfl, rfl⟩
