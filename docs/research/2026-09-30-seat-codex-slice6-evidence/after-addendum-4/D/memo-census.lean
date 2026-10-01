import Effect4.Laws.Auto.Census
import Effect4.Laws.Program.Guard.MemoIds
import Effect4.Laws.Program.Guard.ForkLedger
#auto_census Effect4.Laws.Program.Guard.MemoIds using aesop
#auto_census Effect4.Laws.Program.Guard.MemoIds using aesop (rule_sets := [Effect4.StepInv])
