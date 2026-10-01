import Effect4.Laws.Auto.Census
import Effect4.Laws.Program.Guard.ForkLedger
#auto_census Effect4.Laws.Machine.ForkLedgerInvariant using aesop
#auto_census Effect4.Laws.Machine.ForkLedgerInvariant using aesop (rule_sets := [Effect4.StepInv])
#auto_census Effect4.Laws.Program.Guard.ForkLedger using aesop
#auto_census Effect4.Laws.Program.Guard.ForkLedger using aesop (rule_sets := [Effect4.StepInv])
