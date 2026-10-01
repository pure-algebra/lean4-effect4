import Effect4.Laws.Auto.Census
import Effect4.Laws.Api.TraceOrigin
#auto_census Effect4.Laws.Api.TraceOrigin using aesop
#auto_census Effect4.Laws.Api.TraceOrigin using aesop (rule_sets := [Effect4.StepInv])
