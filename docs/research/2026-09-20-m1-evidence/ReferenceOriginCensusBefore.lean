import Effect4.Laws.Program.Sched
import Effect4.Laws.Program.DenoteR
import Effect4.Laws.Program.EvaluateR
import Effect4.Laws.Program.Means
import Effect4.Laws.Program.Intro.Weight
import Effect4.Laws.Program.Intro.Fibers
import Effect4.Laws.Program.Intro.Merge
import Effect4.Laws.Program.Simulation.Fibers
import Effect4.Laws.Auto.Census

#auto_census Effect4.Laws.Program.Sched using aesop
#auto_census Effect4.Laws.Program.DenoteR using aesop
#auto_census Effect4.Laws.Program.EvaluateR using aesop
#auto_census Effect4.Laws.Program.Means using aesop
#auto_census Effect4.Laws.Program.Intro.Weight using aesop
#auto_census Effect4.Laws.Program.Intro.Fibers using aesop
#auto_census Effect4.Laws.Program.Intro.Merge using aesop
#auto_census Effect4.Laws.Program.Simulation.Fibers using aesop
