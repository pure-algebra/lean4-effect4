import Effect4.Laws.Machine.Clauses
import Effect4.Laws.Machine.Approximation
import Effect4.Laws.Machine.StoresLaws
import Effect4.Laws.Machine.Behaviour
import Effect4.Laws.Machine.Book
import Effect4.Laws.Machine.ContextValue
import Effect4.Laws.Machine.Handles
import Effect4.Laws.Machine.LiveStack
import Effect4.Laws.Machine.Scheduling
import Effect4.Laws.Machine.ScopeMachine
import Effect4.Laws.Machine.ScopeRestoration
import Effect4.Laws.Machine.StoresValue
import Effect4.Laws.Machine.Witnesses
import Effect4.Laws.Program.Denote
import Effect4.Laws.Program.Agreement
import Effect4.Laws.Program.Agreement.Machine
import Effect4.Laws.Program.Sched
import Effect4.Laws.Program.DenoteR
import Effect4.Laws.Program.InterpR
import Effect4.Laws.Program.EvaluateR
import Effect4.Laws.Program.Typed
import Effect4.Laws.Program.Handles
import Effect4.Laws.Program.Means
import Effect4.Laws.Program.Intro
import Effect4.Laws.Program.Progress
import Effect4.Laws.Program.Simulation.Hooks
import Effect4.Laws.Program.Simulation.Walk
import Effect4.Laws.Program.Simulation.Fibers
import Effect4.Laws.Program.Simulation.Deliver
import Effect4.Laws.Program.Simulation.Actions
import Effect4.Laws.Program.Simulation.Evaluate
import Effect4.Laws.Program.Simulation.Pending
import Effect4.Laws.Program.Simulation.Drive
import Effect4.Laws.Program.RuntimeR

/-!
# Effect4 proof graph

The machine and program judgments, simulation, composition and execution laws.
These modules continue their definition modules' namespaces; the module paths
separate build targets. `import Effect4` never reaches this root.
-/
