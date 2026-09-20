/-! Origin/site radius beyond the original M1 census. Book, Clauses and Api.Supervision
already have frozen baseline output in /tmp/m1-origin-census-before.log.
This file is a prepared census input, not evidence of a completed run. -/
import Effect4.Laws.Api.Supervision
import Effect4.Laws.Machine.Book
import Effect4.Laws.Machine.Clauses
import Effect4.Laws.Machine.Approximation
import Effect4.Laws.Machine.Scheduling
import Effect4.Laws.Program.RuntimeR
import Effect4.Laws.Program.EvaluateR
import Effect4.Laws.Program.Sched
import Effect4.Laws.Program.DenoteR
import Effect4.Laws.Program.Simulation.Fibers
import Effect4.Laws.Program.Simulation.Pending
import Effect4.Laws.Program.Handles.Evaluation
import Effect4.Laws.Program.Handles.Compile
import Effect4.Laws.Program.Handles.Layer
import Effect4.Laws.Program.Guard.NativeStateMotion
import Effect4.Laws.Program.Guard.NativeStateExternal
import Effect4.Laws.Program.Guard.ReturnCommands
import Effect4.Laws.Program.Guard.Interruption
import Effect4.Laws.Program.Guard.DeferredCause
import Effect4.Laws.Program.Guard.ReturnFields
import Effect4.Laws.Program.Guard.ReturnTasks
import Effect4.Laws.Program.Guard.NativeStateLinks
import Effect4.Laws.Program.Guard.RegistrationNested
import Effect4.Laws.Auto.Census

#auto_census Effect4.Laws.Api.Supervision using aesop
#auto_census Effect4.Laws.Machine.Book using aesop
#auto_census Effect4.Laws.Machine.Clauses using aesop
#auto_census Effect4.Laws.Machine.Approximation using aesop
#auto_census Effect4.Laws.Machine.Scheduling using aesop
#auto_census Effect4.Laws.Program.RuntimeR using aesop
#auto_census Effect4.Laws.Program.EvaluateR using aesop
#auto_census Effect4.Laws.Program.Sched using aesop
#auto_census Effect4.Laws.Program.DenoteR using aesop
#auto_census Effect4.Laws.Program.Simulation.Fibers using aesop
#auto_census Effect4.Laws.Program.Simulation.Pending using aesop
#auto_census Effect4.Laws.Program.Handles.Evaluation using aesop
#auto_census Effect4.Laws.Program.Handles.Compile using aesop
#auto_census Effect4.Laws.Program.Handles.Layer using aesop
#auto_census Effect4.Laws.Program.Guard.NativeStateMotion using aesop
#auto_census Effect4.Laws.Program.Guard.NativeStateExternal using aesop
#auto_census Effect4.Laws.Program.Guard.ReturnCommands using aesop
#auto_census Effect4.Laws.Program.Guard.Interruption using aesop
#auto_census Effect4.Laws.Program.Guard.DeferredCause using aesop
#auto_census Effect4.Laws.Program.Guard.ReturnFields using aesop
#auto_census Effect4.Laws.Program.Guard.ReturnTasks using aesop
#auto_census Effect4.Laws.Program.Guard.NativeStateLinks using aesop
#auto_census Effect4.Laws.Program.Guard.RegistrationNested using aesop
