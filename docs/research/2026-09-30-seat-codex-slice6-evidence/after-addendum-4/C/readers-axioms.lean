import Effect4.Laws.Api.Supervision
import Effect4.Laws.Program.RuntimeR
import Effect4.Laws.Program.Typed.ForkSource
import Effect4.Laws.Program.Guard.Core

#print axioms Effect4.Machine.BookMeans.forks
#print axioms Effect4.Machine.BookMeans.originOf
#print axioms Effect4.Machine.bookMeans_controls_forks
#print axioms Effect4.Program.Sched.BMeans.forks
#print axioms Effect4.Program.Sched.BMeans.originOf
#print axioms Effect4.Program.Sched.BMeans.appendFork
#print axioms Effect4.Program.Sched.machineOk_forks
#print axioms Effect4.Program.Guard.guardState_forks
#print axioms Effect4.Program.Guard.spawn_machine
#print axioms Effect4.Program.Guard.guardState_spawn
#print axioms Effect4.Program.Typed.M2ForkSourceWanted.fork_source_extension
#print axioms Effect4.Program.Typed.M2ForkSourceWanted.fork_source_originOf
#print axioms Effect4.Api.load_origins
#print axioms Effect4.Api.status_persists
#print axioms Effect4.Api.spawn_status_fresh
#print axioms Effect4.Api.spawn_status_other
#print axioms Effect4.Api.spawn_fibers
#print axioms Effect4.Api.spawn_origins
#print axioms Effect4.Api.launchEntrant_origins
#print axioms Effect4.Machine.spawnChild_fields
#print axioms Effect4.Program.Sched.spawn_rel
#print axioms Effect4.Program.Sched.load_rel
