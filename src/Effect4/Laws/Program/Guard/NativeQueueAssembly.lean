import Effect4.Laws.Program.Guard.NativeAssembly
import Effect4.Laws.Program.Guard.NativeQueueTail
import Effect4.Laws.Program.Guard.ReturnCommands

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Effect4.Program.Guard.NativeQueueAssembly
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard
open Effect4.Program.Guard.RegistrationQueue Effect4.Program.Guard.ReturnFields

theorem guardQueue_settle_native (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (rest : List NCmd)
    (state : GuardState m) (lookup : m.fiber? f.id = some f)
    (running : f.running = true) (park : f.parked = .notParked)
    (queue : GuardQueue p table m rest) (registration : RegistrationQueue rest)
    (fresh : f.id ∉ rest.filterMap (commandOwner m)) :
    GuardQueue p table (settle f.id rest (evaluateNative p m f yielding table)).1
      (settle f.id rest (evaluateNative p m f yielding table)).2 := by
  have hid := Effect4.Program.Guard.Interruption.evaluateNative_id p table m f yielding
  apply Effect4.Program.Guard.NativeQueueTail.guardQueue_settle p table m f.id rest
    (evaluateNative p m f yielding table)
  · rw [hid]; exact ⟨f, lookup, running, park⟩
  · exact queue
  · exact registration
  · rw [hid]; exact fresh
  · exact Effect4.Program.Guard.NativeState.evaluateNative_state p table state f yielding ⟨f, lookup⟩
  · exact Effect4.Program.Guard.NativeStateLinks.evaluateNative_links p table m f yielding
  · exact evaluateNative_freshPark p table m f yielding park
  · exact Effect4.Program.Guard.ReturnCommands.evaluateNative_guardQueue p table m f yielding state lookup running park
  · rw [hid]
    exact Effect4.Program.Guard.ReturnCommands.evaluateNative_commandOwners p table m f yielding state lookup running park

theorem guardQueue_settle_iteration (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (rest : List NCmd)
    (state : GuardState m) (lookup : m.fiber? f.id = some f)
    (running : f.running = true) (park : f.parked = .notParked)
    (queue : GuardQueue p table m rest) (registration : RegistrationQueue rest)
    (fresh : f.id ∉ rest.filterMap (commandOwner m)) :
    letI := evaluatorFor p table
    GuardQueue p table (settle f.id rest (iteration (interpOf p table) m f yielding)).1
      (settle f.id rest (iteration (interpOf p table) m f yielding)).2 := by
  letI := evaluatorFor p table
  have hid := Effect4.Program.Guard.Interruption.iteration_id p table m f yielding
  apply Effect4.Program.Guard.NativeQueueTail.guardQueue_settle p table m f.id rest
    (iteration (interpOf p table) m f yielding)
  · rw [hid]; exact ⟨f, lookup, running, park⟩
  · exact queue
  · exact registration
  · rw [hid]; exact fresh
  · exact Effect4.Program.Guard.NativeState.iteration_state p table state f yielding ⟨f, lookup⟩
  · exact Effect4.Program.Guard.NativeStateLinks.iteration_links p table m f yielding
  · exact iteration_freshPark p table m f yielding park
  · exact Effect4.Program.Guard.ReturnCommands.iteration_guardQueue p table m f yielding state lookup running park
  · rw [hid]
    exact Effect4.Program.Guard.ReturnCommands.iteration_commandOwners p table m f yielding state lookup running park

theorem guardQueue_driveStep_loop (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (target : FiberId) (yielding : Bool) (rest : List NCmd)
    (state : GuardState m) (queue : GuardQueue p table m (.loop target yielding :: rest))
    (registration : RegistrationQueue (.loop target yielding :: rest)) :
    letI := evaluatorFor p table
    GuardQueue p table (driveStep (interpOf p table) m (.loop target yielding) rest).1
      (driveStep (interpOf p table) m (.loop target yielding) rest).2 := by
  letI := evaluatorFor p table
  obtain ⟨f, hf, running, park⟩ := queue.authority (.loop target yielding) (List.mem_cons_self ..)
  have hid := fiber_id_of_lookup hf
  have lookup : m.fiber? f.id = some f := by simpa only [hid] using hf
  have owners := queue.owners
  simp only [List.filterMap_cons, commandOwner] at owners
  have fresh : f.id ∉ rest.filterMap (commandOwner m) := hid ▸ (List.nodup_cons.mp owners).1
  have after := guardQueue_settle_iteration p table m f yielding rest state lookup running park
    (guardQueue_tail p table queue) (registrationQueue_tail registration) fresh
  simpa only [driveStep, hf, hid] using after

theorem guardQueue_driveStep_deliver (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (target : FiberId) (yielding : Bool) (rest : List NCmd)
    (state : GuardState m) (queue : GuardQueue p table m (.deliver target yielding :: rest))
    (registration : RegistrationQueue (.deliver target yielding :: rest)) :
    letI := evaluatorFor p table
    GuardQueue p table (driveStep (interpOf p table) m (.deliver target yielding) rest).1
      (driveStep (interpOf p table) m (.deliver target yielding) rest).2 := by
  letI := evaluatorFor p table
  obtain ⟨f, hf, running, park⟩ := queue.authority (.deliver target yielding) (List.mem_cons_self ..)
  have hid := fiber_id_of_lookup hf
  have lookup : m.fiber? f.id = some f := by simpa only [hid] using hf
  have owners := queue.owners
  simp only [List.filterMap_cons, commandOwner] at owners
  have fresh : f.id ∉ rest.filterMap (commandOwner m) := hid ▸ (List.nodup_cons.mp owners).1
  have after := guardQueue_settle_native p table m f yielding rest state lookup running park
    (guardQueue_tail p table queue) (registrationQueue_tail registration) fresh
  simpa only [driveStep, hf, hid] using after

end Effect4.Program.Guard.NativeQueueAssembly
