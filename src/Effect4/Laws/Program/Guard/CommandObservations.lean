import Effect4.Laws.Program.Guard.Command
import Effect4.Laws.Program.Guard.ControlRemainder

set_option autoImplicit false
namespace Effect4.Program.Guard
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard.RegistrationQueue
open Effect4.Program.Guard.NativeAssembly Effect4.Program.Guard.NativeQueueAssembly Effect4.Program.Guard.Finish Effect4.Program.Guard.FinishQueue
open Effect4.Program.Guard.ControlRemainder

theorem interruptedAt_driveStep_interruptTarget (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (target : FiberId) (who : Option FiberId) (extra : ReasonAnnotations Ann)
    (rest : List NCmd) (fiber : FiberId) (before : InterruptedAt m fiber) :
    letI := evaluatorFor p table
    InterruptedAt (driveStep (interpOf p table) m (.interruptTarget target who extra) rest).1 fiber := by
  letI := evaluatorFor p table
  cases lookup : m.fiber? target with
  | none => simpa only [driveStep, lookup] using before
  | some f =>
    simp only [driveStep, lookup]
    exact interruptedAt_update_interruptRecord p table lookup who extra fiber before

theorem registrationQueue_driveStep (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (command : NCmd) (rest : List NCmd)
    (registration : RegistrationQueue (command :: rest)) :
    letI := evaluatorFor p table
    RegistrationQueue (driveStep (interpOf p table) m command rest).2 := by
  letI := evaluatorFor p table
  cases command with
  | evaluate target => exact registrationQueue_driveStep_evaluate p table m target rest registration
  | loop target yielding => exact registrationQueue_driveStep_loop p table m target yielding rest registration.2
  | deliver target yielding => exact registrationQueue_driveStep_deliver p table m target yielding rest registration.2
  | finish target exit => exact registrationQueue_driveStep_finish p table m target exit rest registration.2
  | resume target offered answer => exact registrationQueue_driveStep_resume p table m target offered answer rest registration
  | launch rid => exact registrationQueue_driveStep_launch p table m rid rest registration
  | enrollRace rid child => exact registrationQueue_driveStep_enrollRace p table m rid child rest registration
  | registrationDone rid yielding => exact registrationQueue_driveStep_registrationDone p table m rid yielding rest registration
  | interruptTarget target who extra => exact registrationQueue_driveStep_interruptTarget p table m target who extra rest registration
  | afterInterrupt host yielding kind => exact registrationQueue_driveStep_afterInterrupt p table m host yielding kind rest registration
  | raceCancel rid host yielding remaining visited => exact registrationQueue_driveStep_raceCancel p table m rid host yielding remaining visited rest registration
  | trackChild parent child => exact registrationQueue_driveStep_trackChild p table m parent child rest registration
  | observe id exit observer => exact registrationQueue_driveStep_observe p table m id exit observer rest registration
  | exitDone target => exact registrationQueue_driveStep_exitDone p table m target rest registration
  | closeParAwait host yielding fibers => exact registrationQueue_driveStep_closeParAwait p table m host yielding fibers rest registration
  | link mode scope target who extra => exact registrationQueue_driveStep_link p table m mode scope target who extra rest registration
  | drainDue  => exact registrationQueue_driveStep_drainDue p table m  rest registration
  | wake key phase => exact registrationQueue_driveStep_wake p table m key phase rest registration

theorem interruptedAt_driveStep (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (command : NCmd) (rest : List NCmd)
    (state : GuardState m) (fiber : FiberId) (before : InterruptedAt m fiber) :
    letI := evaluatorFor p table
    InterruptedAt (driveStep (interpOf p table) m command rest).1 fiber := by
  letI := evaluatorFor p table
  cases command with
  | evaluate target => exact interruptedAt_driveStep_evaluate p table m target rest fiber before
  | loop target yielding => exact interruptedAt_driveStep_loop p table m target yielding rest state fiber before
  | deliver target yielding => exact interruptedAt_driveStep_deliver p table m target yielding rest state fiber before
  | finish target exit => exact interruptedAt_driveStep_finish p table m target exit rest state fiber before
  | resume target offered answer => exact interruptedAt_driveStep_resume p table m target offered answer rest fiber before
  | launch rid => exact interruptedAt_driveStep_launch p table m rid rest fiber before
  | enrollRace rid child => exact interruptedAt_driveStep_enrollRace p table m rid child rest fiber before
  | registrationDone rid yielding => exact interruptedAt_driveStep_registrationDone p table m rid yielding rest fiber before
  | interruptTarget target who extra => exact interruptedAt_driveStep_interruptTarget p table m target who extra rest fiber before
  | afterInterrupt host yielding kind => exact interruptedAt_driveStep_afterInterrupt p table m host yielding kind rest fiber before
  | raceCancel rid host yielding remaining visited => exact interruptedAt_driveStep_raceCancel p table m rid host yielding remaining visited rest fiber before
  | trackChild parent child => exact interruptedAt_driveStep_trackChild p table m parent child rest fiber before
  | observe id exit observer => exact interruptedAt_driveStep_observe p table m id exit observer rest fiber before
  | exitDone target => exact interruptedAt_driveStep_exitDone p table m target rest fiber before
  | closeParAwait host yielding fibers => exact interruptedAt_driveStep_closeParAwait p table m host yielding fibers rest fiber before
  | link mode scope target who extra => exact interruptedAt_driveStep_link p table m mode scope target who extra rest fiber before
  | drainDue  => exact interruptedAt_driveStep_drainDue p table m  rest fiber before
  | wake key phase => exact interruptedAt_driveStep_wake p table m key phase rest fiber before

theorem requestOrInterrupted_driveStep (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (command : NCmd) (rest : List NCmd)
    (state : GuardState m) (queue : GuardQueue p table m (command :: rest))
    (fiber : FiberId) (token : Nat) (request : NativeOp × Val)
    (before : requestOf m fiber token = some request) :
    letI := evaluatorFor p table
    requestOf (driveStep (interpOf p table) m command rest).1 fiber token = some request ∨
      InterruptedAt (driveStep (interpOf p table) m command rest).1 fiber := by
  letI := evaluatorFor p table
  have authority := queue.authority command (List.mem_cons_self ..)
  cases command with
  | evaluate target => exact requestOrInterrupted_driveStep_evaluate p table m target rest fiber token request before
  | loop target yielding => exact requestOrInterrupted_driveStep_loop p table m target yielding rest authority fiber token request before
  | deliver target yielding => exact requestOrInterrupted_driveStep_deliver p table m target yielding rest authority fiber token request before
  | finish target exit => exact Or.inl ((requestOf_driveStep_finish p table m target exit rest authority fiber token).trans before)
  | resume target offered answer => exact requestOrInterrupted_driveStep_resume p table m target offered answer rest queue fiber token request before
  | launch rid => exact Or.inl ((requestOf_driveStep_launch p table m rid rest fiber token).trans before)
  | enrollRace rid child => exact Or.inl ((requestOf_driveStep_enrollRace p table m rid child rest fiber token).trans before)
  | registrationDone rid yielding => exact Or.inl ((requestOf_driveStep_registrationDone p table m rid yielding rest authority fiber token).trans before)
  | interruptTarget target who extra => exact requestOrInterrupted_driveStep_interruptTarget p table m target who extra rest fiber token request before
  | afterInterrupt host yielding kind => exact Or.inl ((requestOf_driveStep_afterInterrupt p table m host yielding kind rest authority fiber token).trans before)
  | raceCancel rid host yielding remaining visited => exact requestOrInterrupted_driveStep_raceCancel p table m rid host yielding remaining visited rest fiber token request before
  | trackChild parent child => exact Or.inl ((requestOf_driveStep_trackChild p table m parent child rest fiber token).trans before)
  | observe id exit observer => exact requestOrInterrupted_driveStep_observe p table m id exit observer rest state queue fiber token request before
  | exitDone target => exact Or.inl ((requestOf_driveStep_exitDone p table m target rest fiber token).trans before)
  | closeParAwait host yielding fibers => exact Or.inl ((requestOf_driveStep_closeParAwait p table m host yielding fibers rest authority fiber token).trans before)
  | link mode scope target who extra => exact requestOrInterrupted_driveStep_link p table m mode scope target who extra rest fiber token request before
  | drainDue  => exact requestOrInterrupted_driveStep_drainDue p table m  rest fiber token request before
  | wake key phase => exact requestOrInterrupted_driveStep_wake p table m key phase rest fiber token request before

end Effect4.Program.Guard
