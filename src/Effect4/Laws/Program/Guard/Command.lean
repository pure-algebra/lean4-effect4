import Effect4.Laws.Program.Guard.Race
import Effect4.Laws.Program.Guard.RegistrationDone
import Effect4.Laws.Program.Guard.NativeQueueAssembly
import Effect4.Laws.Program.Guard.FinishQueue
import Effect4.Laws.Program.Guard.Contract

set_option autoImplicit false
set_option maxRecDepth 2048
namespace Effect4.Program.Guard
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard.RegistrationQueue
open Effect4.Program.Guard.NativeAssembly Effect4.Program.Guard.NativeQueueAssembly Effect4.Program.Guard.Finish Effect4.Program.Guard.FinishQueue

theorem guardState_driveStep (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (command : NCmd) (rest : List NCmd)
    (state : GuardState m) (queue : GuardQueue p table m (command :: rest)) :
    letI := evaluatorFor p table
    GuardState (driveStep (interpOf p table) m command rest).1 := by
  letI := evaluatorFor p table
  have authority := queue.authority command (List.mem_cons_self ..)
  have sites := queue.codeSites command (List.mem_cons_self ..)
  cases command with
  | evaluate target => exact guardState_driveStep_evaluate p table m target rest state
  | loop target yielding => exact guardState_driveStep_loop p table m target yielding rest state authority
  | deliver target yielding => exact guardState_driveStep_deliver p table m target yielding rest state authority
  | finish target exit => exact guardState_driveStep_finish p table m target exit rest state authority
  | resume target token answer => exact guardState_driveStep_resume p table m target token answer rest state sites
  | launch rid => exact guardState_driveStep_launch p table m rid rest state
  | enrollRace rid child => exact guardState_driveStep_enrollRace p table m rid child rest state
  | registrationDone rid yielding => exact guardState_driveStep_registrationDone p table m rid yielding rest state authority
  | interruptTarget target who extra => exact guardState_driveStep_interruptTarget p table m target who extra rest state
  | afterInterrupt host yielding kind => exact guardState_driveStep_afterInterrupt p table m host yielding kind rest state authority sites
  | raceCancel rid host yielding remaining visited => exact guardState_driveStep_raceCancel p table m rid host yielding remaining visited rest state
  | trackChild parent child => exact guardState_driveStep_trackChild p table m parent child rest state
  | observe id exit observer => exact guardState_driveStep_observe p table m id exit observer rest state queue
  | exitDone target => exact guardState_driveStep_exitDone p table m target rest state authority
  | closeParAwait host yielding fibers => exact guardState_driveStep_closeParAwait p table m host yielding fibers rest state authority
  | link mode scope target who extra => exact guardState_driveStep_link p table m mode scope target who extra rest state
  | drainDue => exact guardState_driveStep_drainDue p table m rest state
  | wake key phase => exact guardState_driveStep_wake p table m key phase rest state

theorem guardQueue_driveStep (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (command : NCmd) (rest : List NCmd)
    (state : GuardState m) (queue : GuardQueue p table m (command :: rest))
    (registration : RegistrationQueue (command :: rest)) :
    letI := evaluatorFor p table
    let result := driveStep (interpOf p table) m command rest
    GuardQueue p table result.1 result.2 := by
  letI := evaluatorFor p table
  cases command with
  | evaluate target => exact guardQueue_driveStep_evaluate p table m target rest queue
  | loop target yielding => exact guardQueue_driveStep_loop p table m target yielding rest state queue registration
  | deliver target yielding => exact guardQueue_driveStep_deliver p table m target yielding rest state queue registration
  | finish target exit => exact guardQueue_driveStep_finish p table m target exit rest state queue registration.2
  | resume target token answer => exact guardQueue_driveStep_resume p table m target token answer rest state queue
  | launch rid => exact guardQueue_driveStep_launch p table m rid rest queue
  | enrollRace rid child => exact guardQueue_driveStep_enrollRace p table m rid child rest state queue
  | registrationDone rid yielding => exact guardQueue_driveStep_registrationDone p table m rid yielding rest state queue registration
  | interruptTarget target who extra => exact guardQueue_driveStep_interruptTarget p table m target who extra rest queue
  | afterInterrupt host yielding kind => exact guardQueue_driveStep_afterInterrupt p table m host yielding kind rest state queue registration
  | raceCancel rid host yielding remaining visited => exact guardQueue_driveStep_raceCancel p table m rid host yielding remaining visited rest queue
  | trackChild parent child => exact guardQueue_driveStep_trackChild p table m parent child rest queue
  | observe id exit observer => exact guardQueue_driveStep_observe p table m id exit observer rest state queue
  | exitDone target => exact guardQueue_driveStep_exitDone p table m target rest queue
  | closeParAwait host yielding fibers => exact guardQueue_driveStep_closeParAwait p table m host yielding fibers rest state queue registration
  | link mode scope target who extra => exact guardQueue_driveStep_link p table m mode scope target who extra rest queue
  | drainDue => exact guardQueue_driveStep_drainDue p table m rest state queue
  | wake key phase => exact guardQueue_driveStep_wake p table m key phase rest queue

theorem reservedKeys_driveStep (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (command : NCmd) (rest : List NCmd)
    (state : GuardState m) (queue : GuardQueue p table m (command :: rest))
    (keys : List GuardKey) (reserved : ReservedKeys m keys) :
    letI := evaluatorFor p table
    ReservedKeys (driveStep (interpOf p table) m command rest).1 keys := by
  letI := evaluatorFor p table
  have authority := queue.authority command (List.mem_cons_self ..)
  cases command with
  | evaluate target => exact reservedKeys_driveStep_evaluate p table m target rest keys reserved
  | loop target yielding => exact reservedKeys_driveStep_loop p table m target yielding rest state authority keys reserved
  | deliver target yielding => exact reservedKeys_driveStep_deliver p table m target yielding rest state authority keys reserved
  | finish target exit => exact reservedKeys_driveStep_finish p table m target exit rest authority keys reserved
  | resume target token answer => exact reservedKeys_driveStep_resume p table m target token answer rest keys reserved
  | launch rid => exact reservedKeys_driveStep_launch p table m rid rest keys reserved
  | enrollRace rid child => exact reservedKeys_driveStep_enrollRace p table m rid child rest keys reserved
  | registrationDone rid yielding => exact reservedKeys_driveStep_registrationDone p table m rid yielding rest authority keys reserved
  | interruptTarget target who extra => exact reservedKeys_driveStep_interruptTarget p table m target who extra rest keys reserved
  | afterInterrupt host yielding kind => exact reservedKeys_driveStep_afterInterrupt p table m host yielding kind rest authority keys reserved
  | raceCancel rid host yielding remaining visited => exact reservedKeys_driveStep_raceCancel p table m rid host yielding remaining visited rest keys reserved
  | trackChild parent child => exact reservedKeys_driveStep_trackChild p table m parent child rest keys reserved
  | observe id exit observer => exact reservedKeys_driveStep_observe p table m id exit observer rest state queue keys reserved
  | exitDone target => exact reservedKeys_driveStep_exitDone p table m target rest keys reserved
  | closeParAwait host yielding fibers => exact reservedKeys_driveStep_closeParAwait p table m host yielding fibers rest authority keys reserved
  | link mode scope target who extra => exact reservedKeys_driveStep_link p table m mode scope target who extra rest keys reserved
  | drainDue => exact reservedKeys_driveStep_drainDue p table m rest keys reserved
  | wake key phase => exact reservedKeys_driveStep_wake p table m key phase rest keys reserved

end Effect4.Program.Guard
