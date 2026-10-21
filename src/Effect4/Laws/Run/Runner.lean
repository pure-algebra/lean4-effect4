import Effect4.Run.Runner
import Effect4.Laws.Auto.Semantics

/-!
# Queue and tensor equations

Placement before proof work: host-session-protocol, compatibility, `queue-reactor`, R6 and R13.
The registry points to `queue_spec`. The tensor equations serve that claim's concrete host
composition, read by the session battery on the to-do hosts.

Reach: every row, value and reactor state; the right equation requires the left to decline.
These equations establish neither reply admission nor progress. They do not establish general
client-to-reactor agreement, or equality of complete runs. The checked session owns admission.
-/

set_option autoImplicit false
namespace Effect4.Run
open Effect4.Program Effect4.Machine
open Effect4.Api.HostSession (Answer)

/-- queue-reactor: consume the current request on next, and retain the queue on replies. -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem Reactor.queue_spec (requests : List Val) :
    (∀ row sent pending, row.spelling = Api.ServiceSession.nextName →
      Reactor.queue requests row sent pending =
        some (.ofExit (.success (pending.head?.elim .none (fun value => .some value))), pending.tail)) ∧
    (∀ row sent pending, Api.ServiceSession.isReplyRow row = true →
      Reactor.queue requests row sent pending = some (.ofExit (.success .unit), pending)) := by
  constructor
  · intro row sent pending h
    rw [Reactor.queue, h]
    rfl
  · intro row sent pending h
    unfold Reactor.queue
    split
    · next same =>
        have name : row.spelling = Api.ServiceSession.nextName := beq_iff_eq.mp same
        unfold Api.ServiceSession.isReplyRow at h
        rw [name] at h
        contradiction
    · rfl

/-- Helper of queue-reactor, read on the to-do session rows: a left answer retains right state. -/
@[semantics "host-session-protocol" (requirement := R13)]
theorem Reactor.tensor_left {α β : Type} (r : Reactor α) (s : Reactor β)
    (row : Program.Row) (sent : Val) (a : α) (b : β) (answer : Answer) (next : α)
    (h : r row sent a = some (answer, next)) :
    Reactor.tensor r s row sent (a, b) = some (answer, (next, b)) := by
  simp only [Reactor.tensor, h]

/-- Helper of queue-reactor, read on repository rows: when left declines, only right state changes. -/
@[semantics "host-session-protocol" (requirement := R13)]
theorem Reactor.tensor_right {α β : Type} (r : Reactor α) (s : Reactor β)
    (row : Program.Row) (sent : Val) (a : α) (b : β) (h : r row sent a = none) :
    Reactor.tensor r s row sent (a, b) =
      (s row sent b).map (fun (answer, next) => (answer, (a, next))) := by
  simp only [Reactor.tensor, h]

end Effect4.Run
