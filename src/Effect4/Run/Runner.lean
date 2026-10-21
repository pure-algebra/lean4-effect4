import Effect4.Run.Method
import Effect4.Api.Session

/-!
# Reactors on separate state and the session queue

The runner slice (`docs/research/2026-10-21-runner-slice/README.md`, §2.2) reads reactors as
partial comodels. Their call-tree interpretation uses `StateT σ Option`.
Section 2.3 uses Plotkin and Power (2008), Tensors of Comodels and Models for Operational
Semantics: the tensor of comodels on disjoint supported rows.
The product state keeps each component's state separate. Overlapping rows use left priority.
Section 2.5 reads the queue as a reply-blind client through one-step free-monad unfolding: `next`
reads the pending call, and the reply feeds its continuation, which is where the queue advances.
Ahman and Bauer (2020), Runners in Action, supplies the generalized state-monad reading.
The agreement with a general client, which branches on replies, stays open.

These operations compose existing reactors. They add no interpreter or stored program syntax.
The checked session still admits each answer. Declining a call leaves a live frontier.
-/

set_option autoImplicit false
namespace Effect4.Run
open Effect4.Program Effect4.Machine

/-- Combine reactors on separate state. The left answer wins; otherwise the right may answer.
For disjoint supported rows, this is the componentwise tensor of comodels. -/
def Reactor.tensor {α β : Type} (r : Reactor α) (s : Reactor β) : Reactor (α × β) :=
  fun row sent (a, b) =>
    match r row sent a with
    | some (answer, next) => some (answer, (next, b))
    | none => (s row sent b).map fun (answer, next) => (answer, (a, next))

/-- The queue: the reply-blind client as a reactor of the session rows, the image of the free
monad's one-step unfolding on a client whose continuations ignore replies (the slice note, §2.5).
Its state is the remaining requests. `next` answers the head without consuming it, or none at the
end; a reply row consumes the head, as the reply feeds the pending call's continuation; a reply
with no pending call, and any other row, is declined. -/
def Reactor.queue : Reactor (List Val) := fun row _sent pending =>
  if row.spelling == Api.ServiceSession.nextName then
    some (.ofExit (.success (pending.head?.elim .none (fun value => .some value))), pending)
  else if Api.ServiceSession.isReplyRow row then
    match pending with
    | [] => none
    | _ :: rest => some (.ofExit (.success .unit), rest)
  else none

end Effect4.Run
