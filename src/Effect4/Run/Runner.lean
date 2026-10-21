import Effect4.Run.Method
import Effect4.Api.Session

/-!
# Reactors on separate state and the session queue

The runner slice (`docs/research/2026-10-21-runner-slice/README.md`, §2.2) reads reactors as
partial comodels. Their call-tree interpretation uses `StateT σ Option`.
Section 2.3 uses Plotkin and Power (2008), Tensors of Comodels and Models for Operational
Semantics: the tensor of comodels on disjoint supported rows.
The product state keeps each component's state separate. Overlapping rows use left priority.
Section 2.5 reads the queue as a reply-blind client through one-step free-monad unfolding.
Ahman and Bauer (2020), Runners in Action, supplies the generalized state-monad reading.
The queue and client agree only under the session's next/reply ordering; that general law stays open.

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

/-- A reply-blind session client. `next` consumes the current state's head; replies keep state.
The caller supplies the initial list to `Run.runWith`. The brief's `requests` parameter does
not capture or reset it. The checked session admits the request returned by `next`. -/
def Reactor.queue (_requests : List Val) : Reactor (List Val) := fun row _sent pending =>
  if row.spelling == Api.ServiceSession.nextName then
    some (.ofExit (.success (pending.head?.elim .none (fun value => .some value))), pending.tail)
  else if Api.ServiceSession.isReplyRow row then
    some (.ofExit (.success .unit), pending)
  else none

end Effect4.Run
