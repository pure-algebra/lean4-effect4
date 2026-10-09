module

/-! Capacity-one, replay-zero PubSub bookkeeping with natural messages.
Latest source: `vendor/effect-4.0.1/src/PubSub.ts`, BoundedPubSubSingle, 2539–2680.
Logical names represent model registrations, without a runtime identity encoding.
The Step equations cover arbitrary data states. Source interpretation needs Live and exact numeric admission.
Source number increments must stay admissible; no unbounded JavaScript-number interpretation is claimed.
Placement: pubsub-single-steps-agree, translation-simulation, R10. -/

@[expose] public section
set_option autoImplicit false
namespace Effect4.PubSub.Model

/-- A live model registration. Latest subscription cursor: PubSub.ts:2624. -/
structure Subscriber where
  id : Nat
  cursor : Nat
  deriving DecidableEq, Repr

/-- Latest single-slot fields, with subscriberCount represented by live-list length.
The source's unsubscribed objects have no live entry here. -/
structure State where
  publisherIndex : Nat := 0
  remaining : Nat := 0
  subscribers : List Subscriber := []
  value : Option Nat := none
  deriving DecidableEq, Repr

/-- Source interpretation only: cursor/count invariants, independent of stored Step syntax. -/
def Live (s : State) : Prop :=
  (s.subscribers.map (·.id)).Nodup ∧
  (∀ sub ∈ s.subscribers, sub.cursor ≤ s.publisherIndex) ∧
  (s.remaining = 0 ↔ s.value = none) ∧
  (s.value ≠ none → s.remaining =
    (s.subscribers.filter (fun sub => sub.cursor != s.publisherIndex)).length)

/-- Latest class initial fields: PubSub.ts:2540–2546. -/
def initial : State := {}

/-- A source subscribe allocates a fresh object; logical model names must be fresh too. -/
def Fresh (s : State) (id : Nat) : Prop := ∀ sub ∈ s.subscribers, sub.id ≠ id

/-- Latest subscribe: PubSub.ts:2616–2619. New subscribers see only later publication. -/
def subscribe (s : State) (id : Nat) : Unit × State :=
  ((), { s with subscribers := s.subscribers ++ [⟨id, s.publisherIndex⟩] })

/-- Latest publish: PubSub.ts:2573–2587. No subscribers means successful discard. -/
def tryPublish (s : State) (message : Nat) : Bool × State :=
  if s.remaining != 0 then (false, s)
  else if s.subscribers.isEmpty then (true, s)
  else (true, { s with value := some message, remaining := s.subscribers.length, publisherIndex := s.publisherIndex + 1 })

/-- A live registration that has not read the current publication. -/
def unread (s : State) (id : Nat) : Bool :=
  s.subscribers.any (fun sub => sub.id == id && sub.cursor != s.publisherIndex)

/-- Latest poll: PubSub.ts:2649–2660. The last unread subscriber frees the slot. -/
def poll (s : State) (id : Nat) : Option Nat × State :=
  if s.remaining == 0 || !unread s id then (none, s)
  else
    let remaining := s.remaining - 1
    (s.value, { s with remaining := remaining, value := (if remaining == 0 then none else s.value), subscribers := s.subscribers.map (fun sub => if sub.id == id then { sub with cursor := s.publisherIndex } else sub) })

/-- Latest unsubscribe: PubSub.ts:2669–2679. Only unread ownership reduces retention. -/
def unsubscribe (s : State) (id : Nat) : Unit × State :=
  if !(s.subscribers.any (fun sub => sub.id == id)) then ((), s)
  else
    let remaining := if s.remaining != 0 && unread s id then s.remaining - 1 else s.remaining
    ((), { s with remaining := remaining, value := (if remaining == 0 then none else s.value), subscribers := s.subscribers.filter (fun sub => sub.id != id) })

/-- Latest slide: PubSub.ts:2607–2613. Leave cursors and the publisher index unchanged. -/
def slide (s : State) : Unit × State :=
  if s.remaining == 0 then ((), s) else ((), { s with remaining := 0, value := none })

end Effect4.PubSub.Model
