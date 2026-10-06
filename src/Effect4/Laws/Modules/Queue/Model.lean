/-!
# The Queue's abstract transition model (decisions rows 219 to 222, 240 to 243 and 255)

The model of the packet `Test/contracts/queue.contract.md`, with its diagnostic runner. No effect,
no wrapper and no delivery of a signal occurs here: a step answers a state, a reply and the
signals to post.

Its definitions are the research model's, byte for byte
(`docs/research/2026-10-05-claude-lead/queue-contract/QueueContract.lean` at `da41297b`). Codex
extracted them, and the coordinator built them on 2026-10-05. The file came into the law graph
from the batteries the same day (decisions row 255): its namespace changed, and no definition.
-/

namespace Effect4.Queue.Model

/-- How a queue ended: the clean end (the release's `Done`), a failure with a cause, or the
interrupt that a shutdown of an open queue leaves. -/
inductive End | ended | failed (cause : Nat) | interrupted
  deriving DecidableEq, Repr

inductive Phase | opened | closing (e : End) | done (e : End)
  deriving DecidableEq, Repr

inductive Strategy | suspend | dropping | sliding
  deriving DecidableEq, Repr

/-- A consuming request that waits: its identity and its bounds. -/
structure Taker where
  id : Nat
  min : Nat
  max : Nat
  deriving DecidableEq, Repr

/-- A pending offer: its identity, whether it is a batch, and the messages not yet accepted. -/
structure Offer where
  id : Nat
  batch : Bool
  rest : List Nat
  deriving DecidableEq, Repr

structure State where
  messages : List Nat := []
  /-- `none` is unbounded. -/
  capacity : Option Nat := none
  strategy : Strategy := .suspend
  /-- Arrival order. -/
  takers : List Taker := []
  peekers : List Nat := []
  /-- Arrival order. -/
  offers : List Offer := []
  awaiters : List Nat := []
  phase : Phase := .opened
  deriving DecidableEq, Repr

/-- What a signal tells the request that it names. -/
inductive Note
  /-- Run your step again: a taker or a peeker. -/
  | again
  /-- A single offer's answer. -/
  | offered (ok : Bool)
  /-- A batch offer's answer: the messages that were not accepted. -/
  | left (rest : List Nat)
  /-- An awaiter's answer. -/
  | over (e : End)
  deriving DecidableEq, Repr

structure Signal where
  id : Nat
  note : Note
  deriving DecidableEq, Repr

/-- The configurations that the contract forms (row 219). -/
def formed (s : State) : Bool :=
  match s.capacity, s.strategy with
  | some 0, .suspend => true
  | some 0, _ => false
  | _, _ => true

def isDone (s : State) : Bool := match s.phase with | .done _ => true | _ => false
def isOpen (s : State) : Bool := match s.phase with | .opened => true | _ => false
def isClosing (s : State) : Bool := match s.phase with | .closing _ => true | _ => false

/-- The room that is left. `none` is no limit: an unbounded queue has no number here. -/
def room (s : State) : Option Nat := s.capacity.map (· - s.messages.length)

def hasRoom (s : State) : Bool :=
  match room s with
  | none => true
  | some r => decide (0 < r)

/-- How many of `n` messages fit in the room that is left. -/
def fit (room : Option Nat) (n : Nat) : Nat :=
  match room with
  | none => n
  | some r => Nat.min r n

/-- The least buffer length that serves a minimum (the release's `canTake`): a closing queue
serves any message, and a capacity caps the minimum. -/
def threshold (s : State) (min : Nat) : Nat :=
  if isClosing s then 1
  else match s.capacity with
    | none => min
    | some 0 => Nat.min min 1
    | some c => Nat.min min c

/-- Capacity zero: a taker is served from the first pending offer. -/
def rendezvous (s : State) : Bool :=
  s.capacity == some 0 && !isDone s && !s.offers.isEmpty

def ready (s : State) (min : Nat) : Bool :=
  (!s.messages.isEmpty && decide (threshold s min ≤ s.messages.length)) || rendezvous s

/-- The message that a take would consume next. -/
def front (s : State) : Option Nat :=
  match s.messages with
  | m :: _ => some m
  | [] => if rendezvous s then s.offers.head?.bind (·.rest.head?) else none

/-- The takers that wait before request `id`: every taker when `id` does not wait yet. -/
def earlier (s : State) (id : Nat) : List Taker :=
  s.takers.takeWhile (fun t => t.id != id)

def removeTaker (s : State) (id : Nat) : State :=
  { s with takers := s.takers.filter (fun t => t.id != id) }

/-- The requests to signal: the oldest taker when it is ready, and every peeker when a message
is in front. -/
def wake (s : State) : List Signal :=
  let taker := match s.takers with
    | t :: _ => if ready s t.min then [⟨t.id, .again⟩] else []
    | [] => []
  let peeks := if (front s).isSome then s.peekers.map (⟨·, .again⟩) else []
  taker ++ peeks

def answerOf (o : Offer) (rest : List Nat) : Note :=
  if o.batch then .left rest else .offered rest.isEmpty

/-- Pending offers enter the buffer in arrival order while room remains. An offer that is
accepted whole is answered. -/
def acceptLoop : Option Nat → List Nat → List Offer → List Nat × List Offer × List Signal
  | _, msgs, [] => (msgs, [], [])
  | room, msgs, o :: rest =>
    if room = some 0 then (msgs, o :: rest, [])
    else
      let k := fit room o.rest.length
      let msgs' := msgs ++ o.rest.take k
      let left := o.rest.drop k
      if left.isEmpty then
        let r := acceptLoop (room.map (· - k)) msgs' rest
        (r.1, r.2.1, ⟨o.id, answerOf o []⟩ :: r.2.2)
      else (msgs', { o with rest := left } :: rest, [])

def accept (s : State) : State × List Signal :=
  let r := acceptLoop (room s) s.messages s.offers
  ({ s with messages := r.1, offers := r.2.1 }, r.2.2)

/-- A closing queue with nothing left is done. Every request that waits is signalled and leaves. -/
def settle (s : State) : State × List Signal :=
  match s.phase with
  | .closing e =>
    if s.messages.isEmpty && s.offers.isEmpty then
      ({ s with phase := .done e, takers := [], peekers := [], awaiters := [] },
        s.takers.map (⟨·.id, .again⟩) ++ s.peekers.map (⟨·, .again⟩) ++
          s.awaiters.map (⟨·, .over e⟩))
    else (s, [])
  | _ => (s, [])

/-- The messages that a consuming step receives. From the buffer: up to `max`. At a rendezvous:
one message of the first pending offer, whose offerer is answered when its offer is spent. -/
def pull (s : State) (max : Nat) : List Nat × State × List Signal :=
  if s.messages.isEmpty then
    match s.offers with
    | o :: rest =>
      match o.rest with
      | m :: more =>
        if more.isEmpty then ([m], { s with offers := rest }, [⟨o.id, answerOf o []⟩])
        else ([m], { s with offers := { o with rest := more } :: rest }, [])
      | [] => ([], { s with offers := rest }, [])
    | [] => ([], s, [])
  else (s.messages.take max, { s with messages := s.messages.drop max }, [])

/-- What every consuming step does after it consumed: accept pending offers, finish a closing
queue, and name the requests that became ready. -/
def afterConsume (s : State) : State × List Signal :=
  let a := accept s
  let d := settle a.1
  (d.1, a.2 ++ d.2 ++ wake d.1)

/-! ## The consuming operations -/

inductive TakeReply | got (ms : List Nat) | wait | stopped (e : End)
  deriving DecidableEq, Repr

/-- `take`, `takeN`, `takeBetween` and `takeAll`, by their bounds. One atomic step. -/
def take (s : State) (t : Taker) : State × TakeReply × List Signal :=
  match s.phase with
  | .done e => (removeTaker s t.id, .stopped e, [])
  | _ =>
    if t.min = 0 || t.max = 0 then (s, .got [], [])
    else if ready s t.min && (earlier s t.id).isEmpty then
      let p := pull (removeTaker s t.id) t.max
      let r := afterConsume p.2.1
      (r.1, .got p.1, p.2.2 ++ r.2)
    else if s.takers.any (fun u => u.id == t.id) then (s, .wait, [])
    else ({ s with takers := s.takers ++ [t] }, .wait, [])

/-- `poll`: one message, and it never waits. It passes no waiting taker. -/
def poll (s : State) : State × Option Nat × List Signal :=
  if isDone s || !(ready s 1) || !s.takers.isEmpty then (s, none, [])
  else
    let p := pull s 1
    let r := afterConsume p.2.1
    (r.1, p.1.head?, p.2.2 ++ r.2)

inductive ClearReply | got (ms : List Nat) | stopped (e : End)
  deriving DecidableEq, Repr

/-- `clear`: every buffered message, and it never waits. It passes no waiting taker, so its
empty answer does not say that the buffer is empty. At a rendezvous nothing is buffered, and
`clear` takes what a take would: the first message of the first pending offer, as the release's
`takeAllUnsafe` does. Pending offers may refill the room that it frees, in the same step. -/
def clear (s : State) : State × ClearReply × List Signal :=
  match s.phase with
  | .done .ended => (s, .got [], [])
  | .done e => (s, .stopped e, [])
  | _ =>
    if !s.takers.isEmpty || (front s).isNone then (s, .got [], [])
    else
      let p := pull s s.messages.length
      let r := afterConsume p.2.1
      (r.1, .got p.1, p.2.2 ++ r.2)

inductive PeekReply | saw (m : Nat) | wait | stopped (e : End)
  deriving DecidableEq, Repr

/-- `peek`: the message in front, which stays. It holds no turn. -/
def peek (s : State) (id : Nat) : State × PeekReply :=
  let out := { s with peekers := s.peekers.filter (· != id) }
  match s.phase with
  | .done e => (out, .stopped e)
  | _ =>
    match front s with
    | some m => (out, .saw m)
    | none => if s.peekers.contains id then (s, .wait) else ({ s with peekers := s.peekers ++ [id] }, .wait)

/-! ## The offering operations -/

inductive OfferReply | accepted (ok : Bool) | wait
  deriving DecidableEq, Repr

def offer (s : State) (id a : Nat) : State × OfferReply × List Signal :=
  if !isOpen s then (s, .accepted false, [])
  else if s.strategy == .suspend && !s.offers.isEmpty then
    ({ s with offers := s.offers ++ [⟨id, false, [a]⟩] }, .wait, [])
  else if hasRoom s then
    let s1 := { s with messages := s.messages ++ [a] }
    (s1, .accepted true, wake s1)
  else
    match s.strategy with
    | .dropping => (s, .accepted false, [])
    | .sliding =>
      let s1 := { s with messages := s.messages.drop 1 ++ [a] }
      (s1, .accepted true, wake s1)
    | .suspend =>
      let s1 := { s with offers := s.offers ++ [⟨id, false, [a]⟩] }
      (s1, .wait, wake s1)

inductive OfferAllReply | left (rest : List Nat) | wait
  deriving DecidableEq, Repr

/-- `offerAll`: `left []` means that every message was accepted. -/
def offerAll (s : State) (id : Nat) (ms : List Nat) : State × OfferAllReply × List Signal :=
  if ms.isEmpty then (s, .left [], [])
  else if !isOpen s then (s, .left ms, [])
  else
    match s.strategy with
    | .sliding =>
      let all := s.messages ++ ms
      let keep := match s.capacity with
        | none => all
        | some c => all.drop (all.length - c)
      let s1 := { s with messages := keep }
      (s1, .left [], wake s1)
    | .dropping =>
      let k := fit (room s) ms.length
      let s1 := { s with messages := s.messages ++ ms.take k }
      (s1, .left (ms.drop k), wake s1)
    | .suspend =>
      if !s.offers.isEmpty then
        ({ s with offers := s.offers ++ [⟨id, true, ms⟩] }, .wait, [])
      else
        let k := fit (room s) ms.length
        let rest := ms.drop k
        let s1 := { s with messages := s.messages ++ ms.take k }
        if rest.isEmpty then (s1, .left [], wake s1)
        else
          let s2 := { s1 with offers := s1.offers ++ [⟨id, true, rest⟩] }
          (s2, .wait, wake s2)

/-! ## The ends -/

/-- `end`, `fail`, `failCause` and `interrupt`, by their end. A queue with nothing left is done
at once; otherwise it closes and drains. -/
def close (s : State) (e : End) : State × Bool × List Signal :=
  if !isOpen s then (s, false, [])
  else
    let d := settle { s with phase := .closing e }
    (d.1, true, d.2 ++ wake d.1)

/-- `shutdown`: the buffer and the pending offers are dropped, and each offerer is answered. -/
def shutdown (s : State) : State × Bool × List Signal :=
  match s.phase with
  | .done _ => (s, false, [])
  | p =>
    let e := match p with
      | .closing e => e
      | _ => .interrupted
    ({ s with messages := [], offers := [], takers := [], peekers := [], awaiters := [],
              phase := .done e }, true,
      s.takers.map (⟨·.id, .again⟩) ++ s.peekers.map (⟨·, .again⟩) ++
        s.offers.map (fun o => ⟨o.id, answerOf o o.rest⟩) ++ s.awaiters.map (⟨·, .over e⟩))

inductive AwaitReply | over (e : End) | wait
  deriving DecidableEq, Repr

/-- `await`: the queue's end. The wrapper answers `ended` as success and any other end as a
failure. -/
def awaitQ (s : State) (id : Nat) : State × AwaitReply :=
  match s.phase with
  | .done e => (s, .over e)
  | _ => if s.awaiters.contains id then (s, .wait) else ({ s with awaiters := s.awaiters ++ [id] }, .wait)

def size (s : State) : Nat := if isDone s then 0 else s.messages.length

def isFull (s : State) : Bool := s.capacity == some (size s)

/-! ## The withdrawals -/

/-- A taker leaves. The next taker may now be the oldest, so it is named when it is ready. -/
def withdrawTake (s : State) (id : Nat) : State × List Signal :=
  let s1 := removeTaker s id
  (s1, wake s1)

def withdrawPeek (s : State) (id : Nat) : State :=
  { s with peekers := s.peekers.filter (· != id) }

def withdrawAwait (s : State) (id : Nat) : State :=
  { s with awaiters := s.awaiters.filter (· != id) }

/-- A pending offer leaves, in every phase but the last. What was already accepted of a batch
stays. A closing queue with nothing left is then done. -/
def withdrawOffer (s : State) (id : Nat) : State × List Signal :=
  if isDone s then (s, [])
  else
    let d := settle { s with offers := s.offers.filter (fun o => o.id != id) }
    (d.1, d.2 ++ wake d.1)

inductive Op
  | take (id min max : Nat) | poll | peek (id : Nat)
  | offer (id a : Nat) | offerAll (id : Nat) (ms : List Nat)
  | clear | close (e : End) | shutdown | await (id : Nat)
  | dropTake (id : Nat) | dropOffer (id : Nat) | dropPeek (id : Nat) | dropAwait (id : Nat)

/-- A deliberate defect, for a red control. -/
inductive Fault | none | closing | shutdown
  deriving DecidableEq

structure Run where
  s : State
  /-- The takers and peekers that a signal named and that did not run again yet. -/
  signalled : List Nat := []
  /-- The three properties of the state, so far. -/
  ok : Bool := true
  /-- The property of the step, so far. -/
  named : Bool := true

def within (s : State) : Bool :=
  match s.capacity with
  | none => true
  | some c => decide (s.messages.length ≤ c)

def tidy (s : State) : Bool :=
  (match s.phase with
    | .done _ => s.takers.isEmpty && s.peekers.isEmpty && s.offers.isEmpty && s.awaiters.isEmpty
        && s.messages.isEmpty
    | .closing _ => !(s.messages.isEmpty && s.offers.isEmpty)
    | .opened => true) &&
  (s.offers.isEmpty || room s == some 0)

def quiet (s : State) (signalled : List Nat) : Bool :=
  (match s.takers with
    | t :: _ => !ready s t.min || signalled.contains t.id
    | [] => true) &&
  ((front s).isNone || s.peekers.all signalled.contains)

/-- The identity of every request that waits. The lists of the exploration use one identity
for one request. -/
def waiting (s : State) : List Nat :=
  s.takers.map (·.id) ++ s.peekers ++ s.offers.map (·.id) ++ s.awaiters

def accounted (before after : State) (self : Option Nat) (signals : List Signal) : Bool :=
  (waiting before).all fun id =>
    (waiting after).contains id || self == some id || signals.any (·.id == id)

/-- One step's result joins the run. `self` is the step's own request: it runs again, so it is
no longer owed a signal, and it may leave without one. -/
def bump (r : Run) (s : State) (self : Option Nat) (signals : List Signal) : Run :=
  let kept := match self with
    | some id => r.signalled.filter (· != id)
    | none => r.signalled
  let now := kept ++ (signals.filter (fun g => g.note == Note.again)).map (·.id)
  { s := s, signalled := now, ok := r.ok && within s && tidy s && quiet s now,
    named := r.named && accounted r.s s self signals }

def step (fault : Fault) (r : Run) : Op → Run
  | .take id min max =>
    let x := take r.s ⟨id, min, max⟩
    bump r x.1 (some id) x.2.2
  | .poll =>
    let x := poll r.s
    bump r x.1 none x.2.2
  | .peek id =>
    let x := peek r.s id
    bump r x.1 (some id) []
  | .offer id a =>
    if r.s.offers.any (fun o => o.id == id) then r
    else
      let x := offer r.s id a
      bump r x.1 none x.2.2
  | .offerAll id ms =>
    if r.s.offers.any (fun o => o.id == id) then r
    else
      let x := offerAll r.s id ms
      bump r x.1 none x.2.2
  | .clear =>
    let x := clear r.s
    bump r x.1 none x.2.2
  | .close e =>
    let x := close r.s e
    bump r x.1 none (if fault == .closing then [] else x.2.2)
  | .shutdown =>
    let x := shutdown r.s
    bump r x.1 none (if fault == .shutdown then [] else x.2.2)
  | .await id =>
    let x := awaitQ r.s id
    bump r x.1 (some id) []
  | .dropTake id =>
    let x := withdrawTake r.s id
    bump r x.1 (some id) x.2
  | .dropOffer id =>
    let x := withdrawOffer r.s id
    bump r x.1 (some id) x.2
  | .dropPeek id => bump r (withdrawPeek r.s id) (some id) []
  | .dropAwait id => bump r (withdrawAwait r.s id) (some id) []

end Effect4.Queue.Model
