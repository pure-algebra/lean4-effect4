/-!
# The Queue's transition contract, as a pure model (research probe, 2026-10-05)

Not part of the tree. It imports nothing from `Effect4`. Run it from the repository root:
`lake env lean docs/research/2026-10-05-claude-lead/queue-contract/QueueContract.lean`.

This is the whole queue under decisions rows 219 to 222, one pure step for each operation:

* **Strict request order** (row 219). A take consumes only when it is ready and no earlier taker
  waits. A request that never waits (`poll`, `clear`) consumes only when no taker waits.
* **Consumption at the taker's own step.** A message leaves the buffer, or a pending offer, only
  in the step of the request that receives it. A signal reserves nothing.
* **Offers are accepted in arrival order,** by the step that frees room. That step also decides
  the offerer's answer, so an offerer's signal carries its answer.
* **The release's rules where the pin is defective:** a batch keeps its minimum; a closing queue
  wakes its takers; a withdrawn offer leaves in every phase.
* **Capacity zero** is a rendezvous for the `suspend` strategy: an offer stays pending until a
  taker's step takes its message. `sliding` and `dropping` at capacity zero are not formed.

Each step answers the new state, a reply, and the signals to post. The model does not deliver a
signal. A signal with the note `again` invites its request to run its step again; any other note
is the request's answer.

Every `#guard` is a finite check on the named trace, and the exploration at the end is bounded.
The model has no fibers, no wrapper, no interruption and no delivery. It proves nothing about
the tree.
-/

namespace QueueContract

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

def room (s : State) : Nat :=
  match s.capacity with
  | none => 1000000
  | some c => c - s.messages.length

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
def acceptLoop : Nat → List Nat → List Offer → List Nat × List Offer × List Signal
  | _, msgs, [] => (msgs, [], [])
  | room, msgs, o :: rest =>
    if room = 0 then (msgs, o :: rest, [])
    else
      let k := Nat.min room o.rest.length
      let msgs' := msgs ++ o.rest.take k
      let left := o.rest.drop k
      if left.isEmpty then
        let r := acceptLoop (room - k) msgs' rest
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

/-- `clear`: every buffered message, and it never waits. It passes no waiting taker. -/
def clear (s : State) : State × ClearReply × List Signal :=
  match s.phase with
  | .done .ended => (s, .got [], [])
  | .done e => (s, .stopped e, [])
  | _ =>
    if !s.takers.isEmpty || (front s).isNone then (s, .got [], [])
    else
      let p := pull s 1000000
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
  else if room s > 0 then
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
      let k := Nat.min (room s) ms.length
      let s1 := { s with messages := s.messages ++ ms.take k }
      (s1, .left (ms.drop k), wake s1)
    | .suspend =>
      if !s.offers.isEmpty then
        ({ s with offers := s.offers ++ [⟨id, true, ms⟩] }, .wait, [])
      else
        let k := Nat.min (room s) ms.length
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

def T (id : Nat) (min : Nat := 1) (max : Nat := 1) : Taker := ⟨id, min, max⟩

/-! ## Controls: the order and the point of consumption (row 219) -/

/-- P1. A waits first; a message arrives; a new taker B does not pass A; A receives it. -/
def strictOrder : TakeReply × List Signal × TakeReply × TakeReply :=
  let a := take {} (T 1)
  let o := offer a.1 100 10
  let b := take o.1 (T 2)
  let a2 := take b.1 (T 1)
  (a.2.1, o.2.2, b.2.1, a2.2.1)

#guard strictOrder = (.wait, [⟨1, .again⟩], .wait, .got [10])

/-- No reservation. T1 and T2 wait; two messages arrive; T1 leaves; T2 receives the first
message and a new T3 the second. -/
def noReservation : List TakeReply :=
  let s := (take {} (T 1)).1
  let s := (take s (T 2)).1
  let s := (offer s 100 10).1
  let s := (offer s 101 20).1
  let s := (withdrawTake s 1).1
  let r2 := take s (T 2)
  let r3 := take r2.1 (T 3)
  [r2.2.1, r3.2.1]

#guard noReservation = [.got [10], .got [20]]

/-- The signed difference from 4.0.1: a batch at the head blocks a smaller take. -/
def headBatchBlocks : List Signal × TakeReply :=
  let s := (offer {} 100 10).1
  let s := (take s (T 1 3 5)).1
  (wake s, (take s (T 2)).2.1)

#guard headBatchBlocks = ([], .wait)

/-- P2. A take of three to five waits until three messages are buffered. -/
def keepsMinimum : List TakeReply × List Signal :=
  let t := T 1 3 5
  let s := (take {} t).1
  let o1 := offer s 100 1
  let r1 := take o1.1 t
  let o2 := offer r1.1 101 2
  let o3 := offer o2.1 102 3
  let r3 := take o3.1 t
  ([r1.2.1, r3.2.1], o1.2.2 ++ o2.2.2 ++ o3.2.2)

#guard keepsMinimum = ([.wait, .got [1, 2, 3]], [⟨1, .again⟩])

/-- A bound of zero answers the empty batch, after the test for a done queue. -/
def zeroBounds : TakeReply × TakeReply :=
  ((take {} (T 1 0 5)).2.1, (take (close {} .ended).1 (T 1 0 5)).2.1)

#guard zeroBounds = (.got [], .stopped .ended)

/-- `poll` passes no waiting taker. -/
def pollRules : Option Nat × Option Nat × Option Nat :=
  let one := (offer {} 100 10).1
  ((poll one).2.1, (poll (take one (T 1 3 5)).1).2.1, (poll (close {} .ended).1).2.1)

#guard pollRules = (some 10, none, none)

/-- `clear` takes every message, passes no waiting taker, and answers by the queue's end. -/
def clearRules : ClearReply × ClearReply × ClearReply × ClearReply :=
  let two := (offer (offer {} 100 10).1 101 20).1
  let blocked := (take (offer {} 100 10).1 (T 1 3 5)).1
  ((clear two).2.1, (clear blocked).2.1, (clear (close {} .ended).1).2.1,
    (clear (close {} (.failed 5)).1).2.1)

#guard clearRules = (.got [10, 20], .got [], .got [], .stopped (.failed 5))

/-- `peek` waits on an empty queue, is named by an offer, and leaves the message. -/
def peekRules : PeekReply × List Signal × PeekReply × TakeReply :=
  let p := peek {} 5
  let o := offer p.1 100 10
  let p2 := peek o.1 5
  (p.2, o.2.2, p2.2, (take p2.1 (T 1)).2.1)

#guard peekRules = (.wait, [⟨5, .again⟩], .saw 10, .got [10])

/-! ## Controls: offers -/

/-- Offers are accepted in arrival order. Capacity one holds `10`; B waits with `20`; C waits
with `30` behind B; each take admits one. -/
def offersInOrder : List OfferReply × List TakeReply × List Signal :=
  let s : State := { capacity := some 1 }
  let s := (offer s 100 10).1
  let b := offer s 101 20
  let c := offer b.1 102 30
  let r1 := take c.1 (T 1)
  let r2 := take r1.1 (T 2)
  ([b.2.1, c.2.1], [r1.2.1, r2.2.1], r1.2.2 ++ r2.2.2)

#guard offersInOrder =
  ([.wait, .wait], [.got [10], .got [20]], [⟨101, .offered true⟩, ⟨102, .offered true⟩])

/-- A batch offer: the part that fits is accepted, and the rest waits and is answered later. -/
def offerAllSuspend : OfferAllReply × TakeReply × List Signal × List Nat :=
  let o := offerAll { capacity := some 2 } 100 [1, 2, 3]
  let r := take o.1 (T 1)
  (o.2.1, r.2.1, r.2.2, r.1.messages)

#guard offerAllSuspend = (.wait, .got [1], [⟨100, .left []⟩], [2, 3])

#guard (offerAll { capacity := some 2, strategy := .dropping } 100 [1, 2, 3]).2.1 = .left [3]
#guard (offerAll { capacity := some 2, strategy := .sliding, messages := [9] } 100 [1, 2, 3]).1.messages
  = [2, 3]
#guard (offerAll (close {} .ended).1 100 [1, 2]).2.1 = .left [1, 2]
#guard (offerAll {} 100 []).2.1 = .left []
#guard (offer (offer { capacity := some 1, strategy := .dropping } 100 10).1 101 20).2.1
  = .accepted false
#guard (offer (offer { capacity := some 1, strategy := .sliding } 100 10).1 101 20).1.messages = [20]

/-! ## Controls: the ends -/

/-- P3. One message is buffered; a take of three waits; the queue ends. The taker is named,
receives what is left, and the queue is done. -/
def closingServes : List Signal × TakeReply × Phase × TakeReply :=
  let t := T 1 3 5
  let s := (offer {} 100 10).1
  let s := (take s t).1
  let c := close s .ended
  let r := take c.1 t
  (c.2.2, r.2.1, r.1.phase, (take r.1 (T 2)).2.1)

#guard closingServes = ([⟨1, .again⟩], .got [10], .done .ended, .stopped .ended)

/-- P4. A full queue; an offer waits; the queue ends; the offer is withdrawn. The buffered
message is still served, and the withdrawn message is not. -/
def withdrawnOffer : OfferReply × Phase × TakeReply × Phase × TakeReply :=
  let s : State := { capacity := some 1 }
  let s := (offer s 100 10).1
  let o := offer s 101 20
  let c := close o.1 .ended
  let w := withdrawOffer c.1 101
  let r := take w.1 (T 1)
  (o.2.1, w.1.phase, r.2.1, r.1.phase, (take r.1 (T 2)).2.1)

#guard withdrawnOffer = (.wait, .closing .ended, .got [10], .done .ended, .stopped .ended)

/-- A failure drains like an end, and every later request sees it. -/
def failThenDrain : Phase × AwaitReply × TakeReply × List Signal × TakeReply :=
  let s := (offer {} 100 10).1
  let a := awaitQ s 7
  let c := close a.1 (.failed 5)
  let r := take c.1 (T 1)
  (c.1.phase, a.2, r.2.1, r.2.2, (take r.1 (T 2)).2.1)

#guard failThenDrain =
  (.closing (.failed 5), .wait, .got [10], [⟨7, .over (.failed 5)⟩], .stopped (.failed 5))

/-- A second end answers `false`, and a closing queue accepts no offer. -/
def closedTwice : Bool × OfferReply :=
  let c := (close (offer {} 100 10).1 .ended).1
  ((close c .ended).2.1, (offer c 101 20).2.1)

#guard closedTwice = (false, .accepted false)

/-- `shutdown` answers each pending offer with what was not accepted, and drops the buffer. -/
def shutdownAnswers : Bool × List Signal × Phase × TakeReply × Nat :=
  let s : State := { capacity := some 1 }
  let s := (offer s 100 10).1
  let s := (offer s 101 20).1
  let s := (offerAll s 102 [30, 40]).1
  let s := (awaitQ s 7).1
  let d := shutdown s
  (d.2.1, d.2.2, d.1.phase, (take d.1 (T 1)).2.1, size d.1)

#guard shutdownAnswers =
  (true, [⟨101, .offered false⟩, ⟨102, .left [30, 40]⟩, ⟨7, .over .interrupted⟩],
    .done .interrupted, .stopped .interrupted, 0)

#guard (awaitQ (close {} .ended).1 7).2 = .over .ended

/-! ## Controls: capacity zero -/

/-- An offer waits until a taker's step takes its message. Nothing is ever buffered. -/
def rendezvousOfferFirst : OfferReply × TakeReply × List Signal :=
  let o := offer { capacity := some 0 } 100 10
  let r := take o.1 (T 1)
  (o.2.1, r.2.1, r.2.2)

#guard rendezvousOfferFirst = (.wait, .got [10], [⟨100, .offered true⟩])

def rendezvousTakerFirst : TakeReply × OfferReply × List Signal × TakeReply :=
  let t := take { capacity := some 0 } (T 1)
  let o := offer t.1 100 10
  (t.2.1, o.2.1, o.2.2, (take o.1 (T 1)).2.1)

#guard rendezvousTakerFirst = (.wait, .wait, [⟨1, .again⟩], .got [10])

/-- Either party may leave before the taker's step, and nothing was done. The taker leaves:
the offer is still pending, and a later take receives it. The offerer leaves: the taker's next
attempt waits again. -/
def rendezvousWithdrawals : Nat × Nat × TakeReply × TakeReply :=
  let s := (take { capacity := some 0 } (T 1)).1
  let s := (offer s 100 10).1
  let w := (withdrawTake s 1).1
  let later := take w (T 2)
  let s2 := (withdrawOffer s 100).1
  (w.messages.length, w.offers.length, later.2.1, (take s2 (T 1)).2.1)

#guard rendezvousWithdrawals = (0, 1, .got [10], .wait)

#guard formed {} && formed { capacity := some 0 }
#guard !formed { capacity := some 0, strategy := .sliding }
#guard !formed { capacity := some 0, strategy := .dropping }

/-! ## A bounded exploration

Every sequence of at most five operations from eleven, on each formed configuration. Three
properties hold after each step:

* `within`: a bounded queue never exceeds its capacity;
* `tidy`: a done queue holds nothing and nobody; a closing queue holds something; a pending
  offer means no room;
* `quiet`: the oldest taker, when it is ready, was signalled; each peeker, when a message is in
  front, was signalled.

`forward := false` is the red control: a queue that starts closing names nobody, as rc.112 did
(P3). -/

inductive Op
  | take (id min max : Nat) | poll | peek (id : Nat)
  | offer (id a : Nat) | offerAll (id : Nat) (ms : List Nat)
  | clear | close (e : End) | shutdown
  | dropTake (id : Nat) | dropOffer (id : Nat)

structure Run where
  s : State
  /-- The takers and peekers that a signal named and that did not run again yet. -/
  signalled : List Nat := []
  ok : Bool := true

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
  (s.offers.isEmpty || room s == 0)

def quiet (s : State) (signalled : List Nat) : Bool :=
  (match s.takers with
    | t :: _ => !ready s t.min || signalled.contains t.id
    | [] => true) &&
  ((front s).isNone || s.peekers.all signalled.contains)

def bump (r : Run) (s : State) (rerun : Option Nat) (signals : List Signal) : Run :=
  let kept := match rerun with
    | some id => r.signalled.filter (· != id)
    | none => r.signalled
  let now := kept ++ (signals.filter (fun g => g.note == Note.again)).map (·.id)
  { s := s, signalled := now, ok := r.ok && within s && tidy s && quiet s now }

def step (forward : Bool) (r : Run) : Op → Run
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
    bump r x.1 none (if forward then x.2.2 else [])
  | .shutdown =>
    let x := shutdown r.s
    bump r x.1 none x.2.2
  | .dropTake id =>
    let x := withdrawTake r.s id
    bump r x.1 (some id) x.2
  | .dropOffer id =>
    let x := withdrawOffer r.s id
    bump r x.1 none x.2

def ops : List Op :=
  [.take 1 1 1, .take 2 2 3, .poll, .peek 5, .offer 100 10, .offerAll 101 [20, 30], .clear,
   .close .ended, .shutdown, .dropTake 1, .dropOffer 101]

/-- The count of runs explored, and whether every one kept the three properties. -/
def explore (forward : Bool) : Nat → Run → Nat × Bool
  | 0, r => (1, r.ok)
  | n + 1, r =>
    if !r.ok then (1, false)
    else ops.foldl (fun acc op =>
      let x := explore forward n (step forward r op)
      (acc.1 + x.1, acc.2 && x.2)) (1, true)

def exploreAt (strategy : Strategy) (capacity : Option Nat) (depth : Nat)
    (forward : Bool := true) : Nat × Bool :=
  explore forward depth { s := { strategy := strategy, capacity := capacity } }

#eval [none, some 0, some 1, some 2].map (exploreAt .suspend · 5)
#eval [some 1, some 2].map (exploreAt .dropping · 5)
#eval [some 1, some 2].map (exploreAt .sliding · 5)

#guard [none, some 0, some 1, some 2].all fun c => (exploreAt .suspend c 5).2
#guard [some 1, some 2].all fun c => (exploreAt .dropping c 5).2
#guard [some 1, some 2].all fun c => (exploreAt .sliding c 5).2

/-- The red control: when a closing queue names nobody, the exploration finds a ready taker
that no signal named. -/
def closingNamesNobody : Bool := !(exploreAt .suspend none 5 (forward := false)).2

#guard closingNamesNobody

end QueueContract
