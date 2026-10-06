import Effect4.Laws.Modules.Queue.Model

/-!
# The Queue's abstract contract: the small named controls

Finite controls of `src/Effect4/Laws/Modules/Queue/Model.lean`, one input each. They are the
research model's
controls, byte for byte, without its two million-element controls and its bounded exploration.
Those stay beside the research model, in `QueueLargeControls.lean`, outside every default import.
-/

namespace Test.Program.QueueContract
open Effect4.Queue.Model
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

/-! ## Controls: an offer's acceptance and its answer are two events

The step that frees room accepts the offer and decides its answer. The signal carries that
answer. A withdrawal removes only what is still pending, so a missing entry alone says nothing
about the offer's outcome. -/

/-- Cancellation before acceptance. Capacity one holds `1`; an offer of `2` waits and is then
withdrawn; a take receives `1`. The message `2` never enters, and nobody is signalled. -/
def offerWithdrawnBeforeAccept : TakeReply × List Signal × List Nat :=
  let s : State := { capacity := some 1 }
  let s := (offer s 100 1).1
  let s := (offer s 101 2).1
  let s := (withdrawOffer s 101).1
  let r := take s (T 1)
  (r.2.1, r.2.2, r.1.messages)

#guard offerWithdrawnBeforeAccept = (.got [1], [], [])

/-- Cancellation after acceptance and before the answer is delivered. The take accepts `2` and
names the offerer with `true`. A withdrawal then finds no entry and changes nothing: `2` stays
accepted. -/
def offerWithdrawnAfterAccept : List Signal × List Nat × List Nat × List Signal :=
  let s : State := { capacity := some 1 }
  let s := (offer s 100 1).1
  let s := (offer s 101 2).1
  let r := take s (T 1)
  let w := withdrawOffer r.1 101
  (r.2.2, r.1.messages, w.1.messages, w.2)

#guard offerWithdrawnAfterAccept = ([⟨101, .offered true⟩], [2], [2], [])

/-- A missing entry does not mean acceptance. `shutdown` removes the pending offer and answers
`false`; nothing of it was accepted. -/
def offerRemovedByShutdown : List Signal × List Offer × List Nat :=
  let s : State := { capacity := some 1 }
  let s := (offer s 100 1).1
  let s := (offer s 101 2).1
  let d := shutdown s
  (d.2.2, d.1.offers, d.1.messages)

#guard offerRemovedByShutdown = ([⟨101, .offered false⟩], [], [])

/-- A batch: acceptance commits a prefix, and a withdrawal removes only the suffix that still
waits. Capacity two; a batch of four; one take; the batch is withdrawn. The native queue gives
the same `[2, 3]` on both builds (Codex's delivery controls). -/
def batchPrefixStays : OfferAllReply × TakeReply × List Signal × ClearReply :=
  let o := offerAll { capacity := some 2 } 100 [1, 2, 3, 4]
  let r := take o.1 (T 1)
  let w := withdrawOffer r.1 100
  (o.2.1, r.2.1, r.2.2, (clear w.1).2.1)

#guard batchPrefixStays = (.wait, .got [1], [], .got [2, 3])

/-- The same batch with no withdrawal: the second take accepts its last message and answers the
offerer. -/
def batchAnswered : List Signal × ClearReply :=
  let o := offerAll { capacity := some 2 } 100 [1, 2, 3, 4]
  let r1 := take o.1 (T 1)
  let r2 := take r1.1 (T 2)
  (r1.2.2 ++ r2.2.2, (clear r2.1).2.1)

#guard batchAnswered = ([⟨100, .left []⟩], .got [3, 4])

/-! ## Controls: what an empty answer means (row 242) -/

/-- With a taker waiting, `poll` and `clear` answer empty while a message is buffered. When the
taker leaves, `poll` receives the message. -/
def emptyAnswerNotEmptyBuffer : Option Nat × ClearReply × Nat × Option Nat :=
  let s := (take (offer {} 100 10).1 (T 1 3 5)).1
  ((poll s).2.1, (clear s).2.1, size s, (poll (withdrawTake s 1).1).2.1)

#guard emptyAnswerNotEmptyBuffer = (none, .got [], 1, some 10)

/-- A `clear` that consumes may leave messages: a pending offer refills the room it frees. -/
def clearRefills : ClearReply × List Signal × Nat :=
  let s : State := { capacity := some 1 }
  let s := (offer s 100 10).1
  let s := (offer s 101 20).1
  let c := clear s
  (c.2.1, c.2.2, size c.1)

#guard clearRefills = (.got [10], [⟨101, .offered true⟩], 1)

/-- At capacity zero `clear` and `poll` take one message of the first pending offer, and they
take nothing while a taker waits. -/
def nonblockingAtRendezvous : ClearReply × List Signal × Option Nat × ClearReply :=
  let s := (offer { capacity := some 0 } 100 10).1
  let c := clear s
  let behind := (offer (take { capacity := some 0 } (T 1)).1 100 10).1
  (c.2.1, c.2.2, (poll s).2.1, (clear behind).2.1)

#guard nonblockingAtRendezvous = (.got [10], [⟨100, .offered true⟩], some 10, .got [])

/-! ## Controls: every request that an end removes is named

The properties of the exploration below read states. They cannot see a signal that was lost
after an end emptied the waiting lists (Codex's review). These controls fix the exact signals. -/

/-- `shutdown` of an open queue names a waiting taker, a peeker and an awaiter. -/
def shutdownNamesWaiters : List Signal × Phase :=
  let s := (take {} (T 1)).1
  let s := (peek s 5).1
  let s := (awaitQ s 7).1
  let d := shutdown s
  (d.2.2, d.1.phase)

#guard shutdownNamesWaiters =
  ([⟨1, .again⟩, ⟨5, .again⟩, ⟨7, .over .interrupted⟩], .done .interrupted)

/-- `shutdown` names two takers, a single offerer, a batch offerer and an awaiter at once. The
first taker was named by the offer and did not run again yet. -/
def shutdownNamesEveryone : List Signal :=
  let s : State := { capacity := some 1 }
  let s := (take s (T 1)).1
  let s := (take s (T 2)).1
  let s := (offer s 100 10).1
  let s := (offer s 101 20).1
  let s := (offerAll s 102 [30, 40]).1
  let s := (awaitQ s 7).1
  (shutdown s).2.2

#guard shutdownNamesEveryone =
  [⟨1, .again⟩, ⟨2, .again⟩, ⟨101, .offered false⟩, ⟨102, .left [30, 40]⟩,
    ⟨7, .over .interrupted⟩]

/-- `shutdown` of a closing queue keeps that queue's end. -/
def shutdownKeepsEnd : Phase × List Signal :=
  let s := (awaitQ (offer {} 100 10).1 7).1
  let d := shutdown (close s (.failed 5)).1
  (d.1.phase, d.2.2)

#guard shutdownKeepsEnd = (.done (.failed 5), [⟨7, .over (.failed 5)⟩])

/-- The last take of a closing queue names the taker behind it and the awaiter. -/
def drainNamesEveryone : List Signal × TakeReply × List Signal × TakeReply :=
  let s := (take {} (T 1 3 5)).1
  let s := (offer s 100 10).1
  let s := (take s (T 2)).1
  let s := (awaitQ s 7).1
  let c := close s (.failed 5)
  let r := take c.1 (T 1 3 5)
  (c.2.2, r.2.1, r.2.2, (take r.1 (T 2)).2.1)

#guard drainNamesEveryone =
  ([⟨1, .again⟩], .got [10], [⟨2, .again⟩, ⟨7, .over (.failed 5)⟩], .stopped (.failed 5))

/-- A closing rendezvous queue that a withdrawal empties is done, and its taker and awaiter are
named. -/
def closingRendezvousEmptied : Phase × Phase × List Signal × TakeReply :=
  let s := (take { capacity := some 0 } (T 1)).1
  let s := (offer s 100 10).1
  let s := (awaitQ s 7).1
  let c := close s .ended
  let w := withdrawOffer c.1 100
  (c.1.phase, w.1.phase, w.2, (take w.1 (T 1)).2.1)

#guard closingRendezvousEmptied =
  (.closing .ended, .done .ended, [⟨1, .again⟩, ⟨7, .over .ended⟩], .stopped .ended)

end Test.Program.QueueContract
