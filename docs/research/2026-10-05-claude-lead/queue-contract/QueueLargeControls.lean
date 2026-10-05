import Test.Program.QueueModel

/-!
Retained large controls and the bounded exploration of the Queue's abstract model. No default
import reaches this file. Run it by hand:

    lake env lean docs/research/2026-10-05-claude-lead/queue-contract/QueueLargeControls.lean

Its bodies are the research model's, byte for byte (`QueueContract.lean` beside this file).
-/

namespace QueueContract
/-! ## Controls: an unbounded queue has no limit

Codex's review of 2026-10-05 found that an earlier version of this model used one million as
the room of an unbounded queue. These are its two witnesses, now as regressions. -/

/-- From an empty unbounded queue, a batch of 1,000,001 messages is accepted whole. -/
def unboundedBatch : OfferAllReply × Nat × Nat :=
  let o := offerAll {} 100 (List.range 1000001)
  (o.2.1, o.1.messages.length, o.1.offers.length)

#guard unboundedBatch = (.left [], 1000001, 0)

/-- A million messages, then one more offer, then a `clear`: it returns all of them. -/
def unboundedClear : Nat × Nat :=
  let s := (offerAll {} 100 (List.range 1000000)).1
  let s := (offer s 101 1000000).1
  let c := clear s
  (match c.2.1 with | .got ms => ms.length | .stopped _ => 0, c.1.messages.length)

#guard unboundedClear = (1000001, 0)

/-! ## A bounded exploration

Every sequence of at most five operations from a list, on each formed configuration. The first
list has eleven operations. The second list has thirteen: it adds `await`, the withdrawals of a
peek and of an await, and an end by failure, and it leaves out `poll` and `clear`. It withdraws
the single offer, where the first list withdraws the batch. The identities, the values and the
bounds are fixed in both lists.

Three properties of the state hold after each step:

* `within`: a bounded queue never exceeds its capacity;
* `tidy`: a done queue holds nothing and nobody; a closing queue holds something; a pending
  offer means no room;
* `quiet`: the oldest taker, when it is ready, was signalled; each peeker, when a message is in
  front, was signalled.

One property of the step holds:

* `accounted`: every request that the step removes is named in the step's signals, unless it
  is the step's own request.

Two red controls. `Fault.closing`: a queue that starts closing names nobody, as rc.112 did
(P3); `quiet` fails. `Fault.shutdown`: a shutdown names nobody; the three properties of the
state still hold, and only `accounted` fails. -/

def ops : List Op :=
  [.take 1 1 1, .take 2 2 3, .poll, .peek 5, .offer 100 10, .offerAll 101 [20, 30], .clear,
   .close .ended, .shutdown, .dropTake 1, .dropOffer 101]

def endOps : List Op :=
  [.take 1 1 1, .take 2 2 3, .peek 5, .await 7, .offer 100 10, .offerAll 101 [20, 30],
   .close .ended, .close (.failed 5), .shutdown, .dropTake 1, .dropOffer 100, .dropPeek 5,
   .dropAwait 7]

/-- The count of runs explored, whether every one kept the three properties of the state, and
whether every step named the requests that it removed. -/
def explore (ops : List Op) (fault : Fault) : Nat → Run → Nat × Bool × Bool
  | 0, r => (1, r.ok, r.named)
  | n + 1, r =>
    if !r.ok then (1, false, r.named)
    else ops.foldl (fun acc op =>
      let x := explore ops fault n (step fault r op)
      (acc.1 + x.1, acc.2.1 && x.2.1, acc.2.2 && x.2.2)) (1, true, r.named)

def exploreAt (ops : List Op) (strategy : Strategy) (capacity : Option Nat) (depth : Nat)
    (fault : Fault := .none) : Nat × Bool × Bool :=
  explore ops fault depth { s := { strategy := strategy, capacity := capacity } }

def holds (x : Nat × Bool × Bool) : Bool := x.2.1 && x.2.2

#eval [none, some 0, some 1, some 2].map (exploreAt ops .suspend · 5)
#eval [some 1, some 2].map (exploreAt ops .dropping · 5)
#eval [some 1, some 2].map (exploreAt ops .sliding · 5)
#eval [none, some 0, some 1, some 2].map (exploreAt endOps .suspend · 5)
#eval [some 1, some 2].map (exploreAt endOps .dropping · 5)
#eval [some 1, some 2].map (exploreAt endOps .sliding · 5)

#guard [none, some 0, some 1, some 2].all fun c => holds (exploreAt ops .suspend c 5)
#guard [some 1, some 2].all fun c => holds (exploreAt ops .dropping c 5)
#guard [some 1, some 2].all fun c => holds (exploreAt ops .sliding c 5)
#guard [none, some 0, some 1, some 2].all fun c => holds (exploreAt endOps .suspend c 5)
#guard [some 1, some 2].all fun c => holds (exploreAt endOps .dropping c 5)
#guard [some 1, some 2].all fun c => holds (exploreAt endOps .sliding c 5)

/-- The first red control: when a closing queue names nobody, the exploration finds a ready
taker that no signal named. -/
def closingNamesNobody : Bool := !(exploreAt ops .suspend none 5 (fault := .closing)).2.1

#guard closingNamesNobody

/-- The second red control: when a shutdown names nobody, the three properties of the state
still hold on every run, and the property of the step fails. -/
def shutdownNamesNobody : Bool × Bool :=
  let x := exploreAt endOps .suspend none 5 (fault := .shutdown)
  (x.2.1, x.2.2)

#guard shutdownNamesNobody = (true, false)

end QueueContract
