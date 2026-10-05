/-!
# A pure model of the queue's transition contract (research probe, 2026-10-05)

Not part of the tree. It imports nothing from `Effect4`. Run it from the repository root:
`lake env lean docs/research/2026-10-05-claude-lead/queue-probes/QueueModel.lean`.

The contract it models, after Codex's review of the queues review:

* **No reservation.** A message leaves the buffer only in the atomic step of the taker that
  receives it. A withdrawn request never held a message, so nothing is returned.
* **Turn order.** A take succeeds only when it is ready and no earlier waiting taker blocks it.
  `strict`: every earlier taker blocks. `readyFirst`: only an earlier taker that is ready blocks.
* **Offers in order.** A pending offer keeps its messages; the step that frees room accepts
  them in arrival order, as rc.112 and 4.0.1 do.
* **Eligibility** follows 4.0.1's `canTake`: the minimum is capped by the capacity, and a
  closing queue serves a shorter batch.
* **Signals.** Every transition answers the requests to signal. A signal is a hint: the
  signalled request runs its own step again.

**The admitted domain of this probe.** Bounds are natural numbers; a take with a zero bound
answers the empty batch (4.0.1, `takeBetweenUnsafe`). Capacity zero is modelled for the
`suspend` and `dropping` strategies. `sliding` at capacity zero stores one message, as 4.0.1's
`offerUnsafe` does; that boundary is pinned below and left out of the exploration. At capacity
zero an offer waits until a taker's step takes its message; Effect accepts it at once when a
taker waits.

Every `#guard` is a finite check on the named trace. The exploration at the end is bounded. It
records a signal as sent in the step that answers it. It does not model the wrapper, an
interrupt inside the wrapper, or the delivery of a `Deferred`'s resolution.
-/

namespace QueueModel

inductive Phase | opened | closing | done
  deriving DecidableEq, Repr

inductive Strategy | suspend | dropping | sliding
  deriving DecidableEq, Repr

inductive Policy | strict | readyFirst
  deriving DecidableEq, Repr

/-- A take request: its identity (its `Deferred`), and its bounds. -/
structure Taker where
  id : Nat
  min : Nat
  max : Nat
  deriving DecidableEq, Repr

/-- A pending offer: its identity and the messages not yet accepted. -/
structure Offer where
  id : Nat
  rest : List Nat
  deriving DecidableEq, Repr

structure State where
  messages : List Nat := []
  capacity : Option Nat := none
  strategy : Strategy := .suspend
  policy : Policy := .readyFirst
  takers : List Taker := []
  offers : List Offer := []
  awaiters : List Nat := []
  phase : Phase := .opened
  deriving DecidableEq, Repr

def room (s : State) : Nat :=
  match s.capacity with
  | none => 1000000
  | some c => c - s.messages.length

/-- The least buffer length that serves a take of minimum `min` (4.0.1, `canTake`). -/
def threshold (s : State) (min : Nat) : Nat :=
  if s.phase = .closing then 1
  else match s.capacity with
    | none => min
    | some 0 => Nat.min min 1
    | some c => Nat.min min c

/-- Capacity zero: a taker is served from the first pending offer. -/
def rendezvous (s : State) : Bool :=
  s.capacity == some 0 && s.phase != .done && !s.offers.isEmpty

def ready (s : State) (t : Taker) : Bool :=
  (!s.messages.isEmpty && decide (threshold s t.min ≤ s.messages.length)) || rendezvous s

/-- The takers that wait before request `id`: every taker when `id` does not wait yet. -/
def earlier (s : State) (id : Nat) : List Taker :=
  s.takers.takeWhile (fun t => t.id != id)

def turn (s : State) (id : Nat) : Bool :=
  match s.policy with
  | .strict => (earlier s id).isEmpty
  | .readyFirst => !(earlier s id).any (ready s)

/-- The request to signal: the first taker that is ready and has the turn. -/
def wake (s : State) : List Nat :=
  match s.policy with
  | .strict =>
    match s.takers with
    | t :: _ => if ready s t then [t.id] else []
    | [] => []
  | .readyFirst =>
    match s.takers.find? (ready s) with
    | some t => [t.id]
    | none => []

/-- Pending offers enter the buffer in order while room remains. The third component names
the offerers whose whole offer was accepted. -/
def acceptLoop : Nat → List Nat → List Offer → List Nat × List Offer × List Nat
  | _, msgs, [] => (msgs, [], [])
  | room, msgs, o :: rest =>
    if room = 0 then (msgs, o :: rest, [])
    else
      let k := Nat.min room o.rest.length
      let msgs' := msgs ++ o.rest.take k
      let left := o.rest.drop k
      if left.isEmpty then
        let r := acceptLoop (room - k) msgs' rest
        (r.1, r.2.1, o.id :: r.2.2)
      else (msgs', { o with rest := left } :: rest, [])

def accept (s : State) : State × List Nat :=
  let r := acceptLoop (room s) s.messages s.offers
  ({ s with messages := r.1, offers := r.2.1 }, r.2.2)

/-- A closing queue with nothing left is done. Every waiter is signalled and leaves. -/
def settle (s : State) : State × List Nat :=
  if s.phase = .closing && s.messages.isEmpty && s.offers.isEmpty then
    ({ s with phase := .done, takers := [], awaiters := [] }, s.takers.map (·.id) ++ s.awaiters)
  else (s, [])

def removeTaker (s : State) (id : Nat) : State :=
  { s with takers := s.takers.filter (fun t => t.id != id) }

inductive TakeReply | got (ms : List Nat) | wait | ended
  deriving DecidableEq, Repr

/-- The messages a served take receives, the state after, and the offerer to signal. -/
def pull (s : State) (max : Nat) : List Nat × State × List Nat :=
  if s.messages.isEmpty then
    match s.offers with
    | o :: rest =>
      match o.rest with
      | m :: more =>
        if more.isEmpty then ([m], { s with offers := rest }, [o.id])
        else ([m], { s with offers := { o with rest := more } :: rest }, [])
      | [] => ([], { s with offers := rest }, [o.id])
    | [] => ([], s, [])
  else (s.messages.take max, { s with messages := s.messages.drop max }, [])

/-- One atomic step of a take. Consumption commits here and nowhere else. -/
def take (s : State) (t : Taker) : State × TakeReply × List Nat :=
  if s.phase = .done then (removeTaker s t.id, .ended, [])
  else if t.min = 0 || t.max = 0 then (s, .got [], [])
  else if ready s t && turn s t.id then
    let p := pull (removeTaker s t.id) t.max
    let a := accept p.2.1
    let d := settle a.1
    (d.1, .got p.1, p.2.2 ++ a.2 ++ d.2 ++ wake d.1)
  else if s.takers.any (fun u => u.id == t.id) then (s, .wait, [])
  else ({ s with takers := s.takers ++ [t] }, .wait, [])

inductive OfferReply | accepted (ok : Bool) | wait
  deriving DecidableEq, Repr

def offer (s : State) (id a : Nat) : State × OfferReply × List Nat :=
  if s.phase != .opened then (s, .accepted false, [])
  else if !s.offers.isEmpty then
    match s.strategy with
    | .suspend => ({ s with offers := s.offers ++ [⟨id, [a]⟩] }, .wait, [])
    | _ => (s, .accepted false, [])
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
      let s1 := { s with offers := s.offers ++ [⟨id, [a]⟩] }
      (s1, .wait, wake s1)

def cancelTake (s : State) (id : Nat) : State × List Nat :=
  let s1 := removeTaker s id
  (s1, wake s1)

def cancelOffer (s : State) (id : Nat) : State × List Nat :=
  if s.phase = .done then (s, [])
  else
    let d := settle { s with offers := s.offers.filter (fun o => o.id != id) }
    (d.1, d.2 ++ wake d.1)

def endQ (s : State) : State × Bool × List Nat :=
  if s.phase != .opened then (s, false, [])
  else
    let d := settle { s with phase := .closing }
    (d.1, true, d.2 ++ wake d.1)

def shutdown (s : State) : State × Bool × List Nat :=
  if s.phase = .done then (s, false, [])
  else
    ({ s with messages := [], offers := [], takers := [], awaiters := [], phase := .done }, true,
      s.takers.map (·.id) ++ s.offers.map (·.id) ++ s.awaiters)

/-- Whether a request that never registers may be served now. `strict`: no taker waits.
`readyFirst`: no waiting taker is ready. -/
def passes (s : State) : Bool :=
  match s.policy with
  | .strict => s.takers.isEmpty
  | .readyFirst => !s.takers.any (ready s)

/-- A take of one message that never waits and never registers. -/
def poll (s : State) : State × Option Nat × List Nat :=
  if s.phase = .done || !(ready s ⟨0, 1, 1⟩) || !(passes s) then (s, none, [])
  else
    let p := pull s 1
    let a := accept p.2.1
    let d := settle a.1
    (d.1, p.1.head?, p.2.2 ++ a.2 ++ d.2 ++ wake d.1)

def T (id : Nat) (min : Nat := 1) (max : Nat := 1) : Taker := ⟨id, min, max⟩

/-! ## Codex's countermodels, as controls on this contract -/

/-- Order under cancellation. T1 and T2 wait; `10` and `20` arrive; T1 is withdrawn; T2 then
T3 take. The earlier draft answered `20` before `10`. -/
def orderTrace : List TakeReply :=
  let s := (take {} (T 1)).1
  let s := (take s (T 2)).1
  let s := (offer s 100 10).1
  let s := (offer s 101 20).1
  let s := (cancelTake s 1).1
  let r2 := take s (T 2)
  let r3 := take r2.1 (T 3)
  [r2.2.1, r3.2.1]

#guard orderTrace = [.got [10], .got [20]]

/-- Capacity one. T1 waits; `10` is buffered; `20` must wait; T1 is withdrawn. The earlier
draft held two free messages. -/
def capacityOne : Nat × Nat :=
  let s := (take { capacity := some 1 } (T 1)).1
  let s := (offer s 100 10).1
  let s := (offer s 101 20).1
  let s := (cancelTake s 1).1
  (s.messages.length, s.offers.length)

#guard capacityOne = (1, 1)

/-- Capacity zero. T1 waits; an offer of `10` stays pending and T1 is signalled; T1 is
withdrawn. Nothing is buffered, and the offer is still pending. -/
def capacityZero : List Nat × Nat × Nat :=
  let s := (take { capacity := some 0 } (T 1)).1
  let o := offer s 100 10
  let s := (cancelTake o.1 1).1
  (o.2.2, s.messages.length, s.offers.length)

#guard capacityZero = ([1], 0, 1)

/-- Capacity zero, served: the taker receives the pending offer's message, and the offerer is
signalled. -/
def capacityZeroServed : TakeReply × List Nat :=
  let s := (take { capacity := some 0 } (T 1)).1
  let s := (offer s 100 10).1
  let r := take s (T 1)
  (r.2.1, r.2.2)

#guard capacityZeroServed = (.got [10], [100])

/-- A terminal phase. One message is buffered; T1 needs two and waits; the queue ends. T1 is
signalled and receives the short batch; the queue is then done. -/
def endServes : List Nat × TakeReply × Phase :=
  let s := (offer {} 100 10).1
  let s := (take s (T 1 2 3)).1
  let e := endQ s
  let r := take e.1 (T 1 2 3)
  (e.2.2, r.2.1, r.1.phase)

#guard endServes = ([1], .got [10], .done)

/-- The same, with T1 withdrawn after the end. The queue stays closing with its message; no
awaiter is signalled; a later take drains it and the queue is done. -/
def endThenCancel : Phase × List Nat × TakeReply × Phase × List Nat :=
  let s := (offer {} 100 10).1
  let s := (take s (T 1 2 3)).1
  let s := { s with awaiters := [900] }
  let s := (endQ s).1
  let c := cancelTake s 1
  let r := take c.1 (T 3)
  (c.1.phase, c.2, r.2.1, r.1.phase, r.2.2)

#guard endThenCancel = (.closing, [], .got [10], .done, [900])

/-- A batch at the head. One message, and the oldest taker needs three: nobody is signalled.
Under `strict` a later single take waits; under `readyFirst` it is served. -/
def batchHead (p : Policy) : List Nat × TakeReply :=
  let s := (offer { policy := p } 100 10).1
  let s := (take s (T 1 3 5)).1
  let r := take s (T 2)
  (wake s, r.2.1)

#guard batchHead .strict = ([], .wait)
#guard batchHead .readyFirst = ([], .got [10])

/-- Zero bounds (4.0.1, `takeBetweenUnsafe`): the empty batch at once, and no registration.
At capacity zero a pending offer stays pending. -/
def zeroBounds : TakeReply × Nat × TakeReply × Nat :=
  let r1 := take {} (T 1 0 5)
  let s := (offer { capacity := some 0 } 100 10).1
  let r2 := take s (T 2 1 0)
  (r1.2.1, r1.1.takers.length, r2.2.1, r2.1.offers.length)

#guard zeroBounds = (.got [], 0, .got [], 1)

/-- Codex's timing trace. T1 needs two messages and T2 needs one. `10` arrives and T2 is
signalled. `early := true`: T2 runs its step before `20` arrives. `early := false`: `20`
arrives first. No request is withdrawn. Under `readyFirst` the answers differ. Under `strict`
they agree on this one trace of exact-size batches; `batchTiming` and `scalarTiming` below show
that `strict` gives no such law in general. -/
def timing (p : Policy) (early : Bool) : TakeReply × TakeReply :=
  let t1 := T 1 2 2
  let s := (take { policy := p } t1).1
  let s := (take s (T 2)).1
  let s := (offer s 100 10).1
  if early then
    let r2 := take s (T 2)
    let s := (offer r2.1 101 20).1
    ((take s t1).2.1, r2.2.1)
  else
    let s := (offer s 101 20).1
    let r2 := take s (T 2)
    ((take r2.1 t1).2.1, r2.2.1)

#guard timing .readyFirst true = (.wait, .got [10])
#guard timing .readyFirst false = (.got [10, 20], .wait)
#guard timing .strict true = (.got [10, 20], .wait)
#guard timing .strict false = (.got [10, 20], .wait)

/-! ### The time of a retry, under either turn policy

Codex's third review. A turn policy fixes which request may consume at its step. It does not fix
what that step returns. `early := true`: the signalled request runs its step before the second
offer. `early := false`: the second offer comes first. No request is withdrawn in any of them.
The host probe `queue-timing.ts` (P5, P6, P7) measures the same three traces: Effect 3.22.2
answers as `early` whether or not the offering fiber yields between its offers, and rc.112,
4.0.0 and 4.0.1 answer as `late` when it does not yield. -/

/-- One taker waits for one to two messages. `10` arrives, then `20`. -/
def batchTiming (p : Policy) (early : Bool) : TakeReply :=
  let t := T 1 1 2
  let s := (take { policy := p } t).1
  let s := (offer s 100 10).1
  if early then (take s t).2.1 else (take (offer s 101 20).1 t).2.1

#guard batchTiming .strict true = .got [10]
#guard batchTiming .strict false = .got [10, 20]
#guard batchTiming .readyFirst true = .got [10]
#guard batchTiming .readyFirst false = .got [10, 20]

/-- One taker waits for one message at capacity one. Under `sliding` the second offer discards
`10`, so a late retry returns `20`. Under `suspend` both retries return `10`: the positive
control. -/
def scalarTiming (st : Strategy) (early : Bool) : TakeReply :=
  let t := T 1
  let s := (take { capacity := some 1, strategy := st, policy := .strict } t).1
  let s := (offer s 100 10).1
  if early then (take s t).2.1 else (take (offer s 101 20).1 t).2.1

#guard scalarTiming .sliding true = .got [10]
#guard scalarTiming .sliding false = .got [20]
#guard scalarTiming .suspend true = .got [10]
#guard scalarTiming .suspend false = .got [10]

/-- The same under `dropping`. The take returns `10` either way; the second offer's own answer
changes: accepted after an early retry, refused before a late one. -/
def droppingTiming (early : Bool) : TakeReply × OfferReply :=
  let t := T 1
  let s := (take { capacity := some 1, strategy := .dropping, policy := .strict } t).1
  let s := (offer s 100 10).1
  if early then
    let r := take s t
    (r.2.1, (offer r.1 101 20).2.1)
  else
    let o := offer s 101 20
    ((take o.1 t).2.1, o.2.1)

#guard droppingTiming true = (.got [10], .accepted true)
#guard droppingTiming false = (.got [10], .accepted false)

/-- What the turn policy does decide. T1 needs two messages and waits first. Three times, one
message arrives, T1 runs its step if it still waits, and a new take of one message follows.
Under `readyFirst` each single take is served and T1 still waits after three messages. Under
`strict` T1 is served at the second message and the single takes wait their turn. A finite
run: it is no liveness theorem. -/
def batchBehindSingles (p : Policy) : TakeReply × List TakeReply :=
  let t1 := T 1 2 2
  let init : State × TakeReply × List TakeReply := ((take { policy := p } t1).1, .wait, [])
  let out := [1, 2, 3].foldl (fun (acc : State × TakeReply × List TakeReply) k =>
    let s := (offer acc.1 (100 + k) (10 * k)).1
    let r1 := if acc.2.1 = .wait then take s t1 else (s, acc.2.1, [])
    let r2 := take r1.1 (T (k + 1))
    (r2.1, r1.2.1, acc.2.2 ++ [r2.2.1])) init
  (out.2.1, out.2.2)

#guard batchBehindSingles .readyFirst = (.wait, [.got [10], .got [20], .got [30]])
#guard batchBehindSingles .strict = (.got [10, 20], [.wait, .wait, .wait])

/-- `poll` under each policy, with one message buffered and a batch of three at the head. -/
def pollAtBatchHead (p : Policy) : Option Nat :=
  let s := (offer { policy := p } 100 10).1
  let s := (take s (T 1 3 5)).1
  (poll s).2.1

#guard pollAtBatchHead .strict = none
#guard pollAtBatchHead .readyFirst = some 10

/-! ## The probes of the queues review, on this contract -/

/-- P1. A waits first; a message arrives; a new taker B does not pass A. -/
def noBypass (p : Policy) : TakeReply × TakeReply :=
  let s := (take { policy := p } (T 1)).1
  let s := (offer s 100 10).1
  let b := take s (T 2)
  let a := take b.1 (T 1)
  (b.2.1, a.2.1)

#guard noBypass .strict = (.wait, .got [10])
#guard noBypass .readyFirst = (.wait, .got [10])

/-- P2. A take of three to five waits until three messages are buffered. -/
def keepsMinimum : List TakeReply :=
  let t := T 1 3 5
  let s := (take {} t).1
  let s := (offer s 100 1).1
  let r1 := take s t
  let s := (offer r1.1 101 2).1
  let r2 := take s t
  let s := (offer r2.1 102 3).1
  let r3 := take s t
  [r1.2.1, r2.2.1, r3.2.1]

#guard keepsMinimum = [.wait, .wait, .got [1, 2, 3]]

/-- P4. A full queue; an offer of `20` waits; the queue ends; the offer is withdrawn. The
queue drains to done and `20` is never delivered. -/
def withdrawnOffer : List TakeReply × Phase :=
  let s := (offer { capacity := some 1 } 100 10).1
  let s := (offer s 101 20).1
  let s := (endQ s).1
  let s := (cancelOffer s 101).1
  let r1 := take s (T 1)
  let r2 := take r1.1 (T 2)
  ([r1.2.1, r2.2.1], r1.1.phase)

#guard withdrawnOffer = ([.got [10], .ended], .done)

/-- Codex's contender. Capacity one holds `10`; B waits with `20`; a take frees room; C then
offers `30`. The next take receives `20`. -/
def offersInOrder : List TakeReply × OfferReply :=
  let s := (offer { capacity := some 1 } 100 10).1
  let s := (offer s 101 20).1
  let r1 := take s (T 1)
  let c := offer r1.1 102 30
  let r2 := take c.1 (T 2)
  ([r1.2.1, r2.2.1], c.2.1)

#guard offersInOrder = ([.got [10], .got [20]], .wait)

#guard (offer (offer { capacity := some 1, strategy := .dropping } 100 10).1 101 20).2.1
  = .accepted false
#guard (offer (offer { capacity := some 1, strategy := .sliding } 100 10).1 101 20).1.messages
  = [20]

/-! ## A bounded exploration

Every sequence of at most `depth` operations from the empty queue. After each operation two
properties are checked:

* **capacity**: a bounded queue never buffers more than its capacity;
* **no lost signal**: a taker that is ready and has the turn was signalled, and has not run
  its step since.

The second is the model's form of "no eligible request waits unsignalled". -/

inductive Op
  | offer | takeNew | takeBatch | retry (i : Nat) | cancel (i : Nat) | cancelOffer (i : Nat)
  | endQ | poll
  deriving DecidableEq, Repr

structure Run where
  state : State
  /-- The takers signalled since their last step. -/
  signalled : List Nat := []
  next : Nat := 1
  ok : Bool := true
  deriving Repr

def note (s : State) (signalled signals : List Nat) : List Nat :=
  (signalled ++ signals).filter fun id => s.takers.any (fun t => t.id == id)

def within (s : State) : Bool :=
  match s.capacity with
  | none => true
  | some c => decide (s.messages.length ≤ c)

def check (r : Run) : Run :=
  { r with ok := r.ok && within r.state && (wake r.state).all (r.signalled.contains ·) }

/-- One operation. `forward := false` is the red control: a withdrawal that signals nobody. -/
def step (forward : Bool) (r : Run) : Op → Run
  | .offer =>
    let o := offer r.state (1000 + r.next) r.next
    check { r with state := o.1, signalled := note o.1 r.signalled o.2.2, next := r.next + 1 }
  | .takeNew =>
    let o := take r.state (T r.next)
    check { r with state := o.1, signalled := note o.1 r.signalled o.2.2, next := r.next + 1 }
  | .takeBatch =>
    let o := take r.state (T r.next 2 3)
    check { r with state := o.1, signalled := note o.1 r.signalled o.2.2, next := r.next + 1 }
  | .retry i =>
    match r.state.takers[i]? with
    | some t =>
      let o := take r.state t
      -- the request ran its step: its old signal is spent
      check { r with state := o.1, signalled := note o.1 (r.signalled.erase t.id) o.2.2 }
    | none => r
  | .cancel i =>
    match r.state.takers[i]? with
    | some t =>
      let o := cancelTake r.state t.id
      check { r with state := o.1, signalled := note o.1 r.signalled (if forward then o.2 else []) }
    | none => r
  | .cancelOffer i =>
    match r.state.offers[i]? with
    | some f =>
      let o := cancelOffer r.state f.id
      check { r with state := o.1, signalled := note o.1 r.signalled o.2 }
    | none => r
  | .endQ =>
    let o := endQ r.state
    check { r with state := o.1, signalled := note o.1 r.signalled o.2.2 }
  | .poll =>
    let o := poll r.state
    check { r with state := o.1, signalled := note o.1 r.signalled o.2.2 }

def ops : List Op :=
  [.offer, .takeNew, .takeBatch, .retry 0, .retry 1, .cancel 0, .cancel 1, .cancelOffer 0,
    .endQ, .poll]

/-- The count of runs explored, and whether every one kept both properties. -/
def explore (forward : Bool) : Nat → Run → Nat × Bool
  | 0, r => (1, r.ok)
  | depth + 1, r =>
    ops.foldl (fun acc op =>
      let x := explore forward depth (step forward r op)
      (acc.1 + x.1, acc.2 && x.2)) (1, r.ok)

def exploreAt (capacity : Option Nat) (policy : Policy) (depth : Nat)
    (forward : Bool := true) (strategy : Strategy := .suspend) : Nat × Bool :=
  explore forward depth
    { state := { capacity := capacity, policy := policy, strategy := strategy } }

#eval [exploreAt none .strict 5, exploreAt none .readyFirst 5,
  exploreAt (some 0) .strict 5, exploreAt (some 0) .readyFirst 5,
  exploreAt (some 1) .strict 5, exploreAt (some 1) .readyFirst 5,
  exploreAt (some 2) .strict 5, exploreAt (some 2) .readyFirst 5]

#guard (exploreAt none .strict 5).2 && (exploreAt none .readyFirst 5).2
#guard (exploreAt (some 0) .strict 5).2 && (exploreAt (some 0) .readyFirst 5).2
#guard (exploreAt (some 1) .strict 5).2 && (exploreAt (some 1) .readyFirst 5).2
#guard (exploreAt (some 2) .strict 5).2 && (exploreAt (some 2) .readyFirst 5).2

/-! The eight runs above use the `suspend` strategy. The same exploration for `dropping` at
four capacities, and for `sliding` at the three capacities this probe admits. -/

#guard [none, some 0, some 1, some 2].all fun c =>
  (exploreAt c .strict 5 (strategy := .dropping)).2 &&
    (exploreAt c .readyFirst 5 (strategy := .dropping)).2

#guard [none, some 1, some 2].all fun c =>
  (exploreAt c .strict 5 (strategy := .sliding)).2 &&
    (exploreAt c .readyFirst 5 (strategy := .sliding)).2

/-- The pinned boundary: `sliding` at capacity zero stores one message (4.0.1, `offerUnsafe`).
The contract must refuse this configuration or define it. -/
def slidingZero : List Nat :=
  (offer { capacity := some 0, strategy := .sliding } 100 10).1.messages

#guard slidingZero = [10]

/-- The red control: when a withdrawal forwards no signal, the exploration finds a ready taker
that nobody signalled. -/
def lostSignal : Bool := !(exploreAt none .strict 5 (forward := false)).2

#guard lostSignal

end QueueModel
