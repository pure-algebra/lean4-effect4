/-!
# One wrapper for a queue and a transaction (research probe, 2026-10-05)

Not part of the tree. It imports nothing from `Effect4`. Run it from the repository root:
`lake env lean docs/research/2026-10-05-claude-lead/tx-probes/TxModel.lean`.

The question it tests: is a queue operation that waits the same thing as a transaction that
retries? The model has one wrapper, `attempt`, and no queue-specific step:

* **A body is a pure function of a snapshot.** It reads and writes cells of a store value and
  answers a value, `retry` or `fail`. Its writes reach the store only when it commits.
* **One atomic attempt.** `attempt` runs a body on the store. A success commits the writes and
  names the requests that wait on a written cell. A `retry` registers the request on the cells
  it read. The decision to wait and the registration are one step.
* **A queue is a cell and three small bodies.** `take`, `offer` and the ticket bodies below are
  programs in the same monad. Two of them compose into one atomic body with `do`.

Every `#guard` is a finite check on the named trace. A body here is any Lean function of the
snapshot; only the combinators below record what they read, so the law of the exploration needs
that premise for a body (Codex's review). The model has no fibers, no scheduler and no
interruption. It records a wake as the list of requests to signal; each signalled request
runs its body again. It proves nothing about the tree.
-/

namespace TxModel

/-- The store: each cell holds a list of numbers. A queue is one cell; a counter is one cell. -/
abbrev Store := List (List Nat)

def read (s : Store) (c : Nat) : List Nat := s.getD c []
def write (s : Store) (c : Nat) (v : List Nat) : Store := s.set c v

/-- A snapshot under one attempt, with the cells the body read and wrote so far. -/
structure Acc where
  store : Store
  reads : List Nat := []
  writes : List Nat := []

inductive Step (α : Type)
  | ok (a : α) (acc : Acc)
  | retry (acc : Acc)
  | fail

/-- A transaction body. -/
def TxM (α : Type) := Acc → Step α

instance : Monad TxM where
  pure a := fun acc => .ok a acc
  bind t f := fun acc =>
    match t acc with
    | .ok a acc' => f a acc'
    | .retry acc' => .retry acc'
    | .fail => .fail

def get (c : Nat) : TxM (List Nat) := fun acc =>
  .ok (read acc.store c) { acc with reads := c :: acc.reads }

def put (c : Nat) (v : List Nat) : TxM Unit := fun acc =>
  .ok () { acc with store := write acc.store c v, reads := c :: acc.reads, writes := c :: acc.writes }

def retry {α : Type} : TxM α := fun acc => .retry acc

/-- The left body, or the right one when the left retries. The left body's writes are dropped,
because the snapshot is a value. Its reads stay in the wait set. A failure of the left body is
not caught. This is the rule of Harris et al. and the project's selected contract (decisions
row 224). It is neither of Effect 3's forms: Codex's runs on 3.22.2 show that `STM.orElse` also
catches a failure and drops the left reads, and that `STM.orTry` keeps the left writes. Effect
4's `Effect.tx` has no such form. -/
def orElse {α : Type} (t u : TxM α) : TxM α := fun acc =>
  match t acc with
  | .retry left => u { acc with reads := left.reads }
  | r => r

/-! ## The wrapper -/

structure World where
  store : Store
  /-- Each waiting request with the cells it waits on, in registration order. -/
  waiting : List (Nat × List Nat) := []
  attempts : Nat := 0

inductive Reply (α : Type) | done (a : α) | waiting | failed
  deriving DecidableEq, Repr

/-- One atomic attempt of request `id`. The third component names the requests to signal. -/
def attempt {α : Type} (w : World) (id : Nat) (t : TxM α) : World × Reply α × List Nat :=
  let w := { w with attempts := w.attempts + 1, waiting := w.waiting.filter (·.1 != id) }
  match t { store := w.store } with
  | .ok a acc =>
    let woken := (w.waiting.filter fun p => p.2.any acc.writes.contains).map (·.1)
    ({ w with store := acc.store, waiting := w.waiting.filter fun p => !woken.contains p.1 },
      .done a, woken)
  | .retry acc => ({ w with waiting := w.waiting ++ [(id, acc.reads)] }, .waiting, [])
  | .fail => (w, .failed, [])

/-! ## A queue is a cell and small bodies -/

def take (q : Nat) : TxM Nat := do
  match (← get q) with
  | [] => retry
  | m :: ms => put q ms; pure m

/-- An offer to a queue of capacity `cap`: it waits while the queue is full. -/
def offer (q cap m : Nat) : TxM Unit := do
  let ms ← get q
  if ms.length ≥ cap then retry else put q (ms ++ [m])

/-- Two operations as one atomic body: move one message from `a` to `b`. -/
def transfer (a b cap : Nat) : TxM Nat := do
  let m ← take a
  offer b cap m
  pure m

def takeEither (a b : Nat) : TxM Nat := orElse (take a) (take b)

/-- The queue as an instance. A take waits on the empty cell; an offer commits and names the
waiting take; the take's second attempt answers the message. -/
def queueTrace : Reply Nat × List Nat × Reply Nat :=
  let r1 := attempt { store := [[]] } 1 (take 0)
  let r2 := attempt r1.1 2 (offer 0 9 10)
  let r3 := attempt r2.1 1 (take 0)
  (r1.2.1, r2.2.2, r3.2.1)

#guard queueTrace = (.waiting, [1], .done 10)

/-- Composition. `a` holds `5` and `b` is full with `8`. The transfer takes from `a`, finds `b`
full and retries: `a` keeps its message, so no part of the transfer shows. A take from `b`
names the waiting transfer, and its second attempt moves the message. -/
def transferTrace : Reply Nat × Store × List Nat × Reply Nat × Store :=
  let r1 := attempt { store := [[5], [8]] } 1 (transfer 0 1 1)
  let r2 := attempt r1.1 2 (take 1)
  let r3 := attempt r2.1 1 (transfer 0 1 1)
  (r1.2.1, r1.1.store, r2.2.2, r3.2.1, r3.1.store)

#guard transferTrace = (.waiting, [[5], [8]], [1], .done 5, [[], [5]])

/-- An alternative. With `a` empty and `b` holding `7`, the body answers `7`. With both empty
it waits on both cells, and an offer to either names it. -/
def eitherTrace : Reply Nat × List Nat × List Nat :=
  let r1 := attempt { store := [[], [7]] } 1 (takeEither 0 1)
  let r2 := attempt { store := [[], []] } 1 (takeEither 0 1)
  let waitsOn := (r2.1.waiting.map (·.2)).flatten
  let r3 := attempt r2.1 2 (offer 1 9 3)
  (r1.2.1, [0, 1].filter waitsOn.contains, r3.2.2)

#guard eitherTrace = (.done 7, [0, 1], [1])

/-! ## The turn check is state, not a new mechanism

The queue contract of the queues review keeps the takers' arrival order in the queue's cell.
Here cell `t` holds the tickets. A request first commits its ticket, then waits until its
ticket is the oldest and a message is buffered. -/

def enlist (t id : Nat) : TxM Unit := do
  put t ((← get t) ++ [id])

def serve (q t id : Nat) : TxM Nat := do
  let ts ← get t
  if ts.head? != some id then retry
  else
    match (← get q) with
    | [] => retry
    | m :: ms => put q ms; put t ts.tail; pure m

/-- P1 of the queues review, as an instance. Requests 1 and 2 hold tickets and wait. A message
arrives. A new request 3 cannot pass request 1, although a message is buffered. Request 1 then
receives it, and its commit names the two requests behind it.

The offer's wake is selective with no rule written for it. Request 2 is not the oldest, so its
body retries before it reads the buffer: it waits on the ticket cell alone, and the offer names
request 1 only. The cost shows in the first and third components: each new ticket writes the
ticket cell, so it names every request that waits there, and each runs its body again for
nothing. A queue's own step can name the one request that became ready; that is a saving the
module must prove, and the generic rule needs no proof. -/
def ticketTrace : List Nat × List Nat × List Nat × Reply Nat × Reply Nat × List Nat :=
  let w := (attempt { store := [[], []] } 1 (enlist 1 1)).1
  let w := (attempt w 1 (serve 0 1 1)).1
  let e2 := attempt w 2 (enlist 1 2)
  let w := (attempt e2.1 1 (serve 0 1 1)).1
  let w := (attempt w 2 (serve 0 1 2)).1
  let o := attempt w 9 (offer 0 9 10)
  let e3 := attempt o.1 3 (enlist 1 3)
  let w := (attempt e3.1 2 (serve 0 1 2)).1
  let r3 := attempt w 3 (serve 0 1 3)
  let r1 := attempt r3.1 1 (serve 0 1 1)
  (e2.2.2, o.2.2, e3.2.2, r3.2.1, r1.2.1, r1.2.2)

#guard ticketTrace = ([1], [1], [2], .waiting, .done 10, [2, 3])

/-! ### Tickets do not compose by themselves (Codex's review of this model)

Two findings of Codex's 22-check mirror, replayed here. Both are limits of the candidate, and
neither is a defect of code in the tree. -/

def takeBoth (qa ta qb tb id : Nat) : TxM Nat := do
  let x ← serve qa ta id
  let y ← serve qb tb id
  pure (x + y)

def wouldRetry {α : Type} (w : World) (t : TxM α) : Bool :=
  match t { store := w.store } with
  | .retry _ => true
  | _ => false

/-- The opposing-ticket cycle. Queue A (cells 0 and 1) holds `10` with tickets `[P, Q]`. Queue B
(cells 2 and 3) holds `20` with tickets `[Q, P]`. P takes from A and then from B in one body; Q
takes from B and then from A. Each finds the other first at its second queue and retries. Both
messages stay, both requests wait, and each would still retry: the wrapper's law holds and
nothing moves. So that law is no progress property, and tickets that are enrolled apart do not
compose. -/
def opposingTickets : Reply Nat × Reply Nat × Store × Bool :=
  let w : World := { store := [[10], [1, 2], [20], [2, 1]] }
  let p := attempt w 1 (takeBoth 0 1 2 3 1)
  let q := attempt p.1 2 (takeBoth 2 3 0 1 2)
  (p.2.1, q.2.1, q.1.store,
    wouldRetry q.1 (takeBoth 0 1 2 3 1) && wouldRetry q.1 (takeBoth 2 3 0 1 2))

#guard opposingTickets = (.waiting, .waiting, [[10], [1, 2], [20], [2, 1]], true)

/-- The control: both enrolments in one order on both queues. P then takes both messages. -/
def jointTickets : Reply Nat :=
  (attempt { store := [[10], [1, 2], [20], [1, 2]] } 1 (takeBoth 0 1 2 3 1)).2.1

#guard jointTickets = .done 30

def leave (t id : Nat) : TxM Unit := do
  put t ((← get t).filter (· != id))

/-- A ticket is state that the generic cleanup does not own. Request 1 holds the oldest ticket
and is cancelled. When only its registration is removed, its ticket stays and request 2 never
receives the message. When its ticket is withdrawn too, request 2 receives it. So the module
owns its enrolment and its withdrawal. -/
def abandonedTicket (withdraw : Bool) : Reply Nat :=
  let w := (attempt { store := [[], []] } 1 (enlist 1 1)).1
  let w := (attempt w 1 (serve 0 1 1)).1
  let w := (attempt w 2 (enlist 1 2)).1
  let w := (attempt w 2 (serve 0 1 2)).1
  let w : World := { w with waiting := w.waiting.filter (·.1 != 1) }
  let w := if withdraw then (attempt w 1 (leave 1 1)).1 else w
  let w := (attempt w 9 (offer 0 9 10)).1
  (attempt w 2 (serve 0 1 2)).2.1

#guard abandonedTicket false = .waiting
#guard abandonedTicket true = .done 10

/-- Without tickets, both takes read the buffer, so one message names both. The first takes
it and the second waits again: one attempt is spent for nothing, and no answer changes. -/
def broadcastTrace : List Nat × Reply Nat × Reply Nat × Nat :=
  let w := (attempt { store := [[]] } 1 (take 0)).1
  let w := (attempt w 2 (take 0)).1
  let o := attempt w 9 (offer 0 9 10)
  let r1 := attempt o.1 1 (take 0)
  let r2 := attempt r1.1 2 (take 0)
  (o.2.2, r1.2.1, r2.2.1, r2.1.attempts)

#guard broadcastTrace = ([1, 2], .done 10, .waiting, 5)

/-! ## The red control: the lost wake of rc.112's transactions

rc.112 decides to wait in one step and registers in a later one (`awaitPendingTransaction`,
`vendor/effect-4.0.0-rc.112/src/Effect.ts`). The host probe TX1 shows the result on the pin.
Here the body's decision and the registration are split by hand, with one commit between them.
The request then waits beside a buffered message, and no commit named it. -/
def lostWakeWhenSplit : Bool :=
  let w : World := { store := [[]] }
  let decidedToWait := match (take 0) { store := w.store } with | .retry _ => true | _ => false
  let o := attempt w 2 (offer 0 9 10)
  let late : World := { o.1 with waiting := o.1.waiting ++ [(1, [0])] }
  decidedToWait && o.2.2.isEmpty && read late.store 0 == [10] && late.waiting.any (·.1 == 1)

#guard lostWakeWhenSplit

/-- The same two operations through `attempt`, in both orders: the take is named or served. -/
def noLostWake : List Nat × Reply Nat :=
  let a := attempt (attempt { store := [[]] } 1 (take 0)).1 2 (offer 0 9 10)
  let b := attempt (attempt { store := [[]] } 2 (offer 0 9 10)).1 1 (take 0)
  (a.2.2, b.2.1)

#guard noLostWake = ([1], .done 10)

/-! ## No waiting request is left behind: a bounded exploration

The law of the wrapper, for every body at once: a request that waits would still retry on the
current store. A body is a function of the cells it read, and a commit names every request
that waits on a cell it wrote. Seven bodies over two queues of capacity one; every sequence of
at most six attempts. `sound := false` is the red control: a commit that names a request only
when it wrote the first cell of that request's wait set. -/

def discard {α : Type} (t : TxM α) : TxM Unit := do let _ ← t; pure ()

def bodies : List (TxM Unit) :=
  [discard (take 0), discard (take 1), discard (transfer 0 1 1), discard (takeEither 0 1),
   offer 0 1 10, offer 1 1 20, discard (transfer 1 0 1)]

def bodyOf (id : Nat) : TxM Unit := bodies.getD (id - 1) retry

def attemptWith (sound : Bool) (w : World) (id : Nat) : World :=
  let w := { w with waiting := w.waiting.filter (·.1 != id) }
  match bodyOf id { store := w.store } with
  | .ok _ acc =>
    let hit (p : Nat × List Nat) : Bool :=
      if sound then p.2.any acc.writes.contains
      else (p.2.getLast?.map acc.writes.contains).getD false
    { w with store := acc.store, waiting := w.waiting.filter fun p => !hit p }
  | .retry acc => { w with waiting := w.waiting ++ [(id, acc.reads)] }
  | .fail => w

def stillRetries (w : World) (id : Nat) : Bool :=
  match bodyOf id { store := w.store } with
  | .retry _ => true
  | _ => false

def quiet (w : World) : Bool := w.waiting.all fun p => stillRetries w p.1

/-- The count of runs explored, and whether every state on every run was quiet. -/
def explore (sound : Bool) : Nat → World → Nat × Bool
  | 0, w => (1, quiet w)
  | n + 1, w =>
    if !quiet w then (1, false)
    else (List.range bodies.length).foldl (fun acc i =>
      let r := explore sound n (attemptWith sound w (i + 1))
      (acc.1 + r.1, acc.2 && r.2)) (1, true)

#eval explore true 6 { store := [[], []] }
#guard (explore true 6 { store := [[], []] }).2
#guard !(explore false 6 { store := [[], []] }).2

end TxModel
