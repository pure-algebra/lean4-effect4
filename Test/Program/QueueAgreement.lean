import Effect4.Modules.Queue.Steps
import Effect4.Laws.Modules.Queue.Profile

/-!
# The Queue's steps against the abstract model: the comparison (decisions row 255)

A comparison evaluates one step term of `src/Effect4/Modules/Queue/Steps.lean` on the encoding
of a model state, and compares the whole result with the encoding of the model's step
(`src/Effect4/Laws/Modules/Queue/Model.lean`): the reply, the stored value and the ordered
notifications. It is the probe's comparison
(`docs/research/2026-10-05-claude-lead/queue-readiness/QueueSteps.lean`, "The steps against the
model"), over the library's steps at number messages.

The battery holds:

- the named controls C1 to C6, on the contract's traces of the first profile;
- the refusals P1 to P3: a state outside the profile, a signal with no encoding, and a request
  that breaks a step's premise;
- the red controls M1 to M4: one notification changed and nothing else, and a defective step
  compared on every state;
- every state of a finite universe of the profile, 200 states, with twelve moves on each.

Placement. Each comparison is a finite instance of a step goal of the Queue's refinement
(concept `translation-simulation`, requirement R10, a part of the proposed claim
`queue-expansion-agrees`). Every guard is a finite check. A state outside the universe is not
checked. No guard states delivery, a cancellation law or liveness.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Test.Program.QueueAgreement

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Queue.Model (FirstProfile)

/-! ## The first profile's states

A step goal quantifies over the states of the first profile, and over no other. The predicate
is `FirstProfile`, and it is closed (`first_profile_closed`). A comparison decides it.
`profileFaults` says in words what a state breaks, and agrees with the predicate on every state
that a comparison meets (`faultsAgree`). The model's `within` and `tidy` are no part of it. -/

def distinct : List Nat → Bool
  | [] => true
  | x :: xs => !xs.contains x && distinct xs

/-- What puts a model state outside the first profile, each fault in words. Empty for a state
of the profile. -/
def profileFaults (s : Queue.Model.State) : List String :=
  (if s.phase == .opened then [] else ["the queue is not opened"]) ++
  (if s.strategy == .suspend then [] else ["the strategy is not suspend"]) ++
  (match s.capacity with
    | some (_ + 1) => []
    | _ => ["the capacity is no positive number"]) ++
  (if s.takers.all (fun t => t.min == 1 && t.max == 1) then []
    else ["a stored taker's bounds are not one and one"]) ++
  (if s.offers.all (fun o => !o.batch && o.rest.length == 1) then []
    else ["a pending offer is a batch, or holds no single message"]) ++
  (if s.peekers.isEmpty then [] else ["a peeker waits"]) ++
  (if s.awaiters.isEmpty then [] else ["an awaiter waits"]) ++
  (if distinct (Queue.Model.waiting s) then [] else ["two waiting requests share an identity"])

/-- The predicate of the tree, decided. -/
def firstProfile (s : Queue.Model.State) : Bool := decide (FirstProfile s)

/-- The words agree with the predicate on a state. -/
def faultsAgree (s : Queue.Model.State) : Bool := (profileFaults s).isEmpty == firstProfile s

/-! ## The encoding

Model request `n` has the identity handle `i<n>` and a current hint `h<n>`. A step that enrols
a taker, or renews its hint, changes that request's entry of the table and no other. -/

def ids : List Nat := [1, 2, 3, 100, 101, 102]
def idName (n : Nat) : String := s!"i{n}"
def hintName (n : Nat) : String := s!"h{n}"
def envNames : List String := ids.flatMap (fun n => [idName n, hintName n]) ++ ["fresh"]
def envVals : List Val :=
  ids.flatMap (fun n => [Val.promise ⟨n⟩, Val.promise ⟨1000 + n⟩]) ++ [Val.promise ⟨9999⟩]

/-- A term's value in the scope of the handles. -/
def evalAt (src : TermSrc) : Option Val :=
  (src { names := envNames } []).toOption.bind (evalTerm envVals ·)

def natList (xs : List Nat) : TermSrc :=
  xs.foldr (fun x acc => app "cons" [nat x, acc]) Queue.nilT
def listOf (xs : List TermSrc) : TermSrc :=
  xs.foldr (fun x acc => app "cons" [x, acc]) Queue.nilT

/-- The table: a request's current hint. -/
abbrev Table := Nat → TermSrc
def table0 : Table := fun n => var (hintName n)
def Table.set (tb : Table) (id : Nat) (hint : TermSrc) : Table :=
  fun n => if n = id then hint else tb n

def takerTerm (tb : Table) (t : Queue.Model.Taker) : TermSrc :=
  Queue.mkTaker (var (idName t.id)) (tb t.id)
def offerTerm (o : Queue.Model.Offer) : TermSrc :=
  Queue.mkOffer .nat (var (idName o.id)) (var (hintName o.id)) (bool o.batch) (natList o.rest)

/-- The cell's value for a model state. On the first profile it loses nothing: a stored taker's
bounds, the strategy, the phase and the two empty lists are fixed there. -/
def stateTerm (tb : Table) (s : Queue.Model.State) : TermSrc :=
  record (Queue.cellFields .nat) [("msgs", natList s.messages),
    ("cap", nat (s.capacity.getD 0)),
    ("takers", listOf (s.takers.map (takerTerm tb))),
    ("offers", listOf (s.offers.map offerTerm))]

/-! ## The comparison

A comparison has five verdicts. It refuses a state outside the profile, before and after the
step, and a request that breaks the step's premise. It refuses a reply or a signal that a
first-profile step cannot answer, and drops none. So `agrees` accounts for every signal of the
model, in order. -/

inductive Verdict
  /-- The term's whole result is the encoding of the model's. -/
  | agrees
  | differs
  /-- A term has no value. -/
  | stuck (which : String)
  /-- The model answers what a first-profile step cannot. -/
  | unencoded (why : String)
  /-- The state, the request or the next state is outside the profile. -/
  | outside (faults : List String)
  deriving DecidableEq

/-- The model's signals as a first-profile step answers them: the accepted offers' answers, then
the takers to wake. It refuses a signal that such a step cannot answer: an answer other than
`offered true`, an identity that names no stored request of its kind, any other note, and an
answer behind a wake. -/
def notifications (before after : Queue.Model.State) (tb : Table)
    (signals : List Queue.Model.Signal) : Except String (List TermSrc × List TermSrc) := do
  let isAnswer := fun (g : Queue.Model.Signal) => g.note == Queue.Model.Note.offered true
  let accepted ← (signals.takeWhile isAnswer).mapM fun g =>
    match before.offers.find? (·.id == g.id) with
    | some o => pure (offerTerm o)
    | none => throw s!"the answer for request {g.id} names no pending offer"
  let woken ← (signals.dropWhile isAnswer).mapM fun g =>
    match g.note, after.takers.find? (·.id == g.id) with
    | .again, some t => pure (takerTerm tb t)
    | .again, none => throw s!"the wake of request {g.id} names no stored taker"
    | _, _ => throw s!"the signal for request {g.id} is no accepted answer and no wake"
  pure (accepted, woken)

/-- One comparison, with no premise: the step term's whole result against the encoding of the
model's. -/
def judge (step : TermSrc) (expected : Except String TermSrc) : Verdict :=
  match expected with
  | .error why => .unencoded why
  | .ok e =>
    match evalAt step, evalAt e with
    | some got, some want => if got = want then .agrees else .differs
    | none, _ => .stuck "the step term"
    | _, none => .stuck "the expected term"

/-- A comparison under its premises: the state before the step and the state after it are of
the first profile, and the request keeps the step's premise. -/
def guarded (before after : Queue.Model.State) (request : List String) (raw : Verdict) :
    Verdict :=
  if firstProfile before && request.isEmpty && firstProfile after then raw
  else .outside (profileFaults before ++ request ++
    (profileFaults after).map ("after the step, " ++ ·))

/-- A take's request is fresh, or it is its own waiting taker. -/
def foreign (s : Queue.Model.State) (id : Nat) : List String :=
  if (s.offers.map (·.id) ++ s.peekers ++ s.awaiters).contains id
  then ["the request's identity names a waiting request of another kind"] else []

/-- An offer's request is fresh. -/
def notFresh (s : Queue.Model.State) (id : Nat) : List String :=
  if (Queue.Model.waiting s).contains id then ["the request's identity is not fresh"] else []

/-- A deliberate defect of an expected result, for a red control. The reply and the stored
value stay as they are. -/
inductive Mutation
  | exact
  /-- The two notification lists change places. -/
  | swapNotifications
  /-- The takers to wake are left out. -/
  | dropWake

/-- A take of request `id` with the hint `fresh`, on the encoding of `s`: the encoding of the
model's result, the accepted offers before the takers. -/
def takeExpected (mutation : Mutation) (s : Queue.Model.State) (id : Nat) :
    Except String TermSrc := do
  let r := Queue.Model.take s ⟨id, 1, 1⟩
  let (reply, tb) ← (match r.2.1 with
    | .got [m] => pure (app "some" [nat m], table0)
    | .wait => pure (Queue.noneT, table0.set id (var "fresh"))
    | _ => throw "the reply is no single message and no wait" : Except String (TermSrc × Table))
  let (accepted, woken) ← notifications s r.1 tb r.2.2
  let (first, second) := match mutation with
    | .swapNotifications => (woken, accepted)
    | .dropWake => (accepted, [])
    | .exact => (accepted, woken)
  pure (app "pair" [tuple [reply, listOf first, listOf second], stateTerm tb r.1])

def takeRaw (mutation : Mutation) (s : Queue.Model.State) (id : Nat) : Verdict :=
  judge (Queue.takeStep .nat (var (idName id)) (var "fresh") (stateTerm table0 s))
    (takeExpected mutation s id)

def takeAgrees (s : Queue.Model.State) (id : Nat) : Verdict :=
  guarded s (Queue.Model.take s ⟨id, 1, 1⟩).1 (foreign s id) (takeRaw .exact s id)

/-- The takers that a step with no accepted offer wakes. -/
def wakesOnly (before after : Queue.Model.State) (signals : List Queue.Model.Signal) :
    Except String (List TermSrc) := do
  let (accepted, woken) ← notifications before after table0 signals
  unless accepted.isEmpty do throw "this step answers no accepted offer"
  pure woken

/-- An offer of `a` by request `id`, on the encoding of `s`. -/
def offerExpected (mutation : Mutation) (s : Queue.Model.State) (id a : Nat) :
    Except String TermSrc := do
  let r := Queue.Model.offer s id a
  let reply := match r.2.1 with
    | .accepted ok => app "some" [bool ok]
    | .wait => Queue.noneT
  let woken ← wakesOnly s r.1 r.2.2
  let woken := match mutation with
    | .dropWake => []
    | _ => woken
  pure (app "pair" [tuple [reply, listOf woken], stateTerm table0 r.1])

def offerRaw (mutation : Mutation) (s : Queue.Model.State) (id a : Nat) : Verdict :=
  judge (Queue.offerStep .nat (var (idName id)) (var (hintName id)) (nat a) (stateTerm table0 s))
    (offerExpected mutation s id a)

def offerAgrees (s : Queue.Model.State) (id a : Nat) : Verdict :=
  guarded s (Queue.Model.offer s id a).1 (notFresh s id) (offerRaw .exact s id a)

def pollAgrees (s : Queue.Model.State) : Verdict :=
  let r := Queue.Model.poll s
  guarded s r.1 [] (judge (Queue.pollStep .nat (stateTerm table0 s)) (do
    let (accepted, woken) ← notifications s r.1 table0 r.2.2
    unless woken.isEmpty do throw "a poll wakes no taker"
    let reply := match r.2.1 with
      | some m => app "some" [nat m]
      | none => Queue.noneT
    pure (app "pair" [tuple [reply, listOf accepted], stateTerm table0 r.1])))

def sizeAgrees (s : Queue.Model.State) : Verdict :=
  guarded s s [] (judge (Queue.sizeStep .nat (stateTerm table0 s))
    (pure (nat (Queue.Model.size s))))

def withdrawTakeAgrees (s : Queue.Model.State) (id : Nat) : Verdict :=
  let r := Queue.Model.withdrawTake s id
  guarded s r.1 [] (judge (Queue.withdrawTake .nat (var (idName id)) (stateTerm table0 s)) (do
    let woken ← wakesOnly s r.1 r.2
    pure (app "pair" [listOf woken, stateTerm table0 r.1])))

def withdrawOfferAgrees (s : Queue.Model.State) (id : Nat) : Verdict :=
  let r := Queue.Model.withdrawOffer s id
  guarded s r.1 [] (judge (Queue.withdrawOffer .nat (var (idName id)) (stateTerm table0 s)) (do
    let woken ← wakesOnly s r.1 r.2
    pure (app "pair" [listOf woken, stateTerm table0 r.1])))

/-! ## The named controls C1 to C6 -/

def T (n : Nat) : Queue.Model.Taker := ⟨n, 1, 1⟩

/-- Codex's prefix, before its last step: capacity one, takers 1 and 2, message 1 buffered, the
offer of message 2 by request 101 pending. -/
def mixed : Queue.Model.State :=
  { capacity := some 1, messages := [1], takers := [T 1, T 2], offers := [⟨101, false, [2]⟩] }

/-- `mixed` before its second offer: the buffer is full, and no offer is pending. -/
def full : Queue.Model.State := { mixed with offers := [] }

/-- Takers 1 and 2 wait at an empty buffer. -/
def waiting2 : Queue.Model.State := { capacity := some 1, takers := [T 1, T 2] }

-- C1. The mixed notifications. The model's last step answers message 1, then the offerer's
-- answer before taker 2's wake. The term agrees, in that order.
#guard (Queue.Model.take mixed (T 1)).2 = (.got [1], [⟨101, .offered true⟩, ⟨2, .again⟩])
#guard takeAgrees mixed 1 = .agrees
-- C2. The first offer at a full buffer waits, and the model wakes the earliest taker again.
#guard (Queue.Model.offer full 101 2).2 = (.wait, [⟨1, .again⟩])
#guard offerAgrees full 101 2 = .agrees
-- C2b. An offer behind a pending offer waits and notifies nobody.
#guard (Queue.Model.offer mixed 102 3).2 = (.wait, [])
#guard offerAgrees mixed 102 3 = .agrees
-- C3. A taker that waits already, and no message: the model's state is unchanged, and the term
-- renews that request's hint and no other entry.
#guard Queue.Model.take waiting2 (T 1) = (waiting2, .wait, [])
#guard takeAgrees waiting2 1 = .agrees
-- C4. A new taker enrols behind a waiting one; and an offer into room wakes the earliest.
#guard takeAgrees { capacity := some 1, takers := [T 1] } 2 = .agrees
#guard offerAgrees { capacity := some 2, takers := [T 1] } 100 7 = .agrees
-- C5. The withdrawals: the earliest taker leaves and the next is woken; a pending offer leaves.
#guard (Queue.Model.withdrawTake mixed 1).2 = [⟨2, .again⟩]
#guard withdrawTakeAgrees mixed 1 = .agrees
#guard withdrawOfferAgrees mixed 101 = .agrees
-- C6. A poll that frees room accepts the pending offer; the size is the buffer's length.
#guard (Queue.Model.poll { mixed with takers := [] }).2 = (some 1, [⟨101, .offered true⟩])
#guard pollAgrees { mixed with takers := [] } = .agrees
#guard sizeAgrees mixed = .agrees

/-! ## The refusals P1 to P3: outside the profile the comparison refuses

Codex's witness is C4's state with one peeker. The model wakes taker 1 and then peeker 2. The
cell has no place for a peeker, so the comparison must not go on. -/

def peeked : Queue.Model.State := { capacity := some 2, takers := [T 1], peekers := [2] }
/-- A stored taker with the bounds two and two: one message does not make it ready. -/
def twoTwo : Queue.Model.State := { capacity := some 2, takers := [⟨1, 2, 2⟩] }

-- P1. The model's signals at the peeker's state: taker 1, then peeker 2. The comparison
-- refuses the state. With no premise, the encoder refuses the peeker's signal.
#guard (Queue.Model.offer peeked 100 7).2 = (.accepted true, [⟨1, .again⟩, ⟨2, .again⟩])
#guard offerAgrees peeked 100 7 =
  .outside ["a peeker waits", "after the step, a peeker waits"]
#guard offerRaw .exact peeked 100 7 =
  .unencoded "the wake of request 2 names no stored taker"
-- P2. The model wakes nobody for the two-and-two taker. The comparison refuses the state. With
-- no premise it differs: the step's wake does not read a stored taker's bounds.
#guard (Queue.Model.offer twoTwo 100 7).2 = (.accepted true, [])
#guard offerAgrees twoTwo 100 7 =
  .outside ["a stored taker's bounds are not one and one",
    "after the step, a stored taker's bounds are not one and one"]
#guard offerRaw .exact twoTwo 100 7 = .differs
-- P3. A request that breaks a step's premise: an offer by a request that waits already.
#guard offerAgrees mixed 101 9 =
  .outside ["the request's identity is not fresh",
    "after the step, two waiting requests share an identity"]
-- A take by a pending offer's identity breaks the take's premise.
#guard takeAgrees mixed 101 =
  .outside ["the request's identity names a waiting request of another kind",
    "after the step, two waiting requests share an identity"]

/-! ## The red controls M1 to M3: one notification changed, and nothing else

Each mutant keeps the shape, the reply and the stored value of a passing control. -/

-- M1. C1's expected result with its two notification lists exchanged.
#guard takeRaw .swapNotifications mixed 1 = .differs
-- M2. C2's expected result with its wake left out.
#guard offerRaw .dropWake full 101 2 = .differs
-- M3. C1's expected result with its wake left out.
#guard takeRaw .dropWake mixed 1 = .differs
-- The unchanged expected results agree with no premise too.
#guard takeRaw .exact mixed 1 = .agrees && offerRaw .exact full 101 2 = .agrees

/-! ## Every state of a finite universe of the profile

The universe: capacity one or two; a buffer of zero to three messages; the takers 1 and 2 in
each order; the pending offers 100 and 101 in each order. A buffer may be longer than the
capacity, and an offer may be pending beside free room: the profile does not ask for `within`
or `tidy`. Each move's request keeps its step's premise. -/

inductive Move
  | take (id : Nat) | offer (id a : Nat) | poll | size | dropTake (id : Nat)
  | dropOffer (id : Nat)
  deriving Repr

def moves : List Move :=
  [.take 1, .take 2, .take 3, .offer 102 30, .poll, .size, .dropTake 1, .dropTake 2, .dropTake 3,
   .dropOffer 100, .dropOffer 101, .dropOffer 102]

def Move.verdict (s : Queue.Model.State) : Move → Verdict
  | .take id => takeAgrees s id
  | .offer id a => offerAgrees s id a
  | .poll => pollAgrees s
  | .size => sizeAgrees s
  | .dropTake id => withdrawTakeAgrees s id
  | .dropOffer id => withdrawOfferAgrees s id

def Move.next (s : Queue.Model.State) : Move → Queue.Model.State
  | .take id => (Queue.Model.take s ⟨id, 1, 1⟩).1
  | .offer id a => (Queue.Model.offer s id a).1
  | .poll => (Queue.Model.poll s).1
  | .size => s
  | .dropTake id => (Queue.Model.withdrawTake s id).1
  | .dropOffer id => (Queue.Model.withdrawOffer s id).1

def orders {α : Type} (a b : α) : List (List α) := [[], [a], [b], [a, b], [b, a]]

def profileStates : List Queue.Model.State :=
  [1, 2].flatMap fun cap =>
  ([[], [7], [7, 8], [7, 8, 9]] : List (List Nat)).flatMap fun messages =>
  (orders (T 1) (T 2)).flatMap fun takers =>
  (orders (⟨100, false, [20]⟩ : Queue.Model.Offer) ⟨101, false, [21]⟩).map fun offers =>
    ({ capacity := some cap, messages := messages, takers := takers, offers := offers } :
      Queue.Model.State)

/-- Every state of the universe is of the profile, and each move leaves the profile true. -/
def closed : Bool :=
  profileStates.all fun s => firstProfile s && moves.all fun m => firstProfile (m.next s)

/-- The states and moves whose verdict is not `agrees`. -/
def disagreements : List (Queue.Model.State × Nat) :=
  profileStates.flatMap fun s => moves.zipIdx.filterMap fun (m, i) =>
    if m.verdict s = .agrees then none else some (s, i)

-- The states, the comparisons, and whether the profile is closed on them: a finite instance of
-- the proved closure.
#guard profileStates.length = 200 && profileStates.length * moves.length = 2400 && closed
-- All 2,400 comparisons agree.
#guard disagreements.isEmpty
-- The words of `profileFaults` agree with the tree's predicate: on each state of the universe,
-- on each state a move leaves, and on the three states outside the profile.
#guard (profileStates.all fun s => faultsAgree s && moves.all fun m => faultsAgree (m.next s)) &&
  [peeked, twoTwo, (Queue.Model.offer mixed 101 9).1].all faultsAgree

/-- A deliberate defect of a step, for a red control of the whole comparison: the first draft's
offer, which notifies nobody when it waits at a full buffer. -/
def offerStepSilent (id hint a s : TermSrc) : TermSrc :=
  let msgs := field s "msgs"
  let offers := field s "offers"
  let takers := field s "takers"
  let pending := recordSet s "offers"
    (Queue.snoc offers (Queue.mkOffer .nat id hint (bool false) (app "cons" [a, Queue.nilT])))
  Queue.ifT (Queue.orT (Queue.notT (Queue.isEmpty offers))
      (Queue.notT (app "lt" [Queue.len msgs, field s "cap"])))
    (app "pair" [tuple [Queue.noneT, Queue.noneOf takers], pending])
    (app "pair" [tuple [app "some" [bool true], Queue.wake takers (Queue.snoc msgs a)],
      recordSet s "msgs" (Queue.snoc msgs a)])

-- M4. The comparison over every state finds the silent offer: it differs exactly where the
-- buffer is full, no offer is pending, and a taker waits behind a message. Twenty states.
#guard (profileStates.filter fun s =>
  judge (offerStepSilent (var (idName 102)) (var (hintName 102)) (nat 30) (stateTerm table0 s))
    (offerExpected .exact s 102 30) != .agrees).length = 20
#guard (profileStates.filter fun s =>
  decide (s.offers = []) && decide (s.capacity.getD 0 ≤ s.messages.length) &&
    !s.takers.isEmpty && !s.messages.isEmpty).length = 20
-- The two sets are one set of states.
#guard profileStates.all fun s =>
  (judge (offerStepSilent (var (idName 102)) (var (hintName 102)) (nat 30) (stateTerm table0 s))
    (offerExpected .exact s 102 30) != .agrees) ==
  (decide (s.offers = []) && decide (s.capacity.getD 0 ≤ s.messages.length) &&
    !s.takers.isEmpty && !s.messages.isEmpty)

end Test.Program.QueueAgreement
