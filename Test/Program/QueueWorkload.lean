import Effect4.Api.Author
import Effect4.Program.Authoring.Loops
import Effect4.Laws.Program.Agreement.Machine
import Effect4.Laws.Program.Agreement.Loop
import Test.Program.QueueRelation

/-!
# One workload of the Queue's steps in two spellings (decisions row 255)

A client uses the six step terms of `src/Effect4/Modules/Queue/Steps.lean` as a program does:
one `Ref.modify` for each step, over one cell. The workload is Codex's
(`docs/research/2026-10-05-codex-foundation-packet/implementation-audit/queue-dogfood-design-research/dogfood/review.md`):
capacity one; the takers A and B enrol; the offers 10 and 20 follow; two takes consume.

| Operation | Reply | Notifications, in order |
| --- | --- | --- |
| take A | wait | none |
| take B | wait | none |
| offer P 10 | accepted | the wake of A |
| offer Q 20 | wait | the wake of A |
| take A | message 10 | the answer of Q, then the wake of B |
| take B | message 20 | none |

The setup is shared: the cell, ten handles in one allocation order, and the first four
operations. The two consuming takes are written twice: as a sequence, and as a finite loop over
the two takers. A withdrawal of the second offer runs at two places: before the take that
accepts it, and after that take.

**The observation** is every reply, the whole cell after each operation, and each notification
in order. Its expected value is the model's trace
(`src/Effect4/Laws/Modules/Queue/Model.lean`) through the relation
(`src/Effect4/Laws/Modules/Queue/Relation.lean`), with the table that the allocation order
gives. A notification is read as data: no helper is posted, and no fiber waits.

Placement. A finite control of the six step statements along a run
(`src/Effect4/Laws/Modules/Queue/Steps.lean`; concept `translation-simulation`, requirement
R10, parts of the proposed claim `queue-expansion-agrees`). The sequence is in the straight
fragment, so `run_eq_meaning` gives its run. The loop is in the looped fragment and its
budgeted meaning finishes, so `loopAgreement` gives its run. Their premises are checked here by
evaluation, on these programs only. Nothing here states delivery, an interruption or a host
run. Seat DOGFOOD's scenario record came into the branch after this workload was designed: the
workload is a plain battery, and no scenario of that record.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Test.Program.QueueWorkload

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Program.Denote Effect4.Program.Agreement
open Effect4.Queue.Model
open Test.Program.QueueRelation (decode msg)

/-! ## The programs -/

/-- Where the second offer is withdrawn. -/
inductive Withdrawal
  | never
  /-- Before the take that would accept it: the offer leaves, and its message never enters. -/
  | beforeAccept
  /-- After the take that accepted it: nothing is pending, and the message stays accepted. -/
  | afterAccept
  deriving DecidableEq

/-- What the setup hands on: the cell, the two logs, and each request's identity and hint. -/
structure Handles where
  q : TermSrc
  takes : TermSrc
  withdrawals : TermSrc
  a : TermSrc
  b : TermSrc
  o : TermSrc
  hintA : TermSrc
  hintB : TermSrc

/-- One step on the cell, with the cell's value after it: the pair of the reply and the cell.

The row fixes the name `s` for the cell's current value. Every other term under that binder is
this battery's own: a handle that the setup binds under another name, a literal, or the loop's
counter (addendum 2 of the seat's brief). -/
def stepThen (q : TermSrc) (step : TermSrc → TermSrc) : Src NativeOp := eff do
  let r ← Ref.modify "s" (step (var "s")) q
  let cell ← Ref.get q
  return app "pair" [r, cell]

/-- A step whose entry joins a log. -/
def logged (q log : TermSrc) (step : TermSrc → TermSrc) : Src NativeOp := eff do
  let e ← stepThen q step
  Ref.update "l" (Queue.snoc (var "l") e) log

/-- The shared setup: the cell at capacity one, ten handles, and the first four operations. The
empty logs take their types from the first entry. -/
def setup (rest : Handles → TermSrc → Src NativeOp) : Src NativeOp := eff do
  let q ← Ref.make (Queue.empty .nat 1)
  let a ← Deferred.make .unit .never
  let b ← Deferred.make .unit .never
  let p ← Deferred.make .unit .never
  let o ← Deferred.make .unit .never
  let ha ← Deferred.make .unit .never
  let hb ← Deferred.make .unit .never
  let hp ← Deferred.make .bool .never
  let ho ← Deferred.make .bool .never
  let ha2 ← Deferred.make .unit .never
  let hb2 ← Deferred.make .unit .never
  let e1 ← stepThen q (Queue.takeStep .nat a ha)
  let e2 ← stepThen q (Queue.takeStep .nat b hb)
  let e3 ← stepThen q (Queue.offerStep .nat p hp (nat 10))
  let e4 ← stepThen q (Queue.offerStep .nat o ho (nat 20))
  let takes ← Ref.make (app "take" [app "cons" [e1, Queue.nilT], nat 0])
  let withdrawals ← Ref.make (app "take" [app "cons"
    [app "pair" [Queue.noneOf (field (app "snd" [e1]) "takers"), app "snd" [e1]], Queue.nilT],
    nat 0])
  rest ⟨q, takes, withdrawals, a, b, o, ha2, hb2⟩ (tuple [e1, e2, e3, e4])

/-- The withdrawal of the second offer, logged. -/
def withdraw (h : Handles) : Src NativeOp :=
  logged h.q h.withdrawals (Queue.withdrawOffer .nat h.o)

/-- The observation: the setup's four entries, the two logs and the cell. -/
def observe (h : Handles) (first : TermSrc) : Src NativeOp := eff do
  let takes ← Ref.get h.takes
  let withdrawals ← Ref.get h.withdrawals
  let cell ← Ref.get h.q
  return tuple [first, takes, withdrawals, cell]

/-- A step that a variant leaves out. -/
def skipWhen (skip : Bool) (step : Src NativeOp) : Src NativeOp :=
  if skip then succeed unit else step

/-- **The sequence**: the two consuming takes, one after the other. -/
def sequence (w : Withdrawal) : Src NativeOp :=
  setup fun h first => eff do
    let _ ← skipWhen (w != .beforeAccept) (withdraw h)
    let _ ← logged h.q h.takes (Queue.takeStep .nat h.a h.hintA)
    let _ ← skipWhen (w != .afterAccept) (withdraw h)
    let _ ← logged h.q h.takes (Queue.takeStep .nat h.b h.hintB)
    observe h first

/-- The first of two terms at round zero, and the second after it. -/
def pick (i first second : TermSrc) : TermSrc := Queue.ifT (app "isZero" [i]) first second

/-- **The loop**: the two consuming takes as two rounds of one loop over the takers. The
request's identity and its hint are terms over the loop's counter. -/
def looped (w : Withdrawal) : Src NativeOp :=
  setup fun h first => eff do
    let _ ← skipWhen (w != .beforeAccept) (withdraw h)
    let _ ← forRange (nat 0) (nat 2) fun i => eff do
      let _ ← logged h.q h.takes
        (Queue.takeStep .nat (pick i h.a h.b) (pick i h.hintA h.hintB))
      skipWhen (w != .afterAccept) (ifElse (app "isZero" [i]) (withdraw h) (succeed unit))
    observe h first

/-! ## The expected observation: the model's trace through the relation

The allocation order gives the table: the identities of A, B, P and Q are the `Deferred` keys
0 to 3, and the hints follow from key 4. -/

def A : Nat := 1
def B : Nat := 2
def P : Nat := 100
def Q : Nat := 101

def table0 : Table :=
  { handle := fun n => if n = A then ⟨0⟩ else if n = B then ⟨1⟩ else if n = P then ⟨2⟩ else ⟨3⟩
    hint := fun _ => ⟨0⟩ }

/-- A point of the model's trace: the table, the state, and the entries so far. -/
structure Point where
  tb : Table
  s : State
  entries : List Val := []

/-- A take's entry: the reply, the two notification lists and the cell. `swap` exchanges the
two lists, for a red control. -/
def takeOp (id : Nat) (hint : DeferredKey) (swap : Bool := false) (at_ : Point) : Option Point :=
  let r := take at_.s ⟨id, 1, 1⟩
  let after := at_.tb.afterTake id hint r.2.1
  match takeReplyVal msg r.2.1, decode at_.s r.1 r.2.2 with
  | some reply, some (entered, woken) =>
    let answers := Val.list (entered.map (offerVal at_.tb msg))
    let wakes := Val.list (woken.map (takerVal after))
    some { tb := after, s := r.1, entries := at_.entries ++
      [Val.tuple [Val.tuple (reply :: (if swap then [wakes, answers] else [answers, wakes])),
        cellVal after msg r.1]] }
  | _, _ => none

def offerOp (id a : Nat) (hint : DeferredKey) (at_ : Point) : Option Point :=
  let r := offer at_.s id a
  let after := at_.tb.afterOffer id hint r.2.1
  match decode at_.s r.1 r.2.2 with
  | some ([], woken) =>
    some { tb := after, s := r.1, entries := at_.entries ++
      [Val.tuple [Val.tuple [offerReplyVal r.2.1, Val.list (woken.map (takerVal after))],
        cellVal after msg r.1]] }
  | _ => none

def withdrawOp (id : Nat) (at_ : Point) : Option Point :=
  let r := withdrawOffer at_.s id
  match decode at_.s r.1 r.2 with
  | some ([], woken) =>
    some { at_ with s := r.1, entries := at_.entries ++
      [Val.tuple [Val.list (woken.map (takerVal at_.tb)), cellVal at_.tb msg r.1]] }
  | _ => none

/-- The observation that the model's trace gives. -/
def expected (w : Withdrawal) (swap : Bool := false) : Option Val := do
  let p ← takeOp A ⟨4⟩ false { tb := table0, s := { capacity := some 1 } }
  let p ← takeOp B ⟨5⟩ false p
  let p ← offerOp P 10 ⟨6⟩ p
  let p ← offerOp Q 20 ⟨7⟩ p
  let first := p.entries
  let before ← if w = .beforeAccept then withdrawOp Q { p with entries := [] }
    else some { p with entries := [] }
  let p ← takeOp A ⟨8⟩ swap { before with entries := [] }
  let after ← if w = .afterAccept then withdrawOp Q { p with entries := [] }
    else some { p with entries := [] }
  let p' ← takeOp B ⟨9⟩ false { after with entries := p.entries }
  some (Val.tuple [Val.tuple first, Val.list p'.entries,
    Val.list (before.entries ++ after.entries), cellVal p'.tb msg p'.s])

/-! ## The runs -/

def build (src : Src NativeOp) : Option Api.Program :=
  (Effect4.Api.Author.build { main := src }).toOption.map (·.program)

/-- The fuel that `run_eq_meaning` asks for. -/
def straightFuel (e : Api.Program) : Nat := max (depth e) (2 * steps e + 6)

/-- The budget at which each loop's meaning is taken. -/
def budget : Nat := 4

/-- The fuel that `loopAgreement` gives for a meaning that finishes at `budget`. -/
def loopFuel (e : Api.Program) : Nat := max (depthB e) (2 * (boundB budget e + 1) + 4)

/-- The sequence's checks: it builds, it is in the straight fragment, and its run at the
theorem's fuel finishes with the exit of its meaning, which is the expected observation. -/
def sequenceHolds (w : Withdrawal) : Bool :=
  match build (sequence w), expected w with
  | some e, some want =>
    Straight e &&
    decide ((Api.run e (straightFuel e)).exit = some (meaning e [] Stores.empty).1) &&
    decide ((Api.run e (straightFuel e)).exit = some (.success want))
  | _, _ => false

/-- The loop's checks: it builds, it is in the looped fragment and not in the straight one, its
budgeted meaning finishes with the expected observation, and its run at the theorem's fuel
finishes with that exit. -/
def loopHolds (w : Withdrawal) : Bool :=
  match build (looped w), expected w with
  | some e, some want =>
    Looped e && !Straight e &&
    decide ((meaningB budget e [] Stores.empty).1 = some (.success want)) &&
    decide ((Api.run e (loopFuel e)).exit = some (.success want))
  | _, _ => false

def variants : List Withdrawal := [.never, .beforeAccept, .afterAccept]

-- The model's trace has an encoding at each variant.
#guard variants.all fun w => (expected w).isSome
-- The sequence, at each place of the withdrawal.
#guard variants.all sequenceHolds
-- The loop, at each place of the withdrawal.
#guard variants.all loopHolds

/-! ## What the observation shows -/

/-- The replies of the two consuming takes, and the buffer at the end. -/
def summary (w : Withdrawal) : Option (List (Option Nat) × List Nat) :=
  let finish : Option (List TakeReply × List Nat) := do
    let s : State := { capacity := some 1 }
    let s := (take s ⟨A, 1, 1⟩).1
    let s := (take s ⟨B, 1, 1⟩).1
    let s := (offer s P 10).1
    let s := (offer s Q 20).1
    let s := if w = .beforeAccept then (withdrawOffer s Q).1 else s
    let x := take s ⟨A, 1, 1⟩
    let s := if w = .afterAccept then (withdrawOffer x.1 Q).1 else x.1
    let y := take s ⟨B, 1, 1⟩
    pure ([x.2.1, y.2.1], y.1.messages)
  finish.map fun (replies, buffer) =>
    (replies.map fun | .got [m] => some m | _ => none, buffer)

-- With no withdrawal: A takes 10 and B takes 20. Withdrawn before its acceptance, the second
-- offer's message never enters: B waits. Withdrawn after it, the message stays accepted: B
-- takes 20.
#guard summary .never = some ([some 10, some 20], [])
#guard summary .beforeAccept = some ([some 10, none], [])
#guard summary .afterAccept = some ([some 10, some 20], [])
-- The three observations are three values.
#guard expected .never != expected .beforeAccept && expected .never != expected .afterAccept &&
  expected .beforeAccept != expected .afterAccept

/-! ## Red controls -/

/-- The run's observation. -/
def observed (src : Src NativeOp) : Option ExitV :=
  (build src).bind fun e => (Api.run e (max (straightFuel e) (loopFuel e))).exit

/-- An observation as a run's successful exit. -/
def exitWith (value : Option Val) : Option ExitV := value.map fun v => .success v

-- The reversed notifications. The take that accepts the second offer names the offerer's answer
-- before B's wake. The expected observation with those two lists exchanged is not the run's.
#guard (expected .never true).isSome && expected .never true != expected .never
#guard observed (sequence .never) != exitWith (expected .never true)
#guard observed (looped .never) != exitWith (expected .never true)

/-- A cell update that is dropped: the take that accepts the second offer answers its reply and
stores the cell as it was. -/
def dropped : Src NativeOp :=
  setup fun h first => eff do
    let _ ← logged h.q h.takes fun s =>
      app "pair" [app "fst" [Queue.takeStep .nat h.a h.hintA s], s]
    let _ ← logged h.q h.takes (Queue.takeStep .nat h.b h.hintB)
    observe h first

-- It builds, and its observation is not the expected one: the cell after the take still holds
-- message 10, the taker A and the pending offer.
#guard (build dropped).isSome
#guard (observed dropped).isSome && observed dropped != exitWith (expected .never)
-- Green twin of the two red controls: the unchanged programs give the expected observation.
#guard observed (sequence .never) == exitWith (expected .never)
#guard observed (looped .never) == exitWith (expected .never)

end Test.Program.QueueWorkload
