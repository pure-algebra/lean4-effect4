import Effect4.Laws.Library.Queue.Steps
import Effect4.Laws.Step.Store
import Test.Program.QueueAgreement

/-!
# The Queue's relation and its step goals: finite controls (decisions row 255)

The relation is `src/Effect4/Laws/Library/Queue/Relation.lean`: the message map, the cell's
value and a step's notifications, over the shared encoding table
(`src/Effect4/Laws/Step/Table.lean`). The six step goals are in
`src/Effect4/Laws/Library/Queue/Steps.lean`. This battery evaluates each goal's conclusion, as
the goal states it: at one table, one message map and the scope of the step's own arguments, on
every state of the universe of `Test/Program/QueueAgreement.lean`, twelve moves on each.

It also ties the two encodings: the cell's value of the relation is the value of the
comparison's state term. The red controls drop one premise each: the table's injectivity, and
the hint that a step sets.

Placement. Each guard is a finite instance of a step goal (concept `translation-simulation`,
requirement R10, a part of the proposed claim `queue-expansion-agrees`). A state outside the
universe, another table and another message type are not checked.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Test.Program.QueueRelation

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Modules
open Effect4.Queue.Model
open Test.Program.QueueAgreement (profileStates moves Move mixed full waiting2 T)

/-! ## One table, one message map -/

/-- The comparison's table: request `n` has the identity handle `n` and the hint `1000 + n`. -/
def tb0 : Table := { handle := fun n => ⟨n⟩, hint := fun n => ⟨1000 + n⟩ }

/-- The hint that a step receives. -/
def fresh : DeferredKey := ⟨9999⟩

/-- The model's messages are the cell's numbers. -/
def msg : Nat → Val := Val.nat

-- The relation's cell value is the value of the comparison's state term, on every state of
-- the universe: the two encodings are one.
#guard profileStates.all fun s =>
  decide (QueueAgreement.evalAt (QueueAgreement.stateTerm QueueAgreement.table0 s) =
    some (cellVal tb0 msg s))
-- The initial value of a positive capacity is the cell's value of the model's empty queue.
#guard [1, 2, 7].all fun c =>
  decide ((Queue.empty .nat c {} []).toOption.bind (evalTerm []) =
    some (cellVal tb0 msg { capacity := some c }))

/-! ## A goal's conclusion, decided -/

/-- `Reads` at a scope of names, decided: the source elaborates, and its tree has the value. -/
def readsAt (names : List String) (vals : List Val) (src : TermSrc) (v : Val) : Bool :=
  decide ((src { names := names } []).toOption.bind (evalTerm vals) = some v)

/-- The model's signals read as a first-profile step's two lists: the offers that entered, then
the takers to wake. `none` where a signal has no encoding. -/
def decode (before after : State) (signals : List Signal) :
    Option (List Offer × List Taker) := do
  let isAnswer := fun (g : Signal) => g.note == Note.offered true
  let entered ← (signals.takeWhile isAnswer).mapM fun g => before.offers.find? (·.id == g.id)
  let woken ← (signals.dropWhile isAnswer).mapM fun g =>
    if g.note == Note.again then after.takers.find? (·.id == g.id) else none
  pure (entered, woken)

/-- `Notified`, decided clause by clause. -/
def notified (before after : State) (signals : List Signal) (entered : List Offer)
    (woken : List Taker) : Bool :=
  decide (signals = entered.map (fun o => (⟨o.id, .offered true⟩ : Signal)) ++
    woken.map (fun t => (⟨t.id, .again⟩ : Signal))) &&
  entered.all (fun o => decide (o ∈ before.offers)) &&
  woken.all (fun t => decide (t ∈ after.takers))

/-- The conclusion of `takeStep_agrees`, at the table `tb` and the step's own scope. -/
def takeHolds (tb : Table) (s : State) (id : Nat) : Bool :=
  let r := take s ⟨id, 1, 1⟩
  let after := tb.afterTake id fresh r.2.1
  match takeReplyVal msg r.2.1, decode s r.1 r.2.2 with
  | some reply, some (entered, woken) =>
    notified s r.1 r.2.2 entered woken &&
    readsAt ["id", "hint", "s"] [Val.promise (tb.handle id), Val.promise fresh, cellVal tb msg s]
      (Queue.takeStep .nat (var "id") (var "hint") (var "s"))
      (Val.tuple [Val.tuple [reply, Val.list (entered.map (offerVal tb msg)),
          Val.list (woken.map (takerVal after))],
        cellVal after msg r.1])
  | _, _ => false

/-- The conclusion of `offerStep_agrees`. -/
def offerHolds (tb : Table) (s : State) (id a : Nat) : Bool :=
  let r := offer s id a
  let after := tb.afterOffer id fresh r.2.1
  match decode s r.1 r.2.2 with
  | some ([], woken) =>
    notified s r.1 r.2.2 [] woken &&
    readsAt ["id", "hint", "a", "s"]
      [Val.promise (tb.handle id), Val.promise fresh, msg a, cellVal tb msg s]
      (Queue.offerStep .nat (var "id") (var "hint") (var "a") (var "s"))
      (Val.tuple [Val.tuple [offerReplyVal r.2.1, Val.list (woken.map (takerVal after))],
        cellVal after msg r.1])
  | _ => false

/-- The conclusion of `pollStep_agrees`. -/
def pollHolds (tb : Table) (s : State) : Bool :=
  let r := poll s
  match decode s r.1 r.2.2 with
  | some (entered, []) =>
    notified s r.1 r.2.2 entered [] &&
    readsAt ["s"] [cellVal tb msg s] (Queue.pollStep .nat (var "s"))
      (Val.tuple [Val.tuple [pollReplyVal msg r.2.1, Val.list (entered.map (offerVal tb msg))],
        cellVal tb msg r.1])
  | _ => false

/-- The conclusion of `sizeStep_agrees`. -/
def sizeHolds (tb : Table) (s : State) : Bool :=
  readsAt ["s"] [cellVal tb msg s] (Queue.sizeStep .nat (var "s")) (Val.nat (size s))

/-- The conclusion of `withdrawTake_agrees`. -/
def withdrawTakeHolds (tb : Table) (s : State) (id : Nat) : Bool :=
  let r := withdrawTake s id
  match decode s r.1 r.2 with
  | some ([], woken) =>
    notified s r.1 r.2 [] woken &&
    readsAt ["id", "s"] [Val.promise (tb.handle id), cellVal tb msg s]
      (Queue.withdrawTake .nat (var "id") (var "s"))
      (Val.tuple [Val.list (woken.map (takerVal tb)), cellVal tb msg r.1])
  | _ => false

/-- The conclusion of `withdrawOffer_agrees`. -/
def withdrawOfferHolds (tb : Table) (s : State) (id : Nat) : Bool :=
  let r := withdrawOffer s id
  match decode s r.1 r.2 with
  | some ([], woken) =>
    notified s r.1 r.2 [] woken &&
    readsAt ["id", "s"] [Val.promise (tb.handle id), cellVal tb msg s]
      (Queue.withdrawOffer .nat (var "id") (var "s"))
      (Val.tuple [Val.list (woken.map (takerVal tb)), cellVal tb msg r.1])
  | _ => false

/-- One move's goal, at a table. -/
def holds (tb : Table) (s : State) : Move → Bool
  | .take id => takeHolds tb s id
  | .offer id a => offerHolds tb s id a
  | .poll => pollHolds tb s
  | .size => sizeHolds tb s
  | .dropTake id => withdrawTakeHolds tb s id
  | .dropOffer id => withdrawOfferHolds tb s id

/-! ## The named controls, and every state of the universe -/

-- C1. The mixed notifications: the offerer's answer, then taker 2's wake.
#guard decode mixed (take mixed (T 1)).1 (take mixed (T 1)).2.2 =
  some ([⟨101, false, [2]⟩], [T 2])
#guard takeHolds tb0 mixed 1
-- C2 and C2b. The first offer at a full buffer wakes taker 1; behind a pending offer, nobody.
#guard offerHolds tb0 full 101 2 && offerHolds tb0 mixed 102 3
-- C3. A taker that waits already: the model's state is unchanged, and the cell's value is the
-- state's through the table that holds the step's hint at that request.
#guard (take waiting2 (T 1)).1 = waiting2 && takeHolds tb0 waiting2 1
#guard cellVal (tb0.renew 1 fresh) msg waiting2 ≠ cellVal tb0 msg waiting2
-- C5 and C6. The withdrawals, a poll that frees room, and the size.
#guard withdrawTakeHolds tb0 mixed 1 && withdrawOfferHolds tb0 mixed 101
#guard pollHolds tb0 { mixed with takers := [] } && sizeHolds tb0 mixed

-- Every state of the universe, twelve moves on each: each goal's conclusion holds.
#guard profileStates.all fun s => moves.all fun m => holds tb0 s m
#guard profileStates.length * moves.length = 2400

/-! ## Red controls: one premise dropped -/

/-- A table that is not injective: the requests 1 and 2 share one handle. -/
def shared : Table := { tb0 with handle := fun n => if n = 2 then ⟨1⟩ else ⟨n⟩ }

-- The premise of injectivity. Under the shared handle, a withdrawal of taker 2 removes taker 1
-- too, and the conclusion fails; on a state with neither taker it still holds.
#guard !withdrawTakeHolds shared waiting2 2
#guard withdrawTakeHolds shared { capacity := some 1 } 2
-- It fails on each state that holds taker 1 or taker 2: four of the five orders of the takers.
#guard (profileStates.filter fun s => !moves.all fun m => holds shared s m).length = 160
#guard (profileStates.filter fun s => !s.takers.isEmpty).length = 160
-- The hint that a step sets. With the table left as it was, the conclusion of a take that waits
-- fails: the stored hint is the step's. A take that consumes does not read the table's change.
#guard !readsAt ["id", "hint", "s"]
    [Val.promise (tb0.handle 1), Val.promise fresh, cellVal tb0 msg waiting2]
    (Queue.takeStep .nat (var "id") (var "hint") (var "s"))
    (Val.tuple [Val.tuple [Store.Val.none, Val.list [], Val.list []], cellVal tb0 msg waiting2])
#guard (take mixed (T 1)).2.1 = .got [1] &&
  cellVal (tb0.afterTake 1 fresh (take mixed (T 1)).2.1) msg mixed = cellVal tb0 msg mixed
-- The order of the notifications. C1's two lists exchanged are no conclusion.
#guard !readsAt ["id", "hint", "s"]
    [Val.promise (tb0.handle 1), Val.promise fresh, cellVal tb0 msg mixed]
    (Queue.takeStep .nat (var "id") (var "hint") (var "s"))
    (Val.tuple [Val.tuple [Store.Val.some (msg 1), Val.list [takerVal tb0 (T 2)],
        Val.list [offerVal tb0 msg ⟨101, false, [2]⟩]],
      cellVal tb0 msg (take mixed (T 1)).1])
-- A signal with no encoding is refused: with a peeker the model wakes a request that is no
-- stored taker.
#guard decode { capacity := some 2, takers := [T 1], peekers := [2] }
    (offer { capacity := some 2, takers := [T 1], peekers := [2] } 100 7).1
    (offer { capacity := some 2, takers := [T 1], peekers := [2] } 100 7).2.2 = none

/-! ## The statements at the scope of a step's own arguments

A step statement holds at every scope, for every caller's term that reads the step's
arguments. A variable that an author wrote is such a term (`captured_var`). So each statement
applies at the scope that the guards above evaluate: the two examples are its instances. -/

example (A : Ty) (tb : Table) (msg : Nat → Val) (s : State) (id : Nat) (profile : FirstProfile s)
    (injective : tb.Injective) :
    ∃ woken,
      Notified s (withdrawTake s id).1 (withdrawTake s id).2 [] woken ∧
      Reads (Queue.withdrawTake A (var "id") (var "s")) { names := ["id", "s"] } []
        [Val.promise (tb.handle id), cellVal tb msg s]
        (Val.tuple [Val.list (woken.map (takerVal tb)), cellVal tb msg (withdrawTake s id).1]) :=
  withdrawTake_agrees A tb msg s id profile injective rfl
    (captured_var rfl rfl rfl) (captured_var (x := "s") rfl rfl rfl).atScope

example (A : Ty) (tb : Table) (msg : Nat → Val) (s : State) (id : Nat) (hint : DeferredKey)
    (profile : FirstProfile s) (requested : Requested s (.take id 1 1))
    (injective : tb.Injective) :
    ∃ reply entered woken,
      takeReplyVal msg (take s ⟨id, 1, 1⟩).2.1 = some reply ∧
      Notified s (take s ⟨id, 1, 1⟩).1 (take s ⟨id, 1, 1⟩).2.2 entered woken ∧
      Reads (Queue.takeStep A (var "id") (var "hint") (var "s"))
        { names := ["id", "hint", "s"] } []
        [Val.promise (tb.handle id), Val.promise hint, cellVal tb msg s]
        (Val.tuple [Val.tuple [reply, Val.list (entered.map (offerVal tb msg)),
            Val.list (woken.map (takerVal (tb.afterTake id hint (take s ⟨id, 1, 1⟩).2.1)))],
          cellVal (tb.afterTake id hint (take s ⟨id, 1, 1⟩).2.1) msg (take s ⟨id, 1, 1⟩).1]) :=
  takeStep_agrees A tb msg s id hint profile requested injective rfl
    (captured_var rfl rfl rfl) (captured_var (x := "hint") rfl rfl rfl)
    (captured_var (x := "s") rfl rfl rfl).atScope

end Test.Program.QueueRelation
