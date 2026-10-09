import Effect4.Library.Pool.Steps
import Effect4.Laws.Library.Pool.Profile
import Effect4.Laws.Library.Pool.Typing

/-!
# Pool's steps against the abstract model: the comparison (rows 267 to 269 and 276)

A comparison evaluates one step term of `src/Effect4/Library/Pool/Steps.lean` on the encoding
of a model state, and compares the whole result with the encoding of the model's transition
(`src/Effect4/Library/Pool/Model.lean`): the reply and the stored value.

The battery holds:

- the named controls C1 to C7, on the states of the contract's traces;
- every state of a finite universe of the profile, 130 states, with 19 moves on each;
- five states outside the profile: the comparison agrees there too, so no step goal needs the
  profile as a premise;
- the red controls M1 to M5: one part of an expected result changed, and nothing else;
- the faults F1 to F5 that a step can show. Each is a changed step term, red at its own
  property, and the checker types each as it types the library's step.

Placement. Each comparison is a finite instance of a step goal of Pool's refinement (concept
`translation-simulation`, requirement R10, a part of the proposed claim
`pool-expansion-agrees`). Every guard is a finite check. A state outside the universe is not
checked. No guard states delivery, a law of the wake across helpers, a cancellation law or
liveness.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Test.Program.PoolAgreement

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Pool.Model (State Item Profile)
open Effect4.Modules

/-! ## The encoding

Model request `n` has the identity handle `i<n>` and a current hint `h<n>`. A lease that enrols
its request sets that request's entry of the table, and no other. A model resource `r` has the
value `100 + r`. -/

def ids : List Nat := [1, 2, 3]
def idName (n : Nat) : String := s!"i{n}"
def hintName (n : Nat) : String := s!"h{n}"
def envNames : List String := ids.flatMap (fun n => [idName n, hintName n]) ++ ["fresh"]
def envVals : List Val :=
  ids.flatMap (fun n => [Val.promise ⟨n⟩, Val.promise ⟨1000 + n⟩]) ++ [Val.promise ⟨9999⟩]

/-- A term's value in the scope of the handles. -/
def evalAt (src : TermSrc) : Option Val :=
  (src { names := envNames } []).toOption.bind (evalTerm envVals ·)

/-- The table: a request's current hint. -/
abbrev Table := Nat → TermSrc
def table0 : Table := fun n => var (hintName n)
def Table.set (tb : Table) (id : Nat) (hint : TermSrc) : Table :=
  fun n => if n = id then hint else tb n

def itemTerm (it : Item) : TermSrc :=
  record (Pool.itemFields .nat)
    [("stamp", nat it.stamp), ("resource", nat (100 + it.resource)),
     ("borrowed", bool it.borrowed), ("lease", nat it.lease)]

def waiterTerm (tb : Table) (id : Nat) : TermSrc := Pool.mkWaiter (var (idName id)) (tb id)

/-- The cell's value for a model state: it loses nothing of the state. -/
def stateTerm (tb : Table) (s : State) : TermSrc :=
  record (Pool.cellFields .nat)
    [("items", listOf (s.items.map itemTerm)), ("available", listOf (s.available.map nat)),
     ("waiters", listOf (s.waiters.map (waiterTerm tb))), ("closing", bool s.closing),
     ("next", nat s.next)]

/-! ## The comparison -/

inductive Verdict
  /-- The term's whole result is the encoding of the model's. -/
  | agrees
  | differs
  /-- A term has no value. -/
  | stuck (which : String)
  deriving DecidableEq

/-- One comparison: the step term's whole result against the encoding of the model's. -/
def judge (step expected : TermSrc) : Verdict :=
  match evalAt step, evalAt expected with
  | some got, some want => if got = want then .agrees else .differs
  | none, _ => .stuck "the step term"
  | _, none => .stuck "the expected term"

/-- A deliberate defect of an expected result, for a red control. -/
inductive Mutation
  | exact
  /-- The reply's first Boolean is the other one. -/
  | flipReply
  /-- The table stays as it was: the enrolled request keeps its old hint. -/
  | keepHint
  /-- The selected waiters stay in the list. -/
  | keepSelected
  /-- The returned item's stamp is at the end of the idle stamps. -/
  | backOrder

def leaseExpected (mutation : Mutation) (s : State) (id : Nat) : TermSrc :=
  let r := Pool.Model.lease s id
  let closed := match mutation with
    | .flipReply => !r.2.1
    | _ => r.2.1
  let tb := match mutation with
    | .keepHint => table0
    | _ => table0.set id (var "fresh")
  let leased := match r.2.2 with
    | some it => app "some" [itemTerm it]
    | none => noneT
  app "pair" [tuple [bool closed, leased], stateTerm tb r.1]

def leaseTerm (s : State) (id : Nat) : TermSrc :=
  Pool.leaseStep (var (idName id)) (var "fresh") (stateTerm table0 s)

def leaseAgrees (s : State) (id : Nat) : Verdict :=
  judge (leaseTerm s id) (leaseExpected .exact s id)

def returnExpected (mutation : Mutation) (s : State) (item lease : Nat) : TermSrc :=
  let r := Pool.Model.giveBack s item lease
  let next := match mutation with
    | .backOrder =>
      if r.2.1 then { r.1 with available := s.available ++ [item] } else r.1
    | _ => r.1
  app "pair" [tuple [bool r.2.1, bool r.2.2], stateTerm table0 next]

def returnTerm (s : State) (item lease : Nat) : TermSrc :=
  Pool.returnStep (nat item) (nat lease) (stateTerm table0 s)

def returnAgrees (s : State) (item lease : Nat) : Verdict :=
  judge (returnTerm s item lease) (returnExpected .exact s item lease)

def selectExpected (mutation : Mutation) (s : State) (count : Nat) : TermSrc :=
  let r := Pool.Model.select s count
  let next := match mutation with
    | .keepSelected => s
    | _ => r.1
  app "pair" [listOf (r.2.map (waiterTerm table0)), stateTerm table0 next]

def selectAgrees (s : State) (count : Nat) : Verdict :=
  judge (Pool.selectStep (nat count) (stateTerm table0 s)) (selectExpected .exact s count)

def withdrawAgrees (s : State) (id : Nat) : Verdict :=
  judge (Pool.withdrawStep (var (idName id)) (stateTerm table0 s))
    (app "pair" [unit, stateTerm table0 (Pool.Model.withdraw s id)])

def closeAgrees (s : State) : Verdict :=
  let r := Pool.Model.close s
  judge (Pool.closeStep (stateTerm table0 s))
    (app "pair" [tuple [bool r.2.1, nat r.2.2], stateTerm table0 r.1])

def drainExpected (mutation : Mutation) (s : State) (id : Nat) : TermSrc :=
  let r := Pool.Model.drain s id
  let drained := match mutation with
    | .flipReply => !r.2
    | _ => r.2
  let tb := match mutation with
    | .keepHint => table0
    | _ => table0.set id (var "fresh")
  app "pair" [bool drained, stateTerm tb r.1]

def drainTerm (s : State) (id : Nat) : TermSrc :=
  Pool.drainStep (var (idName id)) (var "fresh") (stateTerm table0 s)

def drainAgrees (s : State) (id : Nat) : Verdict :=
  judge (drainTerm s id) (drainExpected .exact s id)

/-! ## The named controls C1 to C6 -/

/-- One item of the resource 1. The lease 0 holds it, and the requests 1 and 2 wait: the state
of PP3 before H's return. -/
def held : State :=
  { items := [⟨0, 1, true, 0⟩], waiters := [1, 2], next := 1 }

/-- The same state after the return of the lease 0: the item is idle beside two waiters. -/
def premise : State :=
  { items := [⟨0, 1, false, 0⟩], available := [0], waiters := [1, 2], next := 1 }

/-- Two items, both idle, with the item 1 at the front: PP2 after the two returns. -/
def reused : State :=
  { items := [⟨0, 1, false, 0⟩, ⟨1, 2, false, 1⟩], available := [1, 0], next := 2 }

/-- PP2 before B's return: A's item is idle, and the lease 1 holds the item 1. -/
def half : State :=
  { items := [⟨0, 1, false, 0⟩, ⟨1, 2, true, 1⟩], available := [0], next := 2 }

-- C1. A lease where an item is idle takes the front item, at the stamp `next`. With no idle
-- item it enrols at the end, with the step's hint.
#guard (Pool.Model.lease reused 3).2 = (false, some ⟨1, 2, true, 2⟩) &&
  leaseAgrees reused 3 = .agrees
#guard (Pool.Model.lease held 3).2 = (false, none) &&
  (Pool.Model.lease held 3).1.waiters = [1, 2, 3] && leaseAgrees held 3 = .agrees
-- C2. A lease by a request whose entry is present: the entry leaves first. The request 1 takes
-- the idle item at the premise state, and it enrols again, at the end, where none is idle.
#guard (Pool.Model.lease premise 1).1.waiters = [2] && leaseAgrees premise 1 = .agrees
#guard (Pool.Model.lease held 1).1.waiters = [2, 1] && leaseAgrees held 1 = .agrees
-- C3. A lease at a closing pool is refused: its entry leaves, and nothing else changes.
#guard (Pool.Model.lease { premise with closing := true } 1).2 = (true, none) &&
  leaseAgrees { premise with closing := true } 1 = .agrees &&
  leaseAgrees { held with closing := true } 3 = .agrees
-- C4. A return of the lease that holds the item, with a waiter enrolled and with none. A
-- return of a lease that holds nothing: a stale stamp, and an item that the pool has not.
#guard (Pool.Model.giveBack held 0 0).2 = (true, true) && returnAgrees held 0 0 = .agrees
#guard (Pool.Model.giveBack { held with waiters := [] } 0 0).2 = (true, false) &&
  returnAgrees { held with waiters := [] } 0 0 = .agrees
#guard (Pool.Model.giveBack held 0 5).2 = (false, false) && returnAgrees held 0 5 = .agrees
#guard (Pool.Model.giveBack held 3 0).2 = (false, false) && returnAgrees held 3 0 = .agrees
-- C5. The selections of the cases: the count 1, the count 2, a count beyond the list, the
-- count 0, and a selection where nobody waits.
#guard (Pool.Model.select premise 1).2 = [1] && selectAgrees premise 1 = .agrees
#guard (Pool.Model.select premise 2).2 = [1, 2] && selectAgrees premise 2 = .agrees
#guard (Pool.Model.select premise 5).2 = [1, 2] && selectAgrees premise 5 = .agrees
#guard (Pool.Model.select premise 0).2 = [] && selectAgrees premise 0 = .agrees
#guard selectAgrees reused 1 = .agrees
-- C6. The withdrawals, and the close's first step at an open pool and at a closing one.
#guard withdrawAgrees held 2 = .agrees && withdrawAgrees held 3 = .agrees
#guard (Pool.Model.close held).2 = (true, 2) && closeAgrees held = .agrees
#guard (Pool.Model.close { held with closing := true }).2 = (false, 2) &&
  closeAgrees { held with closing := true } = .agrees
-- C7. The closer's step. With a lease outstanding the closer enrols at the end, with the
-- step's hint, and the reply is false. A closer whose entry is present enrols again at the
-- end. With no lease outstanding the reply is true, and the cell stays as it is.
#guard (Pool.Model.drain held 3) = ({ held with waiters := [1, 2, 3] }, false) &&
  drainAgrees held 3 = .agrees
#guard (Pool.Model.drain held 1).1.waiters = [2, 1] && drainAgrees held 1 = .agrees
#guard (Pool.Model.drain premise 3) = (premise, true) && drainAgrees premise 3 = .agrees
#guard (Pool.Model.drain premise 1).1.waiters = [2] && drainAgrees premise 1 = .agrees
#guard drainAgrees { held with closing := true } 3 = .agrees &&
  drainAgrees { premise with closing := true } 3 = .agrees

/-! ## Every state of a finite universe of the profile

The universe: one, two or three items, each idle or borrowed, with each order of the idle
stamps; no waiter, one waiter or two waiters, of the identities 1 and 2 in each order; an open
pool and a closing one. Two items hold one resource in two of the lists, and an idle item
keeps a stale stamp of a last lease in three. The next stamp is 5. -/

inductive Move
  | lease (id : Nat) | giveBack (item lease : Nat) | select (count : Nat) | withdraw (id : Nat)
  | close | drain (id : Nat)
  deriving Repr

def moves : List Move :=
  [.lease 1, .lease 2, .lease 3,
   .giveBack 0 0, .giveBack 0 1, .giveBack 0 3, .giveBack 1 1, .giveBack 1 3, .giveBack 2 0,
   .select 0, .select 1, .select 2, .select 5,
   .withdraw 1, .withdraw 2, .withdraw 3, .close, .drain 1, .drain 3]

def Move.verdict (s : State) : Move → Verdict
  | .lease id => leaseAgrees s id
  | .giveBack item stamp => returnAgrees s item stamp
  | .select count => selectAgrees s count
  | .withdraw id => withdrawAgrees s id
  | .close => closeAgrees s
  | .drain id => drainAgrees s id

def Move.next (s : State) : Move → State
  | .lease id => (Pool.Model.lease s id).1
  | .giveBack item stamp => (Pool.Model.giveBack s item stamp).1
  | .select count => (Pool.Model.select s count).1
  | .withdraw id => Pool.Model.withdraw s id
  | .close => (Pool.Model.close s).1
  | .drain id => (Pool.Model.drain s id).1

/-- The items of the universe, each list with the orders of its idle stamps: 13 pairs. -/
def itemLists : List (List Item × List Nat) :=
  [([⟨0, 7, false, 0⟩], [0]), ([⟨0, 7, false, 4⟩], [0]), ([⟨0, 7, true, 1⟩], []),
   ([⟨0, 7, false, 0⟩, ⟨1, 8, false, 0⟩], [0, 1]), ([⟨0, 7, false, 0⟩, ⟨1, 8, false, 0⟩], [1, 0]),
   ([⟨0, 7, false, 4⟩, ⟨1, 7, false, 4⟩], [0, 1]), ([⟨0, 7, false, 4⟩, ⟨1, 7, false, 4⟩], [1, 0]),
   ([⟨0, 7, true, 1⟩, ⟨1, 8, false, 0⟩], [1]), ([⟨0, 7, false, 2⟩, ⟨1, 8, true, 3⟩], [0]),
   ([⟨0, 7, true, 1⟩, ⟨1, 8, true, 3⟩], []), ([⟨0, 7, true, 3⟩, ⟨1, 7, true, 1⟩], []),
   ([⟨0, 7, true, 1⟩, ⟨1, 8, false, 0⟩, ⟨2, 9, false, 2⟩], [1, 2]),
   ([⟨0, 7, true, 1⟩, ⟨1, 8, false, 0⟩, ⟨2, 9, false, 2⟩], [2, 1])]

/-- The waiter lists of the universe: 5 lists. -/
def waiterLists : List (List Nat) := [[], [1], [2], [1, 2], [2, 1]]

def profileStates : List State :=
  itemLists.flatMap fun (items, available) =>
  waiterLists.flatMap fun waiters =>
  [false, true].map fun closing =>
    ({ items := items, available := available, waiters := waiters, closing := closing,
       next := 5 } : State)

def inProfile (s : State) : Bool := decide (Profile s)

/-- Every state of the universe is of the profile, and each move leaves the profile true: a
finite instance of the proved closure. -/
def closed : Bool :=
  profileStates.all fun s => inProfile s && moves.all fun m => inProfile (m.next s)

/-- The states and moves whose verdict is not `agrees`. -/
def disagreements : List (State × Nat) :=
  profileStates.flatMap fun s => moves.zipIdx.filterMap fun (m, i) =>
    if m.verdict s = .agrees then none else some (s, i)

#guard itemLists.length = 13 && profileStates.length = 130 && moves.length = 19
#guard closed
-- All 2,470 comparisons agree.
#guard disagreements.isEmpty && profileStates.length * moves.length = 2470
-- The universe holds both answers of the closer's step: 70 states with a lease outstanding,
-- and 60 with none.
#guard (profileStates.filter fun s => (Pool.Model.drain s 3).2).length = 60 &&
  (profileStates.filter fun s => !(Pool.Model.drain s 3).2).length = 70
-- The universe holds an idle item beside enrolled waiters at an open pool: 40 such states.
#guard (profileStates.filter fun s =>
  !s.available.isEmpty && !s.waiters.isEmpty && !s.closing).length = 40

/-! ## Outside the profile the comparison still agrees

No step reads the profile: the term and the model compute the same removal by identity, the
same front stamp, the same two passes over the items and the same prefix of the waiters. So a
step goal carries no premise on the state. -/

/-- An idle stamp that names a borrowed item; an idle stamp that names no item; two items of
one stamp; two waiters of one identity; a lease's stamp above the next stamp. -/
def outside : List State :=
  [{ items := [⟨0, 7, true, 1⟩], available := [0], waiters := [1], next := 5 },
   { items := [⟨0, 7, false, 0⟩], available := [9, 0], next := 5 },
   { items := [⟨0, 7, false, 0⟩, ⟨0, 8, true, 1⟩], available := [0], next := 5 },
   { items := [⟨0, 7, true, 1⟩], waiters := [1, 1, 2], next := 5 },
   { items := [⟨0, 7, true, 9⟩, ⟨1, 8, true, 9⟩], next := 5 }]

#guard outside.all fun s => !inProfile s
#guard outside.all fun s => moves.all fun m => m.verdict s = .agrees

/-! ## The red controls M1 to M5: one part of an expected result changed -/

-- M1. C1's expected result with the other first Boolean.
#guard judge (leaseTerm reused 3) (leaseExpected .flipReply reused 3) = .differs
-- M2. A lease that enrols, with the table left as it was: the stored hint is the step's.
#guard judge (leaseTerm held 3) (leaseExpected .keepHint held 3) = .differs
-- A lease that takes an item does not read the table's change.
#guard judge (leaseTerm reused 3) (leaseExpected .keepHint reused 3) = .agrees
-- M3. A selection's expected result with the selected waiters kept in the list.
#guard judge (Pool.selectStep (nat 1) (stateTerm table0 premise))
  (selectExpected .keepSelected premise 1) = .differs
-- M4. A return's expected result with the item's stamp at the end of the idle stamps, on PP2
-- before B's return.
#guard judge (returnTerm half 1 1) (returnExpected .backOrder half 1 1) = .differs
-- With no other idle stamp the two orders are one.
#guard judge (returnTerm held 0 0) (returnExpected .backOrder held 0 0) = .agrees
-- M5. The closer's expected result with the other Boolean, and with the table left as it was
-- where the closer enrols: the stored hint is the step's.
#guard judge (drainTerm held 3) (drainExpected .flipReply held 3) = .differs
#guard judge (drainTerm held 3) (drainExpected .keepHint held 3) = .differs
-- A closer that does not enrol does not read the table's change.
#guard judge (drainTerm premise 3) (drainExpected .keepHint premise 3) = .agrees

/-! ## The faults F1 to F5, as changed step terms

Each fault is red at its own property. The checker types each changed step at the type of the
library's step, so typing alone does not catch it. F1, F2 and F5 are faults of the card's
section 9. F3 is the order of reuse of decisions row 269. F4 is a return that does not name its
lease. The two other faults of a wake in that section are faults of a schedule, and
`Test/Program/PoolContract.lean` and `Test/Program/PoolScenarios.lean` hold them. -/

/-- The checker's type of a source term at a scope, at the native signature. -/
def typeOf (names : List String) (types : List Ty) (src : TermSrc) : Option Ty :=
  typeAt nativeSignature names types src

/-- A field of a step's stored value. -/
def stored (step : TermSrc) (name : String) : Option Val := evalAt (field (tupleAt step 1) name)

/-- The stamps of a step's stored items. -/
def storedStamps (step : TermSrc) : Option Val :=
  evalAt (foldWith (field (tupleAt step 1) "items") (noneOf (field (tupleAt step 1) "available"))
    fun acc it => snoc acc (field it "stamp"))

/-- F1. A return that runs the item's finalizer: the item leaves the pool. -/
def returnFinalizingStep (i l s : TermSrc) : TermSrc :=
  ifT (Pool.heldBy i l s)
    (app "pair" [tuple [bool true, notT (isEmpty (field s "waiters"))],
      recordSet s "items"
        (foldWith (field s "items") (noneOf (field s "items")) fun kept it =>
          ifT (Pool.holdsT i l it) kept (snoc kept it))])
    (app "pair" [tuple [bool false, bool false], s])

-- The property: a return keeps every item (`giveBack_front`, `step_items`). The library's
-- return stores the item, idle at the front. The finalizing return stores no item.
#guard storedStamps (returnTerm held 0 0) = some (.list [.nat 0]) &&
  stored (returnTerm held 0 0) "available" = some (.list [.nat 0])
#guard storedStamps (returnFinalizingStep (nat 0) (nat 0) (stateTerm table0 held)) =
  some (.list [])
#guard judge (returnFinalizingStep (nat 0) (nat 0) (stateTerm table0 held))
  (returnExpected .exact held 0 0) = .differs
-- A return of a lease that holds nothing is the library's return under the fault too.
#guard judge (returnFinalizingStep (nat 0) (nat 5) (stateTerm table0 held))
  (returnExpected .exact held 0 5) = .agrees
-- Typing does not catch it.
#guard decide (typeOf ["i", "l", "s"] [.nat, .nat, Pool.cellTy .nat]
    (returnFinalizingStep (var "i") (var "l") (var "s")) =
  typeOf ["i", "l", "s"] [.nat, .nat, Pool.cellTy .nat]
    (Pool.returnStep (var "i") (var "l") (var "s")))

/-- F2. A wake that hands an item: the selection leases the front idle item for the waiters
that it selects, before any of them runs. -/
def selectHandingStep (count s : TermSrc) : TermSrc :=
  let selected := app "take" [field s "waiters", count]
  let rest := recordSet s "waiters" (app "drop" [field s "waiters", count])
  ifT (andT (notT (isEmpty selected)) (notT (isEmpty (field s "available"))))
    (app "pair" [selected,
      recordSet
        (recordSet (recordSet rest "items" (Pool.marked s)) "available"
          (app "drop" [field s "available", nat 1]))
        "next" (app "add" [field s "next", len selected])])
    (app "pair" [selected, rest])

-- The property: a selection changes the waiters alone (`select_takes_first`). At the premise
-- state the library's selection stores the idle stamp as it was. The handing selection stores
-- no idle stamp: the item is not idle after it.
#guard stored (Pool.selectStep (nat 1) (stateTerm table0 premise)) "available" =
  some (.list [.nat 0])
#guard stored (selectHandingStep (nat 1) (stateTerm table0 premise)) "available" =
  some (.list [])
#guard judge (selectHandingStep (nat 2) (stateTerm table0 premise))
  (selectExpected .exact premise 2) = .differs
-- With no idle item, or with nobody selected, the handing selection is the library's.
#guard judge (selectHandingStep (nat 2) (stateTerm table0 held)) (selectExpected .exact held 2) =
  .agrees
#guard judge (selectHandingStep (nat 0) (stateTerm table0 premise))
  (selectExpected .exact premise 0) = .agrees
-- Over the universe it differs exactly where a waiter is selected beside an idle item.
#guard profileStates.all fun s => [0, 1, 2, 5].all fun count =>
  (judge (selectHandingStep (nat count) (stateTerm table0 s)) (selectExpected .exact s count)
      != .agrees) ==
    (!(Pool.Model.select s count).2.isEmpty && !s.available.isEmpty)
-- Typing does not catch it.
#guard decide (typeOf ["count", "s"] [.nat, Pool.cellTy .nat]
    (selectHandingStep (var "count") (var "s")) =
  typeOf ["count", "s"] [.nat, Pool.cellTy .nat] (Pool.selectStep (var "count") (var "s")))

/-- F3. A return that puts its item at the end of the idle stamps: rc.112's order. -/
def returnBackStep (i l s : TermSrc) : TermSrc :=
  ifT (Pool.heldBy i l s)
    (app "pair" [tuple [bool true, notT (isEmpty (field s "waiters"))],
      recordSet (recordSet s "items" (Pool.freed i l s)) "available"
        (snoc (field s "available") i)])
    (app "pair" [tuple [bool false, bool false], s])

-- The property: a returned item joins the front (decisions row 269, `giveBack_front`). The
-- library's return stores `[1, 0]`, and the changed return stores `[0, 1]`.
#guard stored (returnTerm half 1 1) "available" = some (.list [.nat 1, .nat 0])
#guard stored (returnBackStep (nat 1) (nat 1) (stateTerm table0 half)) "available" =
  some (.list [.nat 0, .nat 1])
#guard judge (returnBackStep (nat 1) (nat 1) (stateTerm table0 half))
  (returnExpected .exact half 1 1) = .differs
-- Typing does not catch it.
#guard decide (typeOf ["i", "l", "s"] [.nat, .nat, Pool.cellTy .nat]
    (returnBackStep (var "i") (var "l") (var "s")) =
  typeOf ["i", "l", "s"] [.nat, .nat, Pool.cellTy .nat]
    (Pool.returnStep (var "i") (var "l") (var "s")))

/-- F4. A return that does not name its lease: it frees the item whenever a lease holds it. -/
def returnUncheckedStep (i _l s : TermSrc) : TermSrc :=
  let holds := fun it => andT (app "eq" [field it "stamp", i]) (field it "borrowed")
  ifT (foldWith (field s "items") (bool false) fun found it => orT found (holds it))
    (app "pair" [tuple [bool true, notT (isEmpty (field s "waiters"))],
      recordSet
        (recordSet s "items"
          (foldWith (field s "items") (noneOf (field s "items")) fun out it =>
            snoc out (ifT (holds it) (recordSet it "borrowed" (bool false)) it)))
        "available" (front i (field s "available"))])
    (app "pair" [tuple [bool false, bool false], s])

/-- The item was leased again, at the stamp 1, after the lease 0 returned. -/
def again : State := { items := [⟨0, 1, true, 1⟩], next := 2 }

-- The property: a stale lease frees no item that was leased again (`giveBack_once`, and the
-- frame of a return that holds nothing). The library's return of the stale lease 0 answers
-- `[false, false]`, and the lease 1 still holds the item. The unchecked return frees it.
#guard (Pool.Model.giveBack again 0 0) = (again, false, false) && returnAgrees again 0 0 = .agrees
#guard stored (returnTerm again 0 0) "available" = some (.list [])
#guard stored (returnUncheckedStep (nat 0) (nat 0) (stateTerm table0 again)) "available" =
  some (.list [.nat 0])
#guard judge (returnUncheckedStep (nat 0) (nat 0) (stateTerm table0 again))
  (returnExpected .exact again 0 0) = .differs
-- The return of the lease that holds the item is the library's under the fault too.
#guard judge (returnUncheckedStep (nat 0) (nat 1) (stateTerm table0 again))
  (returnExpected .exact again 0 1) = .agrees
-- Typing does not catch it.
#guard decide (typeOf ["i", "l", "s"] [.nat, .nat, Pool.cellTy .nat]
    (returnUncheckedStep (var "i") (var "l") (var "s")) =
  typeOf ["i", "l", "s"] [.nat, .nat, Pool.cellTy .nat]
    (Pool.returnStep (var "i") (var "l") (var "s")))

/-- F5. A closer that answers at once: the close that does not wait. -/
def drainAtOnceStep (id _hint s : TermSrc) : TermSrc :=
  app "pair" [bool true, Pool.withdrawn id s]

-- The property: the closer's step answers true only where no lease is outstanding
-- (`drain_waits`). At the held state the library's step answers false, and it stores the
-- closer's entry. The changed step answers true while the lease 0 is outstanding.
#guard evalAt (tupleAt (drainTerm held 3) 0) = some (.bool false) &&
  evalAt (len (field (tupleAt (drainTerm held 3) 1) "waiters")) = some (.nat 3)
#guard evalAt (tupleAt (drainAtOnceStep (var (idName 3)) (var "fresh") (stateTerm table0 held)) 0) =
  some (.bool true)
#guard judge (drainAtOnceStep (var (idName 3)) (var "fresh") (stateTerm table0 held))
  (drainExpected .exact held 3) = .differs
-- Over the universe it differs exactly where a lease is outstanding.
#guard profileStates.all fun s => [1, 3].all fun id =>
  (judge (drainAtOnceStep (var (idName id)) (var "fresh") (stateTerm table0 s))
      (drainExpected .exact s id) != .agrees) == !(Pool.Model.drain s id).2
-- Typing does not catch it.
#guard decide (typeOf ["id", "hint", "s"] [idTy, idTy, Pool.cellTy .nat]
    (drainAtOnceStep (var "id") (var "hint") (var "s")) =
  typeOf ["id", "hint", "s"] [idTy, idTy, Pool.cellTy .nat]
    (Pool.drainStep (var "id") (var "hint") (var "s")))

end Test.Program.PoolAgreement
