import Effect4.Laws.Modules.Semaphore.Steps
import Test.Program.SemaphoreAgreement
import ProofGraph.Plan

/-!
# Semaphore's relation and its step goals: finite controls (decisions row 265)

The relation is `src/Effect4/Laws/Modules/Semaphore/Relation.lean`: the Queue's encoding table,
the cell's value and the replies. The five step goals are in
`src/Effect4/Laws/Modules/Semaphore/Steps.lean`. This battery evaluates each goal's conclusion,
as the goal states it: at one table and at the scope of the step's own arguments, on every
state of the universe of `Test/Program/SemaphoreAgreement.lean`, 23 moves on each.

It also ties the two encodings: the cell's value of the relation is the value of the
comparison's state term. The red controls drop one premise each: the table's injectivity, and
the hint that a take sets. The last section joins a goal to the store by the Queue's
connector, `step_updates`.

Placement. Each guard is a finite instance of a step goal (concept `translation-simulation`,
requirement R10, a part of the proposed claim `semaphore-expansion-agrees`). A state outside
the universe and another table are not checked.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Test.Program.SemaphoreRelation

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Queue.Model (Table Reads Captured captured_var step_updates)
open Effect4.Semaphore.Model
open Test.Program.SemaphoreAgreement (profileStates outside moves Move held freed scan)

/-! ## One table -/

/-- The comparison's table: request `n` has the identity handle `n` and the hint `1000 + n`. -/
def tb0 : Table := { handle := fun n => ⟨n⟩, hint := fun n => ⟨1000 + n⟩ }

/-- The hint that a take receives. -/
def fresh : DeferredKey := ⟨9999⟩

-- The relation's cell value is the value of the comparison's state term, on every state of
-- the universe and on the states outside the profile: the two encodings are one.
#guard (profileStates ++ outside).all fun s =>
  decide (SemaphoreAgreement.evalAt (SemaphoreAgreement.stateTerm SemaphoreAgreement.table0 s) =
    some (cellVal tb0 s))
-- The initial value at a total is the cell's value of the model's initial state.
#guard [1, 2, 7].all fun permits =>
  decide ((Semaphore.empty permits {} []).toOption.bind (evalTerm []) =
    some (cellVal tb0 (initial permits)))

/-! ## A goal's conclusion, decided -/

/-- `Reads` at a scope of names, decided: the source elaborates, and its tree has the value. -/
def readsAt (names : List String) (vals : List Val) (src : TermSrc) (v : Val) : Bool :=
  decide ((src { names := names } []).toOption.bind (evalTerm vals) = some v)

/-- The conclusion of `takeStep_agrees`, at the table `tb` and the step's own scope. -/
def takeHolds (tb : Table) (s : State) (id n : Nat) : Bool :=
  readsAt ["need", "id", "hint", "s"]
    [Val.nat n, Val.promise (tb.handle id), Val.promise fresh, cellVal tb s]
    (Semaphore.takeStep (var "need") (var "id") (var "hint") (var "s"))
    (Val.tuple [Val.bool (take s id n).2, cellVal (tb.renew id fresh) (take s id n).1])

/-- The conclusion of `takeIfAvailableStep_agrees`. -/
def takeIfAvailableHolds (tb : Table) (s : State) (n : Nat) : Bool :=
  readsAt ["need", "s"] [Val.nat n, cellVal tb s]
    (Semaphore.takeIfAvailableStep (var "need") (var "s"))
    (Val.tuple [Val.bool (takeIfAvailable s n).2, cellVal tb (takeIfAvailable s n).1])

/-- The conclusion of `releaseStep_agrees`. -/
def releaseHolds (tb : Table) (s : State) (n : Nat) : Bool :=
  readsAt ["count", "s"] [Val.nat n, cellVal tb s]
    (Semaphore.releaseStep (var "count") (var "s"))
    (Val.tuple [releaseReplyVal (release s n).2, cellVal tb (release s n).1])

/-- The conclusion of `visitStep_agrees`. -/
def visitHolds (tb : Table) (s : State) (cursor : Nat) : Bool :=
  readsAt ["cursor", "s"] [Val.nat cursor, cellVal tb s]
    (Semaphore.visitStep (var "cursor") (var "s"))
    (Val.tuple [visitReplyVal tb (visit s cursor).2, cellVal tb (visit s cursor).1])

/-- The conclusion of `withdrawStep_agrees`. -/
def withdrawHolds (tb : Table) (s : State) (id : Nat) : Bool :=
  readsAt ["id", "s"] [Val.promise (tb.handle id), cellVal tb s]
    (Semaphore.withdrawStep (var "id") (var "s"))
    (Val.tuple [Val.unit, cellVal tb (withdraw s id)])

/-- One move's goal, at a table. -/
def holds (tb : Table) (s : State) : Move → Bool
  | .take id n => takeHolds tb s id n
  | .takeIfAvailable n => takeIfAvailableHolds tb s n
  | .release n => releaseHolds tb s n
  | .visit cursor => visitHolds tb s cursor
  | .withdraw id => withdrawHolds tb s id

/-! ## The named controls, and every state of the universe -/

-- A take that enrols: the stored value is the model's state through the table that holds the
-- step's hint at the request. A take by a request whose entry is present: the entry leaves.
#guard takeHolds tb0 held 1 1 && takeHolds tb0 held 2 2 && takeHolds tb0 freed 2 2
#guard cellVal (tb0.renew 2 fresh) (take held 2 2).1 ≠ cellVal tb0 (take held 2 2).1
-- A take that takes leaves no entry of its request, so the table's change is not read.
#guard cellVal (tb0.renew 2 fresh) (take freed 2 2).1 = cellVal tb0 (take freed 2 2).1
-- The visits of the cases: the reply is the selected waiter's record, with its hint.
#guard visitHolds tb0 freed 0 && visitHolds tb0 scan 0 && visitHolds tb0 held 0
#guard visitReplyVal tb0 (visit scan 0).2 =
  Store.Val.some (waiterOf (Val.promise ⟨1003⟩) (Val.promise ⟨3⟩) (.nat 1) (.nat 1))
-- The release, the take that never waits, and the withdrawal.
#guard releaseHolds tb0 held 2 && releaseHolds tb0 held 5 && takeIfAvailableHolds tb0 freed 2 &&
  withdrawHolds tb0 held 2

-- Every state of the universe, 23 moves on each: each goal's conclusion holds. It holds on
-- the states outside the profile too.
#guard profileStates.all fun s => moves.all fun m => holds tb0 s m
#guard outside.all fun s => moves.all fun m => holds tb0 s m
#guard profileStates.length * moves.length = 5175

/-! ## Red controls: one premise dropped -/

/-- A table that is not injective: the requests 1 and 2 share one handle. -/
def shared : Table := { tb0 with handle := fun n => if n = 2 then ⟨1⟩ else ⟨n⟩ }

/-- The requests 1 and 2 both wait. -/
def both : State := { permits := 2, taken := 2, waiters := [⟨1, 1, 1⟩, ⟨2, 1, 3⟩], next := 5 }

-- The premise of injectivity. Under the shared handle a withdrawal of request 2 removes
-- request 1's entry too, and the conclusion fails. So does a take by request 2.
#guard !withdrawHolds shared both 2 && withdrawHolds tb0 both 2
#guard !takeHolds shared both 2 1 && takeHolds tb0 both 2 1
-- A step that tests no identity does not read the premise.
#guard visitHolds shared both 0 && releaseHolds shared both 1
-- The hint that a take sets. With the table left as it was, the conclusion of a take that
-- enrols fails: the stored hint is the step's.
#guard !readsAt ["need", "id", "hint", "s"]
    [Val.nat 2, Val.promise (tb0.handle 2), Val.promise fresh, cellVal tb0 held]
    (Semaphore.takeStep (var "need") (var "id") (var "hint") (var "s"))
    (Val.tuple [Val.bool false, cellVal tb0 (take held 2 2).1])
-- The selected identity. A visit's reply through another table is no conclusion.
#guard !readsAt ["cursor", "s"] [Val.nat 0, cellVal tb0 scan]
    (Semaphore.visitStep (var "cursor") (var "s"))
    (Val.tuple [visitReplyVal (tb0.renew 3 fresh) (visit scan 0).2, cellVal tb0 (visit scan 0).1])

/-! ## The goals at the scope of a step's own arguments, joined to the store

A step statement holds at every scope, for every caller's term that reads the step's
arguments. A variable that an author wrote is such a term (`captured_var`). With `step_updates`
(`src/Effect4/Laws/Modules/Queue/Steps.lean`) a statement is one atomic update of the cell: the
store step reads the cell once, answers the model's reply and writes the model's next state.
The row's binder for the cell's value is the scope's last name. -/

/-- **One `Ref.modify` of the release step is the model's release**, at the scope of a count
and the cell's value. -/
theorem release_updates (tb : Table) (s : State) (n : Nat) {stores : Stores} {q : RefKey}
    (held : refPeek stores.refs q = some (cellVal tb s)) :
    ∃ f, Semaphore.releaseStep (var "count") (var "s") { names := ["count", "s"] } [] = .ok f ∧
      syncOpStep (.refModify q f [Val.nat n]) stores =
        some ({ stores with refs := refPoke stores.refs q (cellVal tb (release s n).1) },
          releaseReplyVal (release s n).2) :=
  step_updates (env := { names := ["count"] }) (current := "s") (captured := [Val.nat n]) held
    (releaseStep_agrees tb s n (captured_var (x := "count") rfl rfl rfl).atScope
      (captured_var (x := "s") rfl rfl rfl).atScope)

/-- **One `Ref.modify` of the visit step is the model's visit**: the cursor and the row's
binder are author's variables, so each is a caller's term under the visit's fold. -/
theorem visit_updates (tb : Table) (s : State) (cursor : Nat) {stores : Stores} {q : RefKey}
    (held : refPeek stores.refs q = some (cellVal tb s)) :
    ∃ f, Semaphore.visitStep (var "cursor") (var "s") { names := ["cursor", "s"] } [] = .ok f ∧
      syncOpStep (.refModify q f [Val.nat cursor]) stores =
        some ({ stores with refs := refPoke stores.refs q (cellVal tb (visit s cursor).1) },
          visitReplyVal tb (visit s cursor).2) :=
  step_updates (env := { names := ["cursor"] }) (current := "s") (captured := [Val.nat cursor])
    held
    (visitStep_agrees tb s cursor rfl (captured_var (x := "cursor") rfl rfl rfl)
      (captured_var (x := "s") rfl rfl rfl))

/-- **One `Ref.modify` of the take step is the model's take**, through the table that holds the
step's hint at the request. -/
theorem take_updates (tb : Table) (s : State) (id n : Nat) (hint : DeferredKey)
    (injective : tb.Injective) {stores : Stores} {q : RefKey}
    (held : refPeek stores.refs q = some (cellVal tb s)) :
    ∃ f, Semaphore.takeStep (var "need") (var "id") (var "hint") (var "s")
        { names := ["need", "id", "hint", "s"] } [] = .ok f ∧
      syncOpStep
          (.refModify q f [Val.nat n, Val.promise (tb.handle id), Val.promise hint]) stores =
        some ({ stores with
            refs := refPoke stores.refs q (cellVal (tb.renew id hint) (take s id n).1) },
          Val.bool (take s id n).2) :=
  step_updates (env := { names := ["need", "id", "hint"] }) (current := "s")
    (captured := [Val.nat n, Val.promise (tb.handle id), Val.promise hint]) held
    (takeStep_agrees tb s id n hint injective rfl
      (captured_var (x := "need") rfl rfl rfl).atScope (captured_var (x := "id") rfl rfl rfl)
      (captured_var (x := "hint") rfl rfl rfl).atScope
      (captured_var (x := "s") rfl rfl rfl).atScope)

end Test.Program.SemaphoreRelation
