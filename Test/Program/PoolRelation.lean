import Effect4.Laws.Modules.Pool.Steps
import Effect4.Laws.Modules.Store
import Test.Program.PoolAgreement
import Test.Program.PoolSteps

/-!
# Pool's relation and its step goals: finite controls (decisions rows 267 to 269 and 276)

The relation is `src/Effect4/Laws/Modules/Pool/Relation.lean`: the shared encoding table, the
resources' values, the cell's value and the replies. The six step goals are in
`src/Effect4/Laws/Modules/Pool/Steps.lean`. This battery evaluates each goal's conclusion, as
the goal states it: at one table and at the scope of the step's own arguments, on every state
of the universe of `Test/Program/PoolAgreement.lean`, 19 moves on each.

It also ties the two encodings: the cell's value of the relation is the value of the
comparison's state term. The red controls drop one premise each: the table's injectivity, and
the hint that a lease sets. Two more sections apply the statements: joined to the store by the
shared connector `step_updates`, and at the scope of a row of `Ref.modifyWith` under three
names that `bindWith` minted.

Placement. Each guard is a finite instance of a step goal (concept `translation-simulation`,
requirement R10, a part of the proposed claim `pool-expansion-agrees`). A state outside the
universe and another table are not checked.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Test.Program.PoolRelation

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Modules
open Effect4.Pool.Model
open Test.Program.PoolAgreement (profileStates outside moves Move held premise reused half again)
open Test.Program.PoolSteps (poolName idName hintName currentName stepScope stepScope_id
  stepScope_hint stepScope_cell)

/-! ## One table -/

/-- The comparison's table: request `n` has the identity handle `n` and the hint `1000 + n`. -/
def tb0 : Table := { handle := fun n => ⟨n⟩, hint := fun n => ⟨1000 + n⟩ }

/-- The comparison's resources: the model resource `r` has the value `100 + r`. -/
def res0 : Nat → Val := fun r => Val.nat (100 + r)

/-- The hint that a lease receives. -/
def fresh : DeferredKey := ⟨9999⟩

-- The relation's cell value is the value of the comparison's state term, on every state of
-- the universe and on the states outside the profile: the two encodings are one.
#guard (profileStates ++ outside).all fun s =>
  decide (PoolAgreement.evalAt (PoolAgreement.stateTerm PoolAgreement.table0 s) =
    some (cellVal tb0 res0 s))
-- The initial value at its resources is the cell's value of the model's initial state.
#guard [[7], [7, 8], [7, 7, 9]].all fun (resources : List Nat) =>
  decide ((Pool.initial .nat (resources.map fun r => nat (100 + r)) {} []).toOption.bind
      (evalTerm []) =
    some (cellVal tb0 res0 (initial resources)))

/-! ## A goal's conclusion, decided -/

/-- `Reads` at a scope of names, decided: the source elaborates, and its tree has the value. -/
def readsAt (names : List String) (vals : List Val) (src : TermSrc) (v : Val) : Bool :=
  decide ((src { names := names } []).toOption.bind (evalTerm vals) = some v)

/-- The conclusion of `leaseStep_agrees`, at the table `tb` and the step's own scope. -/
def leaseHolds (tb : Table) (s : State) (id : Nat) : Bool :=
  readsAt ["id", "hint", "s"] [Val.promise (tb.handle id), Val.promise fresh, cellVal tb res0 s]
    (Pool.leaseStep (var "id") (var "hint") (var "s"))
    (Val.tuple [leaseReplyVal res0 (lease s id).2, cellVal (tb.renew id fresh) res0 (lease s id).1])

/-- The conclusion of `returnStep_agrees`. -/
def returnHolds (tb : Table) (s : State) (item stamp : Nat) : Bool :=
  readsAt ["item", "lease", "s"] [Val.nat item, Val.nat stamp, cellVal tb res0 s]
    (Pool.returnStep (var "item") (var "lease") (var "s"))
    (Val.tuple [returnReplyVal (giveBack s item stamp).2, cellVal tb res0 (giveBack s item stamp).1])

/-- The conclusion of `selectStep_agrees`. -/
def selectHolds (tb : Table) (s : State) (count : Nat) : Bool :=
  readsAt ["count", "s"] [Val.nat count, cellVal tb res0 s]
    (Pool.selectStep (var "count") (var "s"))
    (Val.tuple [selectReplyVal tb (select s count).2, cellVal tb res0 (select s count).1])

/-- The conclusion of `withdrawStep_agrees`. -/
def withdrawHolds (tb : Table) (s : State) (id : Nat) : Bool :=
  readsAt ["id", "s"] [Val.promise (tb.handle id), cellVal tb res0 s]
    (Pool.withdrawStep (var "id") (var "s"))
    (Val.tuple [Val.unit, cellVal tb res0 (withdraw s id)])

/-- The conclusion of `closeStep_agrees`. -/
def closeHolds (tb : Table) (s : State) : Bool :=
  readsAt ["s"] [cellVal tb res0 s] (Pool.closeStep (var "s"))
    (Val.tuple [closeReplyVal (close s).2, cellVal tb res0 (close s).1])

/-- The conclusion of `drainStep_agrees`, at the table `tb` and the step's own scope. -/
def drainHolds (tb : Table) (s : State) (id : Nat) : Bool :=
  readsAt ["id", "hint", "s"] [Val.promise (tb.handle id), Val.promise fresh, cellVal tb res0 s]
    (Pool.drainStep (var "id") (var "hint") (var "s"))
    (Val.tuple [Val.bool (drain s id).2, cellVal (tb.renew id fresh) res0 (drain s id).1])

/-- One move's goal, at a table. -/
def holds (tb : Table) (s : State) : Move → Bool
  | .lease id => leaseHolds tb s id
  | .giveBack item stamp => returnHolds tb s item stamp
  | .select count => selectHolds tb s count
  | .withdraw id => withdrawHolds tb s id
  | .close => closeHolds tb s
  | .drain id => drainHolds tb s id

/-! ## The named controls, and every state of the universe -/

-- A lease that enrols: the stored value is the model's state through the table that holds the
-- step's hint at the request. A lease by a request whose entry is present: the entry leaves.
#guard leaseHolds tb0 held 3 && leaseHolds tb0 held 1 && leaseHolds tb0 premise 1
#guard cellVal (tb0.renew 1 fresh) res0 (lease held 1).1 ≠ cellVal tb0 res0 (lease held 1).1
-- A lease that takes an item leaves no entry of its request, so the table's change is not
-- read. Its reply holds the item's record as its lease holds it.
#guard cellVal (tb0.renew 1 fresh) res0 (lease premise 1).1 = cellVal tb0 res0 (lease premise 1).1
#guard leaseReplyVal res0 (lease reused 3).2 =
  Val.tuple [.bool false, Store.Val.some (itemOf (.bool true) (.nat 2) (.nat 102) (.nat 1))]
-- The selections of the cases: the reply is the selected waiters' records, each with its
-- identity and its hint, in the order of enrolment.
#guard selectHolds tb0 premise 1 && selectHolds tb0 premise 2 && selectHolds tb0 premise 5
#guard selectReplyVal tb0 (select premise 2).2 =
  Val.list [waiterOf (Val.promise ⟨1001⟩) (Val.promise ⟨1⟩),
    waiterOf (Val.promise ⟨1002⟩) (Val.promise ⟨2⟩)]
-- The return of the lease that holds the item, the stale return, the withdrawal and the
-- close's first step.
#guard returnHolds tb0 held 0 0 && returnHolds tb0 again 0 0 && returnHolds tb0 half 1 1 &&
  withdrawHolds tb0 held 2 && closeHolds tb0 held
-- The closer's step. Where it enrols the closer, the stored value is the model's state through
-- the table that holds the step's hint at the closer. Where it does not, no entry of the
-- closer stays, so the table's change is not read.
#guard drainHolds tb0 held 3 && drainHolds tb0 held 1 && drainHolds tb0 premise 3
#guard cellVal (tb0.renew 3 fresh) res0 (drain held 3).1 ≠ cellVal tb0 res0 (drain held 3).1
#guard cellVal (tb0.renew 3 fresh) res0 (drain premise 3).1 = cellVal tb0 res0 (drain premise 3).1

-- Every state of the universe, 19 moves on each: each goal's conclusion holds. It holds on
-- the states outside the profile too.
#guard profileStates.all fun s => moves.all fun m => holds tb0 s m
#guard outside.all fun s => moves.all fun m => holds tb0 s m
#guard profileStates.length * moves.length = 2470

/-! ## Red controls: one premise dropped -/

/-- A table that is not injective: the requests 1 and 2 share one handle. -/
def shared : Table := { tb0 with handle := fun n => if n = 2 then ⟨1⟩ else ⟨n⟩ }

-- The premise of injectivity. Under the shared handle a withdrawal of request 2 removes
-- request 1's entry too, and the conclusion fails. So does a lease by request 2.
#guard !withdrawHolds shared held 2 && withdrawHolds tb0 held 2
#guard !leaseHolds shared held 2 && leaseHolds tb0 held 2
#guard !drainHolds shared held 2 && drainHolds tb0 held 2
-- A step that tests no identity does not read the premise: the selection, the return and the
-- close's first step hold under the shared handle.
#guard selectHolds shared held 1 && returnHolds shared held 0 0 && closeHolds shared held
-- The hint that a lease sets. With the table left as it was, the conclusion of a lease that
-- enrols fails: the stored hint is the step's.
#guard !readsAt ["id", "hint", "s"]
    [Val.promise (tb0.handle 3), Val.promise fresh, cellVal tb0 res0 held]
    (Pool.leaseStep (var "id") (var "hint") (var "s"))
    (Val.tuple [leaseReplyVal res0 (lease held 3).2, cellVal tb0 res0 (lease held 3).1])
-- The hint that the closer's step sets, in the same way.
#guard !readsAt ["id", "hint", "s"]
    [Val.promise (tb0.handle 3), Val.promise fresh, cellVal tb0 res0 held]
    (Pool.drainStep (var "id") (var "hint") (var "s"))
    (Val.tuple [Val.bool (drain held 3).2, cellVal tb0 res0 (drain held 3).1])
-- The selected identities. A selection's reply through another table is no conclusion.
#guard !readsAt ["count", "s"] [Val.nat 1, cellVal tb0 res0 premise]
    (Pool.selectStep (var "count") (var "s"))
    (Val.tuple [selectReplyVal (tb0.renew 1 fresh) (select premise 1).2,
      cellVal tb0 res0 (select premise 1).1])
-- The resources' values. A lease's reply through another map of the resources is no
-- conclusion.
#guard !readsAt ["id", "hint", "s"]
    [Val.promise (tb0.handle 3), Val.promise fresh, cellVal tb0 res0 reused]
    (Pool.leaseStep (var "id") (var "hint") (var "s"))
    (Val.tuple [leaseReplyVal (fun r => Val.nat r) (lease reused 3).2,
      cellVal (tb0.renew 3 fresh) res0 (lease reused 3).1])

/-! ## The goals at the scope of a step's own arguments, joined to the store

A step statement holds at every scope, for every caller's term that reads the step's
arguments. A variable that an author wrote is such a term (`captured_var`). With `step_updates`
(`src/Effect4/Laws/Modules/Store.lean`) a statement is one atomic update of the cell: the
store step reads the cell once, answers the model's reply and writes the model's next state.
The row's binder for the cell's value is the scope's last name. -/

/-- **One `Ref.modify` of the selection step is the model's selection**, at the scope of a
count and the cell's value. The reply names the selected identities. -/
theorem select_updates (tb : Table) (res : Nat → Val) (s : State) (count : Nat) {stores : Stores}
    {q : RefKey} (held : refPeek stores.refs q = some (cellVal tb res s)) :
    ∃ f, Pool.selectStep (var "count") (var "s") { names := ["count", "s"] } [] = .ok f ∧
      syncOpStep (.refModify q f [Val.nat count]) stores =
        some ({ stores with refs := refPoke stores.refs q (cellVal tb res (select s count).1) },
          selectReplyVal tb (select s count).2) :=
  step_updates (env := { names := ["count"] }) (current := "s") (captured := [Val.nat count]) held
    (selectStep_agrees tb res s count (captured_var (x := "count") rfl rfl rfl).atScope
      (captured_var (x := "s") rfl rfl rfl).atScope)

/-- **One `Ref.modify` of the return step is the model's return**: the two stamps are author's
variables, so each is a caller's term under the return's folds. -/
theorem return_updates (tb : Table) (res : Nat → Val) (s : State) (item stamp : Nat)
    {stores : Stores} {q : RefKey} (held : refPeek stores.refs q = some (cellVal tb res s)) :
    ∃ f, Pool.returnStep (var "item") (var "lease") (var "s")
        { names := ["item", "lease", "s"] } [] = .ok f ∧
      syncOpStep (.refModify q f [Val.nat item, Val.nat stamp]) stores =
        some ({ stores with
            refs := refPoke stores.refs q (cellVal tb res (giveBack s item stamp).1) },
          returnReplyVal (giveBack s item stamp).2) :=
  step_updates (env := { names := ["item", "lease"] }) (current := "s")
    (captured := [Val.nat item, Val.nat stamp]) held
    (returnStep_agrees tb res s item stamp rfl (captured_var (x := "item") rfl rfl rfl)
      (captured_var (x := "lease") rfl rfl rfl) (captured_var (x := "s") rfl rfl rfl).atScope)

/-- **One `Ref.modify` of the lease step is the model's lease**, through the table that holds
the step's hint at the request. The row's binder is an author's variable here, so it is a
caller's term under the lease's folds. -/
theorem lease_updates (tb : Table) (res : Nat → Val) (s : State) (id : Nat) (hint : DeferredKey)
    (injective : tb.Injective) {stores : Stores} {q : RefKey}
    (held : refPeek stores.refs q = some (cellVal tb res s)) :
    ∃ f, Pool.leaseStep (var "id") (var "hint") (var "s") { names := ["id", "hint", "s"] } [] =
        .ok f ∧
      syncOpStep (.refModify q f [Val.promise (tb.handle id), Val.promise hint]) stores =
        some ({ stores with
            refs := refPoke stores.refs q (cellVal (tb.renew id hint) res (lease s id).1) },
          leaseReplyVal res (lease s id).2) :=
  step_updates (env := { names := ["id", "hint"] }) (current := "s")
    (captured := [Val.promise (tb.handle id), Val.promise hint]) held
    (leaseStep_agrees tb res s id hint injective rfl (captured_var (x := "id") rfl rfl rfl)
      (captured_var (x := "hint") rfl rfl rfl).atScope (captured_var (x := "s") rfl rfl rfl))

/-- **One `Ref.modify` of the closer's step is the model's `drain`**, through the table that
holds the step's hint at the closer. -/
theorem drain_updates (tb : Table) (res : Nat → Val) (s : State) (id : Nat) (hint : DeferredKey)
    (injective : tb.Injective) {stores : Stores} {q : RefKey}
    (held : refPeek stores.refs q = some (cellVal tb res s)) :
    ∃ f, Pool.drainStep (var "id") (var "hint") (var "s") { names := ["id", "hint", "s"] } [] =
        .ok f ∧
      syncOpStep (.refModify q f [Val.promise (tb.handle id), Val.promise hint]) stores =
        some ({ stores with
            refs := refPoke stores.refs q (cellVal (tb.renew id hint) res (drain s id).1) },
          Val.bool (drain s id).2) :=
  step_updates (env := { names := ["id", "hint"] }) (current := "s")
    (captured := [Val.promise (tb.handle id), Val.promise hint]) held
    (drainStep_agrees tb res s id hint injective rfl (captured_var (x := "id") rfl rfl rfl)
      (captured_var (x := "hint") rfl rfl rfl).atScope
      (captured_var (x := "s") rfl rfl rfl).atScope)

/-! ## The lease step in a row of `Ref.modifyWith`

The scope is `Test/Program/PoolSteps.lean`'s: the pool's handle, the identity and the hint under
three names that `bindWith` minted, and the cell's current value under the row's own minted
binder. `captured_answer` gives the capture of the identity, and `captured_minted` the capture
of the cell's own source. No `Captured` is assumed. -/

/-- The lease step at a row's scope: every caller's term is a minted name, and each goes under
the step's folds. -/
example (tb : Table) (res : Nat → Val) (s : State) (id : Nat) (hint : DeferredKey)
    (injective : tb.Injective) (pool : Val) :
    Reads (Pool.leaseStep (minted idName) (minted hintName) (minted currentName)) stepScope []
      [pool, Val.promise (tb.handle id), Val.promise hint, cellVal tb res s]
      (Val.tuple [leaseReplyVal res (lease s id).2,
        cellVal (tb.renew id hint) res (lease s id).1]) :=
  leaseStep_agrees tb res s id hint injective rfl
    (captured_answer (outer := { names := [poolName] }) stepScope_id rfl)
    ⟨.var 2, minted_tree stepScope_hint [], rfl⟩
    (captured_minted stepScope_cell rfl
      (mint_ne_of_head (b := 97) (c := 99) (by decide) (by decide) (by decide) _ _)
      (mint_ne_of_head (b := 105) (c := 99) (by decide) (by decide) (by decide) _ _))

end Test.Program.PoolRelation
