import Effect4.Laws.Modules.Pool.Reading
import Effect4.Laws.Auto.Obligations
import Effect4.Laws.Auto.Semantics

/-!
# Pool's six steps agree with the abstract model: the step goals (rows 267 to 269 and 276)

Each step term of `src/Effect4/Modules/Pool/Steps.lean` has one statement here. From a cell
that holds a model state through the table, the step reads the tuple of the model's reply and
the model's next state through the table. The relation is in
`src/Effect4/Laws/Modules/Pool/Relation.lean`.

| Goal | The model's transition | Premises beside the readings |
| --- | --- | --- |
| `leaseStep_agrees` | `lease` | an injective table; the identity and the cell's source kept under a fold |
| `returnStep_agrees` | `giveBack` | the item's stamp and the lease's stamp kept under a fold |
| `selectStep_agrees` | `select` | none: the step folds nothing, and it tests no identity |
| `withdrawStep_agrees` | `withdraw` | an injective table; the identity kept under a fold |
| `closeStep_agrees` | `close` | none |
| `drainStep_agrees` | `drain` | an injective table; the identity kept under a fold |

Placement. Concept `translation-simulation`. Requirement R10, as parts of the proposed claim
`pool-expansion-agrees`. The consumer of each goal is the public law, in the slice of the
public operations. Reach, for each goal:

- the domain is every model state: no goal takes the profile as a premise, because no step
  reads it. The profile's closure is a statement of its own
  (`src/Effect4/Laws/Modules/Pool/Profile.lean`);
- the table's injectivity is a written premise where a step tests an identity, and the hint
  that a lease sets is written in the conclusion's table (`Table.renew`);
- the observation is the reply and the stored value. A lease's reply holds the leased item's
  record: its stamp, its resource and its lease's stamp. A selection's reply is the selected
  waiters' records, so it names the selected identities and their hints;
- the statement holds at every scope, for every caller's term that reads the step's arguments
  (`Reads`, `Captured`, `src/Effect4/Laws/Modules/Reading.lean`).

The shared connectors join a goal to the store (`src/Effect4/Laws/Modules/Store.lean`). With
`step_updates`, a step term that reads the pair of a reply and a next value is one atomic
update of the cell. `step_keeps_cell` gives the typed half, with a step's typing
(`src/Effect4/Laws/Modules/Pool/Typing.lean`).

The first five statements are proved, each in place of its planned goal and with its statement
unchanged (decisions row 203). The sixth is the closer's step (decisions row 276, point 2): it
is proved where it is stated. The proofs read each builder of a step through the shared
reading rules (`src/Effect4/Laws/Modules/Reading.lean`) and Pool's
(`src/Effect4/Laws/Modules/Pool/Reading.lean`). They put the model's transition in closed form
on each side of its tests.

The statements establish no order of the wake across helpers, no cancellation law, no
fairness, no liveness, no wait of the close along a run and nothing of a wrapper. An equal value in the
model says nothing of a host. The finite controls are `Test/Program/PoolAgreement.lean` and
`Test/Program/PoolRelation.lean`: each statement's conclusion on every state of a finite
universe.
-/

set_option autoImplicit false

namespace Effect4.Pool.Model

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Modules
open Effect4.Constructive.List (decide_length_zero)

/-! ## The model's side, in closed form

Steps of the step goals: a lease that enrols, a lease that takes an item, and a return of a
lease that holds its item. The two refusals are `lease_closed` and `giveBack_stale`, and the
closer's two forms are `drain_enrols` and `drain_drained`
(`src/Effect4/Laws/Modules/Pool/Profile.lean`). -/

theorem lease_enrols {s : State} (id : Nat) (open_ : s.closing = false)
    (empty : s.available = []) :
    lease s id = ({ s with waiters := without s.waiters id ++ [id] }, false, none) := by
  unfold lease
  rw [open_, if_neg Bool.false_ne_true, empty]

theorem lease_takes {s : State} (id : Nat) {i : Nat} {rest : List Nat}
    (open_ : s.closing = false) (front : s.available = i :: rest) :
    lease s id =
      ({ s with
          items := mark s.items i s.next, available := rest,
          waiters := without s.waiters id, next := s.next + 1 },
        false, leased s.items i s.next) := by
  unfold lease
  rw [open_, if_neg Bool.false_ne_true, front]

theorem giveBack_returns {s : State} {i l : Nat} (held : s.items.any (·.heldBy i l) = true) :
    giveBack s i l =
      ({ s with items := freed s.items i l, available := i :: s.available }, true,
        !s.waiters.isEmpty) := by
  unfold giveBack
  rw [if_pos held]

/-! ## The six step goals -/

/-- **The selection step agrees with the model's `select`.** The reply is the selected
waiters' records through the table, in order: each names a selected identity and its hint. The
stored value is the model's next state. The step compares no identity, so no premise names the
table's injectivity. The table does not change. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem selectStep_agrees (tb : Table) (res : Nat → Val) (s : State) (count : Nat)
    {countSrc cellSrc : TermSrc} {env : Env} {path : List Nat} {vals : List Val}
    (readsCount : Reads countSrc env path vals (Val.nat count))
    (readsCell : Reads cellSrc env path vals (cellVal tb res s)) :
    Reads (Pool.selectStep countSrc cellSrc) env path vals
      (Val.tuple [selectReplyVal tb (select s count).2, cellVal tb res (select s count).1]) := by
  have waiters := reads_field readsCell (cell_waiters _ _ _ _ _)
  refine (reads_pair (reads_take waiters readsCount)
    (reads_recordSet readsCell (reads_drop waiters readsCount)
      (cell_setWaiters _ _ _ _ _ _))).to ?_
  rw [← List.map_take, ← List.map_drop]
  rfl

/-- **The close's first step agrees with the model's `close`.** The reply is whether the step
began the close, and the count of the waiters. The stored value is the model's next state. The
table does not change. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem closeStep_agrees (tb : Table) (res : Nat → Val) (s : State)
    {cellSrc : TermSrc} {env : Env} {path : List Nat} {vals : List Val}
    (readsCell : Reads cellSrc env path vals (cellVal tb res s)) :
    Reads (Pool.closeStep cellSrc) env path vals
      (Val.tuple [closeReplyVal (close s).2, cellVal tb res (close s).1]) := by
  have reply := reads_tuple2 (reads_notT (reads_field readsCell (cell_closing _ _ _ _ _)))
    (reads_len (reads_field readsCell (cell_waiters _ _ _ _ _)))
  refine (reads_pair reply
    (reads_recordSet readsCell (reads_bool true env path vals) (cell_setClosing _ _ _ _ _ _))).to ?_
  rw [List.length_map]
  rfl

/-- **The withdrawal agrees with the model's `withdraw`.** The reply is nothing, and the stored
value is the model's next state. The table does not change. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem withdrawStep_agrees (tb : Table) (res : Nat → Val) (s : State) (id : Nat)
    (injective : tb.Injective) {idSrc cellSrc : TermSrc} {env : Env} {path : List Nat}
    {vals : List Val} (depth : vals.length = env.names.length)
    (readsId : Captured idSrc env path vals (Val.promise (tb.handle id)))
    (readsCell : Reads cellSrc env path vals (cellVal tb res s)) :
    Reads (Pool.withdrawStep idSrc cellSrc) env path vals
      (Val.tuple [Val.unit, cellVal tb res (withdraw s id)]) :=
  reads_pair reads_unit (reads_withdrawn tb injective res s id depth readsId readsCell)

/-- **The return step agrees with the model's `giveBack`.** The reply is whether the lease
returned and whether a wake is owed. The stored value is the model's next state: where the
lease holds the item, the item's stamp is at the front of the idle stamps. No premise names
the lease: a return of a lease that holds nothing reads the cell as it is. The step compares
stamps and no identity, so no premise names the table's injectivity. The table does not
change. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem returnStep_agrees (tb : Table) (res : Nat → Val) (s : State) (item lease : Nat)
    {itemSrc leaseSrc cellSrc : TermSrc} {env : Env} {path : List Nat} {vals : List Val}
    (depth : vals.length = env.names.length)
    (readsItem : Captured itemSrc env path vals (Val.nat item))
    (readsLease : Captured leaseSrc env path vals (Val.nat lease))
    (readsCell : Reads cellSrc env path vals (cellVal tb res s)) :
    Reads (Pool.returnStep itemSrc leaseSrc cellSrc) env path vals
      (Val.tuple [returnReplyVal (giveBack s item lease).2,
        cellVal tb res (giveBack s item lease).1]) := by
  have waiters := reads_field readsCell (cell_waiters _ _ _ _ _)
  have returned := reads_pair
    (reads_tuple2 (reads_bool true env path vals) (reads_notT (reads_isEmpty waiters)))
    (reads_recordSet
      (reads_recordSet readsCell
        (reads_freed tb res s item lease depth readsItem readsLease readsCell)
        (cell_setItems _ _ _ _ _ _))
      (reads_front readsItem.atScope (reads_field readsCell (cell_available _ _ _ _ _)))
      (cell_setAvailable _ _ _ _ _ _))
  have stale := reads_pair
    (reads_tuple2 (reads_bool false env path vals) (reads_bool false env path vals)) readsCell
  have whole := reads_ifT
    (reads_heldBy tb res s item lease depth readsItem readsLease readsCell) returned stale
  cases held : s.items.any (·.heldBy item lease) with
  | true =>
    rw [held, if_pos rfl] at whole
    rw [giveBack_returns held]
    refine whole.to ?_
    rw [List.length_map, decide_length_zero]
    rfl
  | false =>
    rw [held, if_neg Bool.false_ne_true] at whole
    rw [giveBack_stale held]
    exact whole

/-- **The lease step agrees with the model's `lease`.** The reply is whether the pool refused,
and the leased item's record, if any: its stamp, its resource and its lease's stamp. The stored
value is the model's next state, through the table that holds `hint` at `id`: where the request
enrols, its entry holds the step's hint. No premise names the request: the step removes the
request's own entry first, as the model does. The request's identity stands in the removal's
fold, and the cell's own source in the two folds over the items, so each is a caller's term
under a fold. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem leaseStep_agrees (tb : Table) (res : Nat → Val) (s : State) (id : Nat)
    (hint : DeferredKey) (injective : tb.Injective) {idSrc hintSrc cellSrc : TermSrc}
    {env : Env} {path : List Nat} {vals : List Val} (depth : vals.length = env.names.length)
    (readsId : Captured idSrc env path vals (Val.promise (tb.handle id)))
    (readsHint : Reads hintSrc env path vals (Val.promise hint))
    (readsCell : Captured cellSrc env path vals (cellVal tb res s)) :
    Reads (Pool.leaseStep idSrc hintSrc cellSrc) env path vals
      (Val.tuple [leaseReplyVal res (lease s id).2,
        cellVal (tb.renew id hint) res (lease s id).1]) := by
  have cell := readsCell.atScope
  have available := reads_field cell (cell_available _ _ _ _ _)
  have waiters := reads_field cell (cell_waiters _ _ _ _ _)
  have next := reads_field cell (cell_next _ _ _ _ _)
  have gone := reads_withdrawn tb injective res s id depth readsId cell
  have none := reads_noItem tb res s cell
  have rest := reads_removeById tb injective (waiterVal tb) (fun w => w)
    (fun _ => waiter_id _ _) 0 s.waiters id depth waiters readsId
  -- the request's own entry left, so every waiter that stays is of another identity
  have others : ∀ w ∈ without s.waiters id, w ≠ id := fun w member => (mem_without.mp member).2
  have refused := reads_pair (reads_tuple2 (reads_bool true env path vals) none) gone
  have enrolled := reads_pair (reads_tuple2 (reads_bool false env path vals) none)
    (reads_recordSet cell (reads_snoc rest (reads_mkWaiter readsId.atScope readsHint))
      (cell_setWaiters _ _ _ _ _ _))
  have taken := reads_pair
    (reads_tuple2 (reads_bool false env path vals)
      (reads_head (reads_leasedOf tb res s depth readsCell)))
    (reads_recordSet
      (reads_recordSet
        (reads_recordSet gone (reads_marked tb res s depth readsCell) (cell_setItems _ _ _ _ _ _))
        (reads_drop available (reads_nat 1 env path vals)) (cell_setAvailable _ _ _ _ _ _))
      (reads_add next (reads_nat 1 env path vals)) (cell_setNext _ _ _ _ _ _))
  have whole := reads_ifT (reads_field cell (cell_closing _ _ _ _ _)) refused
    (reads_ifT (reads_isEmpty available) enrolled taken)
  cases closed : s.closing with
  | true =>
    rw [if_pos closed] at whole
    rw [lease_closed closed id, cellVal_renew tb res (withdraw s id) id hint others]
    exact whole
  | false =>
    rw [if_neg fun refuses => Bool.false_ne_true (closed.symm.trans refuses)] at whole
    cases front : s.available with
    | nil =>
      have noneIdle : decide ((s.available.map Val.nat).length = 0) = true := by
        rw [front]
        rfl
      rw [noneIdle, if_pos rfl] at whole
      rw [lease_enrols id closed front]
      refine whole.to ?_
      show _ = Val.tuple [Val.tuple [Val.bool false, Store.Val.none],
        cellOf (.list (s.available.map Val.nat)) (.bool s.closing)
          (.list (s.items.map (itemVal res))) (.nat s.next)
          (.list ((without s.waiters id ++ [id]).map (waiterVal (tb.renew id hint))))]
      rw [List.map_append, waiters_renew tb (without s.waiters id) id hint others, List.map_cons,
        List.map_nil, waiterVal_renewed]
      rfl
    | cons i tail =>
      have someIdle : decide ((s.available.map Val.nat).length = 0) = false := by
        rw [front]
        rfl
      have head : s.available.headD 0 = i := by
        rw [front]
        rfl
      have dropped : (s.available.map Val.nat).drop 1 = tail.map Val.nat := by
        rw [front]
        rfl
      rw [someIdle, if_neg Bool.false_ne_true, head, dropped, List.getElem?_map,
        leased_flatMap] at whole
      rw [lease_takes id closed front,
        cellVal_renew tb res
          { s with
            items := mark s.items i s.next, available := tail,
            waiters := without s.waiters id, next := s.next + 1 }
          id hint others]
      refine whole.to ?_
      cases leased s.items i s.next with
      | none => rfl
      | some it => rfl

/-- **The closer's step agrees with the model's `drain`** (decisions row 276, point 2). The
reply is whether no lease is outstanding. The stored value is the model's next state, through
the table that holds `hint` at `id`: where the closer enrols, its entry holds the step's hint.
No premise names the closer: the step removes the closer's own entry first, as the model does.
The identity stands in the removal's fold, so it is a caller's term under a fold. The cell's own
source stands in no fold's body. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem drainStep_agrees (tb : Table) (res : Nat → Val) (s : State) (id : Nat)
    (hint : DeferredKey) (injective : tb.Injective) {idSrc hintSrc cellSrc : TermSrc}
    {env : Env} {path : List Nat} {vals : List Val} (depth : vals.length = env.names.length)
    (readsId : Captured idSrc env path vals (Val.promise (tb.handle id)))
    (readsHint : Reads hintSrc env path vals (Val.promise hint))
    (readsCell : Reads cellSrc env path vals (cellVal tb res s)) :
    Reads (Pool.drainStep idSrc hintSrc cellSrc) env path vals
      (Val.tuple [Val.bool (drain s id).2, cellVal (tb.renew id hint) res (drain s id).1]) := by
  have waiters := reads_field readsCell (cell_waiters _ _ _ _ _)
  have gone := reads_withdrawn tb injective res s id depth readsId readsCell
  have rest := reads_removeById tb injective (waiterVal tb) (fun w => w)
    (fun _ => waiter_id _ _) 0 s.waiters id depth waiters readsId
  -- the closer's own entry left, so every waiter that stays is of another identity
  have others : ∀ w ∈ without s.waiters id, w ≠ id := fun w member => (mem_without.mp member).2
  have enrolled := reads_pair (reads_bool false env path vals)
    (reads_recordSet readsCell (reads_snoc rest (reads_mkWaiter readsId.atScope readsHint))
      (cell_setWaiters _ _ _ _ _ _))
  have drained := reads_pair (reads_bool true env path vals) gone
  have whole := reads_ifT (reads_outstanding tb res s depth readsCell) enrolled drained
  cases held : s.items.any (·.borrowed) with
  | true =>
    rw [held, if_pos rfl] at whole
    rw [drain_enrols id held]
    refine whole.to ?_
    show _ = Val.tuple [Val.bool false,
      cellOf (.list (s.available.map Val.nat)) (.bool s.closing)
        (.list (s.items.map (itemVal res))) (.nat s.next)
        (.list ((without s.waiters id ++ [id]).map (waiterVal (tb.renew id hint))))]
    rw [List.map_append, waiters_renew tb (without s.waiters id) id hint others, List.map_cons,
      List.map_nil, waiterVal_renewed]
    rfl
  | false =>
    rw [held, if_neg Bool.false_ne_true] at whole
    rw [drain_drained id held, cellVal_renew tb res (withdraw s id) id hint others]
    exact whole

/-! ## The six statements as one

`pool_steps_agree` assembles the six step statements: each field is one of them, word for
word, and its proof cites that statement. So the plan derives the standing of the whole from
the six. -/

/-- **Pool's six steps agree with the abstract model**: one field for each step, at the
statement of its goal. -/
structure StepsAgree : Prop where
  /-- The model's `lease`. -/
  lease : ∀ (tb : Table) (res : Nat → Val) (s : State) (id : Nat) (hint : DeferredKey),
    tb.Injective →
    ∀ {idSrc hintSrc cellSrc : TermSrc} {env : Env} {path : List Nat} {vals : List Val},
      vals.length = env.names.length →
      Captured idSrc env path vals (Val.promise (tb.handle id)) →
      Reads hintSrc env path vals (Val.promise hint) →
      Captured cellSrc env path vals (cellVal tb res s) →
      Reads (Pool.leaseStep idSrc hintSrc cellSrc) env path vals
        (Val.tuple [leaseReplyVal res (lease s id).2,
          cellVal (tb.renew id hint) res (lease s id).1])
  /-- The model's `giveBack`. -/
  giveBack : ∀ (tb : Table) (res : Nat → Val) (s : State) (item lease : Nat)
    {itemSrc leaseSrc cellSrc : TermSrc} {env : Env} {path : List Nat} {vals : List Val},
      vals.length = env.names.length →
      Captured itemSrc env path vals (Val.nat item) →
      Captured leaseSrc env path vals (Val.nat lease) →
      Reads cellSrc env path vals (cellVal tb res s) →
      Reads (Pool.returnStep itemSrc leaseSrc cellSrc) env path vals
        (Val.tuple [returnReplyVal (giveBack s item lease).2,
          cellVal tb res (giveBack s item lease).1])
  /-- The model's `select`. -/
  select : ∀ (tb : Table) (res : Nat → Val) (s : State) (count : Nat)
    {countSrc cellSrc : TermSrc} {env : Env} {path : List Nat} {vals : List Val},
      Reads countSrc env path vals (Val.nat count) →
      Reads cellSrc env path vals (cellVal tb res s) →
      Reads (Pool.selectStep countSrc cellSrc) env path vals
        (Val.tuple [selectReplyVal tb (select s count).2, cellVal tb res (select s count).1])
  /-- The model's `withdraw`. -/
  withdraw : ∀ (tb : Table) (res : Nat → Val) (s : State) (id : Nat), tb.Injective →
    ∀ {idSrc cellSrc : TermSrc} {env : Env} {path : List Nat} {vals : List Val},
      vals.length = env.names.length →
      Captured idSrc env path vals (Val.promise (tb.handle id)) →
      Reads cellSrc env path vals (cellVal tb res s) →
      Reads (Pool.withdrawStep idSrc cellSrc) env path vals
        (Val.tuple [Val.unit, cellVal tb res (withdraw s id)])
  /-- The model's `close`. -/
  close : ∀ (tb : Table) (res : Nat → Val) (s : State)
    {cellSrc : TermSrc} {env : Env} {path : List Nat} {vals : List Val},
      Reads cellSrc env path vals (cellVal tb res s) →
      Reads (Pool.closeStep cellSrc) env path vals
        (Val.tuple [closeReplyVal (close s).2, cellVal tb res (close s).1])
  /-- The model's `drain`. -/
  drain : ∀ (tb : Table) (res : Nat → Val) (s : State) (id : Nat) (hint : DeferredKey),
    tb.Injective →
    ∀ {idSrc hintSrc cellSrc : TermSrc} {env : Env} {path : List Nat} {vals : List Val},
      vals.length = env.names.length →
      Captured idSrc env path vals (Val.promise (tb.handle id)) →
      Reads hintSrc env path vals (Val.promise hint) →
      Reads cellSrc env path vals (cellVal tb res s) →
      Reads (Pool.drainStep idSrc hintSrc cellSrc) env path vals
        (Val.tuple [Val.bool (drain s id).2, cellVal (tb.renew id hint) res (drain s id).1])

/-- **The six step statements hold** (the claim `pool-steps-agree`, a part of the proposed
claim `pool-expansion-agrees`). Each field is one statement of this file. It establishes no
order of the wake across helpers, no cancellation law, no liveness, no wait of the close along
a run and nothing of a wrapper. Its consumer is the attempt laws of the public operations
(`src/Effect4/Laws/Modules/Pool/Ops.lean`), and then the law of a run. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem pool_steps_agree : StepsAgree where
  lease := leaseStep_agrees
  giveBack := returnStep_agrees
  select := selectStep_agrees
  withdraw := withdrawStep_agrees
  close := closeStep_agrees
  drain := drainStep_agrees

end Effect4.Pool.Model
