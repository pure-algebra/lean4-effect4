import Effect4.Laws.Modules.Semaphore.Reading
import Effect4.Laws.Auto.Obligations
import Effect4.Laws.Auto.Semantics

/-!
# Semaphore's five steps agree with the abstract model: the step goals (decisions row 265)

Each step term of `src/Effect4/Modules/Semaphore/Steps.lean` has one statement here. From a
cell that holds a model state through the table, the step reads the tuple of the model's reply
and the model's next state through the table. The relation is in
`src/Effect4/Laws/Modules/Semaphore/Relation.lean`.

| Goal | The model's transition | Premises beside the readings |
| --- | --- | --- |
| `takeStep_agrees` | `take` | an injective table; the identity kept under a fold |
| `takeIfAvailableStep_agrees` | `takeIfAvailable` | none |
| `releaseStep_agrees` | `release` | none: no premise on the count |
| `visitStep_agrees` | `visit` | the cursor and the cell's source kept under a fold |
| `withdrawStep_agrees` | `withdraw` | an injective table; the identity kept under a fold |

Placement. Concept `translation-simulation`. Requirement R10, as parts of the proposed claim
`semaphore-expansion-agrees`. The consumer of each goal is the public law, in the slice of the
operations that wait. Reach, for each goal:

- the domain is every model state: no goal takes the profile as a premise, because no step
  reads it. The profile's closure is a statement of its own
  (`src/Effect4/Laws/Modules/Semaphore/Profile.lean`);
- the table's injectivity is a written premise where a step tests an identity, and the hint
  that a take sets is written in the conclusion's table (`Table.renew`);
- the observation is the reply and the stored value. A visit's reply is the selected waiter's
  record: its identity, its hint, its count and its stamp;
- the statement holds at every scope, for every caller's term that reads the step's arguments
  (`Reads`, `Captured`, `src/Effect4/Laws/Modules/Reading.lean`).

The shared connectors join a goal to the store (`src/Effect4/Laws/Modules/Store.lean`). With
`step_updates`, a step term that reads the pair of a reply and a next value is one atomic
update of the cell. `step_keeps_cell` gives the typed half, with a step's typing
(`src/Effect4/Laws/Modules/Semaphore/Typing.lean`).

The five statements are proved, each in place of its planned goal and with its statement
unchanged (decisions row 203). The proofs read each builder of a step through the shared
reading rules (`src/Effect4/Laws/Modules/Reading.lean`) and Semaphore's
(`src/Effect4/Laws/Modules/Semaphore/Reading.lean`). They put the model's transition in closed
form: the two takes on each side of their test, and a visit from the waiters that start at the
first fitting one (`visit_fromFirst`).

The statements establish no order of the wake across visits, no cancellation law, no fairness,
no liveness and nothing of a wrapper. An equal value in the model says nothing of a host. The
finite controls are `Test/Program/SemaphoreAgreement.lean` and
`Test/Program/SemaphoreRelation.lean`: each statement's conclusion on every state of a
universe of 225 states.
-/

set_option autoImplicit false

namespace Effect4.Semaphore.Model

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Modules
open Effect4.Constructive.List (fromFirst_find? decide_length_zero)

/-! ## The model's side, in closed form

Steps of the step goals: the two takes on each side of their test, and a visit from the waiters
that start at the first fitting one. -/

theorem take_fits {s : State} {n : Nat} (id : Nat) (fitsNow : n ≤ free s) :
    take s id n = ({ s with taken := s.taken + n, waiters := without s.waiters id }, true) := by
  unfold take
  rw [if_pos fitsNow]

theorem take_enrols {s : State} {n : Nat} (id : Nat) (tooMany : ¬ n ≤ free s) :
    take s id n =
      ({ s with waiters := without s.waiters id ++ [⟨id, n, s.next⟩], next := s.next + 1 },
        false) := by
  unfold take
  rw [if_neg tooMany]

theorem takeIfAvailable_fits {s : State} {n : Nat} (fitsNow : n ≤ free s) :
    takeIfAvailable s n = ({ s with taken := s.taken + n }, true) := by
  unfold takeIfAvailable
  rw [if_pos fitsNow]

theorem takeIfAvailable_stays {s : State} {n : Nat} (tooMany : ¬ n ≤ free s) :
    takeIfAvailable s n = (s, false) := by
  unfold takeIfAvailable
  rw [if_neg tooMany]

/-- **The model's visit where a permit is free, from the waiters that start at the first
fitting one.** The reply is the first of those waiters, if any. The next state holds the
waiters before them, then the rest of them. The list is the list without the selected waiter:
an earlier entry equal to the selected one would fit too, at or after the cursor, so it would
have been selected first (`fromFirst_find?`). So the removal by position is the model's
removal, with no premise on the identities. -/
theorem visit_fromFirst (s : State) (cursor : Nat) (someFree : free s ≠ 0) :
    visit s cursor =
      ({ s with
          waiters :=
            s.waiters.take (s.waiters.length -
                (s.waiters.dropWhile (fun w => !fits cursor (free s) w)).length) ++
              (s.waiters.dropWhile (fun w => !fits cursor (free s) w)).drop 1 },
        (s.waiters.dropWhile (fun w => !fits cursor (free s) w))[0]?) := by
  obtain ⟨head, around⟩ := fromFirst_find? (fits cursor (free s)) s.waiters
  cases found : s.waiters.find? (fits cursor (free s)) with
  | none =>
    rw [found] at head around
    rw [visit_none_fits someFree found, head, around]
  | some w =>
    rw [found] at head around
    rw [visit_some someFree found, head, around]

/-! ## The five step goals -/

/-- **The take-if-available step agrees with the model's `takeIfAvailable`.** The reply is
whether the request took, and the stored value is the model's next state. The table does not
change. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem takeIfAvailableStep_agrees (tb : Table) (s : State) (n : Nat)
    {needSrc cellSrc : TermSrc} {env : Env} {path : List Nat} {vals : List Val}
    (readsNeed : Reads needSrc env path vals (Val.nat n))
    (readsCell : Reads cellSrc env path vals (cellVal tb s)) :
    Reads (Semaphore.takeIfAvailableStep needSrc cellSrc) env path vals
      (Val.tuple [Val.bool (takeIfAvailable s n).2, cellVal tb (takeIfAvailable s n).1]) := by
  have taken := reads_field readsCell (cell_taken _ _ _ _)
  have took := reads_pair (reads_bool true env path vals)
    (reads_recordSet readsCell (reads_add taken readsNeed) (cell_setTaken _ _ _ _ _))
  have stays := reads_pair (reads_bool false env path vals) readsCell
  have whole := reads_ifT (reads_fitsT tb s n readsNeed readsCell) took stays
  by_cases fitsNow : n ≤ free s
  · rw [decide_eq_true fitsNow, if_pos rfl] at whole
    rw [takeIfAvailable_fits fitsNow]
    exact whole
  · rw [decide_eq_false fitsNow, if_neg Bool.false_ne_true] at whole
    rw [takeIfAvailable_stays fitsNow]
    exact whole

/-- **The release step agrees with the model's `release`.** The reply is the free count after
the release and whether a waiter is enrolled. The stored value is the model's next state. No
premise names the count: the model's release is total too (decisions row 261). The table does
not change. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem releaseStep_agrees (tb : Table) (s : State) (n : Nat)
    {countSrc cellSrc : TermSrc} {env : Env} {path : List Nat} {vals : List Val}
    (readsCount : Reads countSrc env path vals (Val.nat n))
    (readsCell : Reads cellSrc env path vals (cellVal tb s)) :
    Reads (Semaphore.releaseStep countSrc cellSrc) env path vals
      (Val.tuple [releaseReplyVal (release s n).2, cellVal tb (release s n).1]) := by
  have taken := reads_field readsCell (cell_taken _ _ _ _)
  have permits := reads_field readsCell (cell_permits _ _ _ _)
  have waiters := reads_field readsCell (cell_waiters _ _ _ _)
  have left := reads_sub taken readsCount
  have reply := reads_tuple2 (reads_sub permits left) (reads_notT (reads_isEmpty waiters))
  have stored := reads_recordSet readsCell left (cell_setTaken _ _ _ _ _)
  refine (reads_pair reply stored).to ?_
  rw [List.length_map, decide_length_zero]
  rfl

/-- **The withdrawal agrees with the model's `withdraw`.** The reply is nothing, and the stored
value is the model's next state. The table does not change. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem withdrawStep_agrees (tb : Table) (s : State) (id : Nat) (injective : tb.Injective)
    {idSrc cellSrc : TermSrc} {env : Env} {path : List Nat} {vals : List Val}
    (depth : vals.length = env.names.length)
    (readsId : Captured idSrc env path vals (Val.promise (tb.handle id)))
    (readsCell : Reads cellSrc env path vals (cellVal tb s)) :
    Reads (Semaphore.withdrawStep idSrc cellSrc) env path vals
      (Val.tuple [Val.unit, cellVal tb (withdraw s id)]) := by
  have waiters := reads_field readsCell (cell_waiters _ _ _ _)
  have removed := reads_removeWaiter tb injective s.waiters id depth waiters readsId
  exact reads_pair reads_unit (reads_recordSet readsCell removed (cell_setWaiters _ _ _ _ _))

/-- **The take step agrees with the model's `take`.** The reply is whether the request took.
The stored value is the model's next state, through the table that holds `hint` at `id`: where
the request enrols, its entry holds the step's hint. No premise names the request: the step
removes the request's own entry first, as the model does. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem takeStep_agrees (tb : Table) (s : State) (id n : Nat) (hint : DeferredKey)
    (injective : tb.Injective) {needSrc idSrc hintSrc cellSrc : TermSrc} {env : Env}
    {path : List Nat} {vals : List Val} (depth : vals.length = env.names.length)
    (readsNeed : Reads needSrc env path vals (Val.nat n))
    (readsId : Captured idSrc env path vals (Val.promise (tb.handle id)))
    (readsHint : Reads hintSrc env path vals (Val.promise hint))
    (readsCell : Reads cellSrc env path vals (cellVal tb s)) :
    Reads (Semaphore.takeStep needSrc idSrc hintSrc cellSrc) env path vals
      (Val.tuple [Val.bool (take s id n).2, cellVal (tb.renew id hint) (take s id n).1]) := by
  have waiters := reads_field readsCell (cell_waiters _ _ _ _)
  have taken := reads_field readsCell (cell_taken _ _ _ _)
  have next := reads_field readsCell (cell_next _ _ _ _)
  have rest := reads_removeWaiter tb injective s.waiters id depth waiters readsId
  -- the request's own entry left, so every waiter that stays is of another identity
  have others : ∀ w ∈ without s.waiters id, w.id ≠ id := fun w member => (mem_without.mp member).2
  have framed := waiters_renew tb (without s.waiters id) id hint others
  have took := reads_pair (reads_bool true env path vals)
    (reads_recordSet
      (reads_recordSet readsCell (reads_add taken readsNeed) (cell_setTaken _ _ _ _ _)) rest
      (cell_setWaiters _ _ _ _ _))
  have enrolled := reads_pair (reads_bool false env path vals)
    (reads_recordSet
      (reads_recordSet readsCell
        (reads_snoc rest (reads_mkWaiter readsId.atScope readsNeed readsHint next))
        (cell_setWaiters _ _ _ _ _))
      (reads_add next (reads_nat 1 env path vals)) (cell_setNext _ _ _ _ _))
  have whole := reads_ifT (reads_fitsT tb s n readsNeed readsCell) took enrolled
  by_cases fitsNow : n ≤ free s
  · rw [decide_eq_true fitsNow, if_pos rfl] at whole
    rw [take_fits id fitsNow]
    refine whole.to ?_
    show _ = Val.tuple [Val.bool true,
      cellOf (.nat s.next) (.nat s.permits) (.nat (s.taken + n))
        (.list ((without s.waiters id).map (waiterVal (tb.renew id hint))))]
    rw [framed]
  · rw [decide_eq_false fitsNow, if_neg Bool.false_ne_true] at whole
    rw [take_enrols id fitsNow]
    refine whole.to ?_
    show _ = Val.tuple [Val.bool false,
      cellOf (.nat (s.next + 1)) (.nat s.permits) (.nat s.taken)
        (.list ((without s.waiters id ++ [(⟨id, n, s.next⟩ : Waiter)]).map
          (waiterVal (tb.renew id hint))))]
    rw [List.map_append, framed, List.map_cons, List.map_nil, waiterVal_renewed]

/-- **The visit step agrees with the model's `visit`.** The reply is the selected waiter's
record through the table, or nothing. The stored value is the model's next state. The cursor
and the cell's own source stand in the fold's body, so each is a caller's term under a fold.
The table does not change.

The term compares two numbers of each entry, and no record and no handle. It removes the
selected entry by its position. The model removes it by `erase`. The two agree with no premise
on the identities: an earlier entry equal to the selected one would fit too, at or after the
cursor, so it would have been selected first (`visit_fromFirst`). -/
@[semantics "translation-simulation" (requirement := R10)]
theorem visitStep_agrees (tb : Table) (s : State) (cursor : Nat)
    {cursorSrc cellSrc : TermSrc} {env : Env} {path : List Nat} {vals : List Val}
    (depth : vals.length = env.names.length)
    (readsCursor : Captured cursorSrc env path vals (Val.nat cursor))
    (readsCell : Captured cellSrc env path vals (cellVal tb s)) :
    Reads (Semaphore.visitStep cursorSrc cellSrc) env path vals
      (Val.tuple [visitReplyVal tb (visit s cursor).2, cellVal tb (visit s cursor).1]) := by
  have rest := reads_fromFirst tb s cursor depth readsCursor readsCell
  have whole := reads_visitFrom tb s _ rest readsCell.atScope
  by_cases noneFree : free s = 0
  · rw [if_pos noneFree] at whole
    rw [visit_none_free cursor noneFree]
    exact whole
  · rw [if_neg noneFree] at whole
    rw [visit_fromFirst s cursor noneFree]
    exact whole

/-! ## The five statements as one

`semaphore_steps_agree` assembles the five step statements: each field is one of them, word
for word, and its proof cites that statement. So the plan derives the standing of the whole
from the five. -/

/-- **Semaphore's five steps agree with the abstract model**: one field for each step, at the
statement of its goal. -/
structure StepsAgree : Prop where
  /-- The model's `take`. -/
  take : ∀ (tb : Table) (s : State) (id n : Nat) (hint : DeferredKey), tb.Injective →
    ∀ {needSrc idSrc hintSrc cellSrc : TermSrc} {env : Env} {path : List Nat} {vals : List Val},
      vals.length = env.names.length →
      Reads needSrc env path vals (Val.nat n) →
      Captured idSrc env path vals (Val.promise (tb.handle id)) →
      Reads hintSrc env path vals (Val.promise hint) →
      Reads cellSrc env path vals (cellVal tb s) →
      Reads (Semaphore.takeStep needSrc idSrc hintSrc cellSrc) env path vals
        (Val.tuple [Val.bool (take s id n).2, cellVal (tb.renew id hint) (take s id n).1])
  /-- The model's `takeIfAvailable`. -/
  takeIfAvailable : ∀ (tb : Table) (s : State) (n : Nat)
    {needSrc cellSrc : TermSrc} {env : Env} {path : List Nat} {vals : List Val},
      Reads needSrc env path vals (Val.nat n) →
      Reads cellSrc env path vals (cellVal tb s) →
      Reads (Semaphore.takeIfAvailableStep needSrc cellSrc) env path vals
        (Val.tuple [Val.bool (takeIfAvailable s n).2, cellVal tb (takeIfAvailable s n).1])
  /-- The model's `release`. -/
  release : ∀ (tb : Table) (s : State) (n : Nat)
    {countSrc cellSrc : TermSrc} {env : Env} {path : List Nat} {vals : List Val},
      Reads countSrc env path vals (Val.nat n) →
      Reads cellSrc env path vals (cellVal tb s) →
      Reads (Semaphore.releaseStep countSrc cellSrc) env path vals
        (Val.tuple [releaseReplyVal (release s n).2, cellVal tb (release s n).1])
  /-- The model's `visit`. -/
  visit : ∀ (tb : Table) (s : State) (cursor : Nat)
    {cursorSrc cellSrc : TermSrc} {env : Env} {path : List Nat} {vals : List Val},
      vals.length = env.names.length →
      Captured cursorSrc env path vals (Val.nat cursor) →
      Captured cellSrc env path vals (cellVal tb s) →
      Reads (Semaphore.visitStep cursorSrc cellSrc) env path vals
        (Val.tuple [visitReplyVal tb (visit s cursor).2, cellVal tb (visit s cursor).1])
  /-- The model's `withdraw`. -/
  withdraw : ∀ (tb : Table) (s : State) (id : Nat), tb.Injective →
    ∀ {idSrc cellSrc : TermSrc} {env : Env} {path : List Nat} {vals : List Val},
      vals.length = env.names.length →
      Captured idSrc env path vals (Val.promise (tb.handle id)) →
      Reads cellSrc env path vals (cellVal tb s) →
      Reads (Semaphore.withdrawStep idSrc cellSrc) env path vals
        (Val.tuple [Val.unit, cellVal tb (withdraw s id)])

/-- **The five step statements hold** (the proposed claim `semaphore-steps-agree`, a part of
`semaphore-expansion-agrees`). Each field is one statement of this file. It establishes no
order of the wake across visits, no cancellation law, no liveness and nothing of a wrapper. Its
consumer is the public law, in the slice of the operations that wait. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem semaphore_steps_agree : StepsAgree where
  take := takeStep_agrees
  takeIfAvailable := takeIfAvailableStep_agrees
  release := releaseStep_agrees
  visit := visitStep_agrees
  withdraw := withdrawStep_agrees

end Effect4.Semaphore.Model
