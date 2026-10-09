import Effect4.Laws.Library.Semaphore.Reading
import Effect4.Laws.Library.Semaphore.Data
import Effect4.Laws.Auto.Obligations
import Effect4.Laws.Auto.Semantics

/-!
# Semaphore's five steps agree with the abstract model: the step goals (decisions row 265)

Each step term of `src/Effect4/Library/Semaphore/Steps.lean` has one statement here. From a
cell that holds a model state through the table, the step reads the tuple of the model's reply
and the model's next state through the table. The relation is in
`src/Effect4/Laws/Library/Semaphore/Relation.lean`.

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
  (`src/Effect4/Laws/Library/Semaphore/Profile.lean`);
- the table's injectivity is a written premise where a step tests an identity, and the hint
  that a take sets is written in the conclusion's table (`Table.renew`);
- the observation is the reply and the stored value. A visit's reply is the selected waiter's
  record: its identity, its hint, its count and its stamp;
- the statement holds at every scope, for every caller's term that reads the step's arguments
  (`Reads`, `Captured`, `src/Effect4/Laws/Step/Reading.lean`).

The shared connectors join a goal to the store (`src/Effect4/Laws/Step/Store.lean`). With
`step_updates`, a step term that reads the pair of a reply and a next value is one atomic
update of the cell. `step_keeps_cell` gives the typed half, with a step's typing
(`src/Effect4/Laws/Library/Semaphore/Typing.lean`).

The five statements are proved, each in place of its planned goal and with its statement
unchanged (decisions row 203). The proofs read each builder of a step through the shared
reading rules (`src/Effect4/Laws/Step/Reading.lean`) and Semaphore's
(`src/Effect4/Laws/Library/Semaphore/Reading.lean`). They put the model's transition in closed
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
  have reads := Step.sound Effect4.Schema.Model.Leaves.deferredKeys (inputsAt tb s n)
    (Input.reads_cons readsNeed (Input.reads_cons (readsCell.to (cellVal_image tb s).symm)
      Input.reads_nil)) Data.takeIfAvailable rfl
  rw [takeIfAvailable_eval] at reads
  exact reads.to (by rw [← cellVal_image]; rfl)

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
  have reads := Step.sound Effect4.Schema.Model.Leaves.deferredKeys (inputsAt tb s n)
    (Input.reads_cons readsCount (Input.reads_cons (readsCell.to (cellVal_image tb s).symm)
      Input.reads_nil)) Data.release rfl
  rw [release_eval] at reads
  exact reads.to (by rw [← cellVal_image]; rfl)

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
  have reads := Step.sound Effect4.Schema.Model.Leaves.deferredKeys (withdrawInputs tb s id)
    (Input.reads_cons readsId.atScope
      (Input.reads_cons (readsCell.to (cellVal_image tb s).symm) Input.reads_nil))
    Data.withdraw rfl depth ⟨Effect4.Schema.DeferredIdentity.deferredKeys⟩
  rw [withdraw_eval tb s id injective] at reads
  exact reads.to (by rw [← cellVal_image]; rfl)

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
  have reads := Step.sound Effect4.Schema.Model.Leaves.deferredKeys (takeInputs tb s id n hint)
    (Input.reads_cons readsNeed (Input.reads_cons readsId.atScope
      (Input.reads_cons readsHint
        (Input.reads_cons (readsCell.to (cellVal_image tb s).symm) Input.reads_nil))))
    Data.take rfl depth ⟨Effect4.Schema.DeferredIdentity.deferredKeys⟩
  rw [take_eval tb s id n hint injective] at reads
  exact reads.to (by rw [← cellVal_image]; rfl)

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
  have reads := Step.sound Effect4.Schema.Model.Leaves.deferredKeys (inputsAt tb s cursor)
    (Input.reads_cons readsCursor.atScope
      (Input.reads_cons (readsCell.atScope.to (cellVal_image tb s).symm) Input.reads_nil))
    Data.visit rfl depth (by trivial)
  rw [visit_eval] at reads
  exact reads.to (by
    change Val.list [(Effect4.Schema.Model.imageAt Effect4.Schema.Model.Leaves.deferredKeys
      (.option waiterTy)).toVal ((visit s cursor).2.map (waiterC tb)),
      (Effect4.Schema.Model.imageAt Effect4.Schema.Model.Leaves.deferredKeys (.record cellRecord)).toVal
        (cellC tb (visit s cursor).1)] = _
    rw [visitReply_image, cellVal_image])

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
