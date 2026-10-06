import Effect4.Laws.Modules.Pool.Relation
import Effect4.Laws.Modules.Reading
import Effect4.Laws.Auto.Obligations
import Effect4.Laws.Auto.Semantics

/-!
# Pool's five steps agree with the abstract model: the step goals (decisions rows 267 to 269)

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

The five statements are planned goals (decisions row 203): each is a theorem whose body is
open, and `pool_steps_agree` rests on the five. Each is proved in place, with its statement
unchanged.

The statements establish no order of the wake across helpers, no cancellation law, no
fairness, no liveness, no close that waits and nothing of a wrapper. An equal value in the
model says nothing of a host. The finite controls are `Test/Program/PoolAgreement.lean` and
`Test/Program/PoolRelation.lean`: each statement's conclusion on every state of a finite
universe, and each statement's pinned axioms.
-/

set_option autoImplicit false

namespace Effect4.Pool.Model

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Modules

/-! ## The five step goals -/

/-- **The selection step agrees with the model's `select`.** The reply is the selected
waiters' records through the table, in order: each names a selected identity and its hint. The
stored value is the model's next state. The step compares no identity, so no premise names the
table's injectivity. The table does not change. -/
@[semantics "translation-simulation" (requirement := R10)]
proof_goal selectStep_agrees (tb : Table) (res : Nat → Val) (s : State) (count : Nat)
    {countSrc cellSrc : TermSrc} {env : Env} {path : List Nat} {vals : List Val}
    (readsCount : Reads countSrc env path vals (Val.nat count))
    (readsCell : Reads cellSrc env path vals (cellVal tb res s)) :
    Reads (Pool.selectStep countSrc cellSrc) env path vals
      (Val.tuple [selectReplyVal tb (select s count).2, cellVal tb res (select s count).1])

/-- **The close's first step agrees with the model's `close`.** The reply is whether the step
began the close, and the count of the waiters. The stored value is the model's next state. The
table does not change. -/
@[semantics "translation-simulation" (requirement := R10)]
proof_goal closeStep_agrees (tb : Table) (res : Nat → Val) (s : State)
    {cellSrc : TermSrc} {env : Env} {path : List Nat} {vals : List Val}
    (readsCell : Reads cellSrc env path vals (cellVal tb res s)) :
    Reads (Pool.closeStep cellSrc) env path vals
      (Val.tuple [closeReplyVal (close s).2, cellVal tb res (close s).1])

/-- **The withdrawal agrees with the model's `withdraw`.** The reply is nothing, and the stored
value is the model's next state. The table does not change. -/
@[semantics "translation-simulation" (requirement := R10)]
proof_goal withdrawStep_agrees (tb : Table) (res : Nat → Val) (s : State) (id : Nat)
    (injective : tb.Injective) {idSrc cellSrc : TermSrc} {env : Env} {path : List Nat}
    {vals : List Val} (depth : vals.length = env.names.length)
    (readsId : Captured idSrc env path vals (Val.promise (tb.handle id)))
    (readsCell : Reads cellSrc env path vals (cellVal tb res s)) :
    Reads (Pool.withdrawStep idSrc cellSrc) env path vals
      (Val.tuple [Val.unit, cellVal tb res (withdraw s id)])

/-- **The return step agrees with the model's `giveBack`.** The reply is whether the lease
returned and whether a wake is owed. The stored value is the model's next state: where the
lease holds the item, the item's stamp is at the front of the idle stamps. No premise names
the lease: a return of a lease that holds nothing reads the cell as it is. The step compares
stamps and no identity, so no premise names the table's injectivity. The table does not
change. -/
@[semantics "translation-simulation" (requirement := R10)]
proof_goal returnStep_agrees (tb : Table) (res : Nat → Val) (s : State) (item lease : Nat)
    {itemSrc leaseSrc cellSrc : TermSrc} {env : Env} {path : List Nat} {vals : List Val}
    (depth : vals.length = env.names.length)
    (readsItem : Captured itemSrc env path vals (Val.nat item))
    (readsLease : Captured leaseSrc env path vals (Val.nat lease))
    (readsCell : Reads cellSrc env path vals (cellVal tb res s)) :
    Reads (Pool.returnStep itemSrc leaseSrc cellSrc) env path vals
      (Val.tuple [returnReplyVal (giveBack s item lease).2,
        cellVal tb res (giveBack s item lease).1])

/-- **The lease step agrees with the model's `lease`.** The reply is whether the pool refused,
and the leased item's record, if any: its stamp, its resource and its lease's stamp. The stored
value is the model's next state, through the table that holds `hint` at `id`: where the request
enrols, its entry holds the step's hint. No premise names the request: the step removes the
request's own entry first, as the model does. The request's identity stands in the removal's
fold, and the cell's own source in the two folds over the items, so each is a caller's term
under a fold. -/
@[semantics "translation-simulation" (requirement := R10)]
proof_goal leaseStep_agrees (tb : Table) (res : Nat → Val) (s : State) (id : Nat)
    (hint : DeferredKey) (injective : tb.Injective) {idSrc hintSrc cellSrc : TermSrc}
    {env : Env} {path : List Nat} {vals : List Val} (depth : vals.length = env.names.length)
    (readsId : Captured idSrc env path vals (Val.promise (tb.handle id)))
    (readsHint : Reads hintSrc env path vals (Val.promise hint))
    (readsCell : Captured cellSrc env path vals (cellVal tb res s)) :
    Reads (Pool.leaseStep idSrc hintSrc cellSrc) env path vals
      (Val.tuple [leaseReplyVal res (lease s id).2,
        cellVal (tb.renew id hint) res (lease s id).1])

/-! ## The five statements as one

`pool_steps_agree` assembles the five step statements: each field is one of them, word for
word, and its proof cites that statement. So the plan derives the standing of the whole from
the five. -/

/-- **Pool's five steps agree with the abstract model**: one field for each step, at the
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

/-- **The five step statements hold** (the proposed claim `pool-steps-agree`, a part of
`pool-expansion-agrees`). Each field is one statement of this file. It establishes no order of
the wake across helpers, no cancellation law, no liveness, no close that waits and nothing of a
wrapper. Its consumer is the public law, in the slice of the public operations. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem pool_steps_agree : StepsAgree where
  lease := leaseStep_agrees
  giveBack := returnStep_agrees
  select := selectStep_agrees
  withdraw := withdrawStep_agrees
  close := closeStep_agrees

end Effect4.Pool.Model
