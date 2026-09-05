# Surface capabilities and derivations contract

Status: breaker packet, red, 2026-09-04 (wave 1b, for wave 2e of
`docs/research/2026-09-04-surface-library-plan.md` §14.3-§14.7)

Implementation (owed): `src/Effect4/Codegen/App.lean`, `Effect4.Surface.Model (planned module; the packet remains red)`

Battery: `Test/Surface/DeriveContract.lean`

Counterexamples: `E4-SURFACE-CE-071` through `E4-SURFACE-CE-075`

Witnesses: `Test/Counterexamples/Surface/Derive.lean`

Depends on: `Test/contracts/surface-facts.contract.md` (the lifted clauses and
each carrier's `wellFormed_iff`)

## Purpose

A **capability** is a surface value together with the facts one has chosen to
prove about it: a structure whose proof fields default to `by decide`, so
writing `{ entity := doc }` discharges them and a failure names the clause. A
**derivation** is a function out of a capability, so it cannot be called
without the proof in hand, and the library proves once and generically that
what it derives is well formed.

The payoff is exact and worth stating plainly, because it is the only reason
this layer exists: `getEndpoint_wf` is a theorem about the *builder*, proved
by unfolding it, not a `decide` over its output. Kernel work stays linear in
the size of the fact rather than the size of the derived value, and there is
exactly one place a derived endpoint could be ill-formed.

This adds no carrier. A capability is a subtype over the rows of §4, and
"the type is the schema" still holds.

## Frozen public declarations

All in namespace `Effect4.Surface`.

```lean
structure Identified (dom : Domain) where
  entity      : Entity
  described   : Entity.Described entity := by decide
  hasKey      : Entity.HasKey entity := by decide
  keyRequired : Entity.KeyRequired dom entity := by decide

structure Creatable (dom : Domain) extends Identified dom where
  create   : Entity
  subshape : Entity.Subshape dom create entity := by decide

structure Updatable (dom : Domain) extends Identified dom where
  patch     : Entity
  optional  : Entity.AllOptional patch := by decide
  subshape  : Entity.Subshape dom patch entity := by decide

structure Listable (dom : Domain) extends Identified dom where
  wrapper  : Entity
  wraps    : Entity.WrapsList dom wrapper entity := by decide

structure TaggedError (dom : Domain) where
  entity      : Entity
  status      : Nat
  described   : Entity.Described entity := by decide
  tagged      : Entity.HasTag entity := by decide
  errorStatus : 400 ≤ status ∧ status ≤ 599 := by decide

structure Closed where
  domain : Domain
  closed : Domain.WellFormed domain := by decide

structure Provided (refs : List Effect4.ReferenceEntry) where
  deployment : Deployment
  apis       : List (Api refs)
  wellFormed : Deployment.WellFormed deployment := by decide
  satisfies  : Deployment.Satisfies deployment apis := by decide

def Entity.Subshape (dom : Domain) (small large : Entity) : Prop
def Entity.AllOptional (e : Entity) : Prop
def Entity.WrapsList (dom : Domain) (wrapper item : Entity) : Prop
def Entity.HasTag (e : Entity) : Prop

def Identified.keyParams {dom} (i : Identified dom) : Sch dom.refs .text
def Identified.keyPath {dom} (i : Identified dom) : Path
def Identified.getEndpoint {dom} (i : Identified dom) (plural : String) :
    Endpoint dom.refs
def Identified.deleteEndpoint {dom} (i : Identified dom) (plural : String) :
    Endpoint dom.refs
def Creatable.createEndpoint {dom} (c : Creatable dom) (plural : String) :
    Endpoint dom.refs
def Updatable.updateEndpoint {dom} (u : Updatable dom) (plural : String) :
    Endpoint dom.refs
def Listable.listEndpoint {dom} (l : Listable dom) (plural : String) :
    Endpoint dom.refs
def Identified.repository {dom} (i : Identified dom) : ServiceRow
def Creatable.crudGroup {dom} (c : Creatable dom) (plural : String) :
    Group dom.refs

theorem Identified.getEndpoint_wf {dom} (i : Identified dom) (plural : String) :
    Endpoint.WellFormed (i.getEndpoint plural)
theorem Identified.deleteEndpoint_wf {dom} (i : Identified dom) (plural : String) :
    Endpoint.WellFormed (i.deleteEndpoint plural)
theorem Creatable.createEndpoint_wf {dom} (c : Creatable dom) (plural : String) :
    Endpoint.WellFormed (c.createEndpoint plural)
theorem Updatable.updateEndpoint_wf {dom} (u : Updatable dom) (plural : String) :
    Endpoint.WellFormed (u.updateEndpoint plural)
theorem Listable.listEndpoint_wf {dom} (l : Listable dom) (plural : String) :
    Endpoint.WellFormed (l.listEndpoint plural)
theorem Creatable.crudGroup_wf {dom} (c : Creatable dom) (plural : String) :
    Group.WellFormed (c.crudGroup plural)
theorem Identified.getEndpoint_paramsMatchPath {dom} (i : Identified dom) (plural : String) :
    Endpoint.ParamsMatchPath (i.getEndpoint plural)

-- Effect4.Surface.Model (planned module; the packet remains red)
def Model.Store (key entity : Type) : Type := List (key × entity)
def Model.Store.get {key entity} [DecidableEq key] :
    Model.Store key entity → key → Option entity
def Model.Store.put {key entity} [DecidableEq key] :
    Model.Store key entity → key → entity → Model.Store key entity
def Model.Store.delete {key entity} [DecidableEq key] :
    Model.Store key entity → key → Model.Store key entity

theorem Repository.get_put {key entity} [DecidableEq key]
    (s : Model.Store key entity) (k : key) (e : entity) :
    (s.put k e).get k = some e
theorem Repository.get_delete {key entity} [DecidableEq key]
    (s : Model.Store key entity) (k : key) :
    (s.delete k).get k = none
theorem Repository.put_put {key entity} [DecidableEq key]
    (s : Model.Store key entity) (k : key) (e e' : entity) :
    (s.put k e).put k e' = s.put k e'

structure Contract where
  service  : String
  name     : String
  sentence : String
deriving DecidableEq, Repr

def Identified.contracts {dom} (i : Identified dom) : List Contract
```

## Observations

1. **Elaboration.** `({ entity := userEntity } : Identified shop)` elaborates
   or it does not. A capability constructed on a value whose facts hold is a
   positive receipt; one on a value whose facts fail is a **compile-negative**
   and is recorded as such per `AGENTS.md`: the battery keeps the
   rejected term in a comment beside the mutant it names, because a failing
   elaboration cannot be a `#guard`.
2. `Endpoint.check dom.refs (i.getEndpoint "users") = .ok ()`, a `#guard`.
3. The derivation theorems, used rather than restated: the battery states
   `Endpoint.WellFormed (i.getEndpoint "users")` by applying
   `getEndpoint_wf`, never by `decide`. A battery that proved it by `decide`
   would pass even if the theorem were vacuous, which is the whole failure
   this layer is meant to remove.
4. The three store equations, over a small literal store.

## Acceptance conditions

- Every proof field of every capability is an auto-param whose tactic is
  exactly `by decide`. No `simp`, no `omega`, no `native_decide`, no
  typeclass-resolved fact, no proof cache, no search (plan §14.6's explicit
  exclusions). A user who cannot `decide` a fact writes the term by hand and
  the API does not change (`E4-SURFACE-CE-071`).
- A capability names facts and never behaviour, extends rather than repeats,
  and carries no field an existing carrier already owns
  (`E4-SURFACE-CE-072`).
- `Identified.getEndpoint` builds its `params` from the key, so
  `ParamsMatchPath` is true by construction:
  `getEndpoint_paramsMatchPath` is proved by unfolding the builder and
  `getEndpoint_wf` uses `Endpoint.wellFormed_iff`, not `decide`
  (`E4-SURFACE-CE-073`).
- A derived value is an ordinary row. Taking `i.getEndpoint "users"`, adding
  an error and checking the result with `decide` works exactly as it does for
  a hand-written endpoint; derivation is a starting point, not a frame.
- `Identified.keyParams` is `Sch dom.refs .text` by a theorem from
  `keyRequired` and the key fields' types, not by a `decide` at each use
  site.
- Derived endpoints satisfy the semantic layer: `getEndpoint` writes an
  `identifier` and a `description` into the endpoint's bag from the entity's
  own (plan §15), so a derived endpoint is not refused by clause 1 or 2 of
  `surface-api.contract.md` (`E4-SURFACE-CE-074`).
- A derivation that cannot be given its theorem in the landing packet does
  not land. It is an owed row in this contract's status line, named as owed;
  it is not landed with a `#guard` standing in for the theorem
  (`E4-SURFACE-CE-075`).
- The three `Repository` theorems are proved over `Model.Store` and are
  theorems today. The *implementation* they will one day be replayed against
  is not claimed: `Identified.repository`'s emitter stance stays
  `Stance.emitted`, and the docstring says the contract is about the model.

## Assurance allocation

Graph edge `SURFACE-PG-DERIVE`, obligations:

| obligation | evidence at landing |
| --- | --- |
| construction | each capability elaborates on the fixture with defaulted proofs; each compile-negative is recorded |
| laws | the six `_wf` theorems and `getEndpoint_paramsMatchPath`, each proved over the capability and not over a fixture |
| bridges | `wellFormed_iff` of `surface-facts.contract.md`: without it the `_wf` theorems cannot be stated from three clauses |
| model | the three `Repository` theorems over `Model.Store` |
| counterexamples | `E4-SURFACE-CE-071` through `E4-SURFACE-CE-075` |

## What this contract does not claim

It does not claim any emitted repository implementation satisfies the three
store equations; that is a later wave's harness, and Char's `characterize`
over the model is the named instrument. It does not claim the capability set
is complete: the seven are the ones the derivations need, and plan §14.3 says
nothing else lands until a derivation needs it. It does not claim derivations
compose (there is no capability algebra beyond `extends`), and it does not
claim a capability with more facts derives strictly more, only at least as
much. It does not add a typeclass, an instance search or a tactic.
