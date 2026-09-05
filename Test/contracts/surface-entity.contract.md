# Surface entity and domain contract

Status: breaker packet, red, 2026-09-04 (wave 1b of
`docs/research/2026-09-04-surface-library-plan.md` §4.1-§4.2)

Implementation (owed): `src/Effect4/Surface/Entity.lean`

Battery: `Test/Surface/EntityContract.lean`

Counterexamples: `E4-SURFACE-CE-009` through `E4-SURFACE-CE-015`,
`E4-SURFACE-CE-062`, `E4-SURFACE-CE-063`

Shared: `Test/contracts/surface-facts.contract.md` owns the `Refusal`
alphabet; this contract owns the entity and domain clause names and their
order.

Witnesses: `Test/Counterexamples/Surface/Entity.lean`

Fixtures: `Test/Surface/Fixtures.lean` (the `shop` domain: `User` keyed
by `id`, `Address`, `NotFound`)

## Purpose

An entity is a named struct representation with identity fields, a version, a
stance and a domain. A domain is a closed set of entities, one of which may be
active. The pair is the source of truth every other surface in this slice
refers to: an endpoint body, a tool result and a page's form all name an
entity, and the domain's reference table is the `refs` index of every `Sch`
in the packet.

The closure claim is the whole content: `Domain.refs` is exactly the domain's
entities, so a `Schema.reference` inside an entity either resolves inside the
domain or the domain is not well formed. There is no ambient reference table.

## Frozen public declarations

All in namespace `Effect4.Surface`.

```lean
inductive EntityStance
  | canonical
  | view
  | ingested
deriving DecidableEq, Repr

structure Entity where
  name        : String
  domain      : String
  version     : Nat := 1
  rep         : Effect4.Representation
  key         : List String
  stance      : EntityStance := .canonical
  description : Option String := none
deriving DecidableEq

structure Domain where
  name     : String
  entities : List Entity
  active   : Bool := false
deriving DecidableEq

def Domain.refs : Domain → List Effect4.ReferenceEntry

def Entity.propertyNames : Entity → List String
def Entity.requiredPropertyNames : Entity → List String

def Entity.rootBag : Entity → Effect4.Annotations
def Entity.identifier : Entity → Option String
def Entity.description : Entity → Option String
def Entity.propertyDescription : Entity → String → Option String

def Entity.check (dom : Domain) (e : Entity) : Except Refusal Unit
def Entity.WellFormed (dom : Domain) (e : Entity) : Prop :=
  Entity.check dom e = .ok ()

def Domain.check (dom : Domain) : Except Refusal Unit
def Domain.WellFormed (dom : Domain) : Prop := Domain.check dom = .ok ()

def Domain.entity? (dom : Domain) (name : String) : Option Entity

-- the clauses, lifted, so a capability can ask for exactly what it needs
def Entity.Named (e : Entity) : Prop
def Entity.Structured (dom : Domain) (e : Entity) : Prop
def Entity.HasKey (e : Entity) : Prop
def Entity.KeyRequired (dom : Domain) (e : Entity) : Prop
def Entity.KeyDistinct (e : Entity) : Prop
def Entity.InDomain (dom : Domain) (e : Entity) : Prop
def Entity.Described (e : Entity) : Prop
def Entity.PropertiesDescribed (dom : Domain) (e : Entity) : Prop
def Domain.Closed (dom : Domain) : Prop
def Domain.NamesDistinct (dom : Domain) : Prop

theorem Entity.wellFormed_iff (dom : Domain) (e : Entity) :
    Entity.WellFormed dom e ↔
      (Entity.Described e ∧ Entity.Named e ∧ Entity.Structured dom e ∧
        Entity.HasKey e ∧ Entity.KeyRequired dom e ∧ Entity.KeyDistinct e ∧
        Entity.InDomain dom e ∧ Entity.PropertiesDescribed dom e)

theorem Domain.wellFormed_iff (dom : Domain) :
    Domain.WellFormed dom ↔
      (Domain.NamesDistinct dom ∧ Domain.Closed dom ∧
        ∀ e ∈ dom.entities, Entity.WellFormed dom e)

theorem Entity.key_subset_props (dom : Domain) (e : Entity) :
    Entity.WellFormed dom e →
      ∀ k ∈ e.key, k ∈ Entity.requiredPropertyNames e

theorem Domain.wellFormed_entities (dom : Domain) :
    Domain.WellFormed dom → ∀ e ∈ dom.entities, Entity.WellFormed dom e

def Entity.document (dom : Domain) (e : Entity) : Effect4.Document
def Entity.json : Entity → Effect4.Json
def Entity.tsModule (dom : Domain) (e : Entity) :
    Option TypeScript.Module
def Entity.tsConstructor (dom : Domain) (e : Entity) :
    Option TypeScript.Expr

def Domain.json : Domain → Effect4.Json
def Domain.doc : Domain → Effect4.Document
def Domain.tsModule : Domain → Option TypeScript.Module

def spell (refs : List Effect4.ReferenceEntry) :
    Effect4.Representation → Option TypeScript.Expr
```

`EntityStance` is deliberately not called `Stance`. The plan spells both the
entity classification of §4.1 and the emitter classification of §5 `Stance` in
one namespace; the two are different alphabets and both are public, so this
packet freezes `EntityStance` here and reserves `Stance` for
`src/Effect4/Codegen/Emit.lean`. See finding 1 of the wave-1b report.

## Observations

1. `Entity.check dom e` and `Domain.check dom`, both
   `Except Refusal Unit`, compared against `.ok ()` or against an exact
   `.error` value. Every negative receipt names the clause it triggers.
2. `Domain.refs dom`, an ordered `List ReferenceEntry`, compared against a
   literal list in the battery so a reordering is visible.
3. `Entity.document dom e`, compared through `Effect4.Arch.accepts` and
   through `Effect4.Target.TypeScript.Schema.module?` for `isSome` only.
4. `spell refs rep`, an `Option Expr`; the battery observes `isSome`/`isNone`
   and the exact rendered bytes of the two smallest fixtures.

## Acceptance conditions

- `Domain.refs dom = dom.entities.map (fun e => ⟨e.name, e.rep⟩)`, in entity
  declaration order. This is an equation, checked by `#guard` on the fixture
  and stated as a theorem by the builder.
- `Entity.wellFormed dom e` holds exactly when: `e.name` is a legal
  `Effect4.Target.TypeScript.targetIdentifier`; `kindCheck dom.refs 64 .struct
  e.rep = true`; `e.key ≠ []` (`E4-SURFACE-CE-010`); every member of `e.key`
  is a property name of `e.rep` (`E4-SURFACE-CE-011`) that is not optional
  (`E4-SURFACE-CE-009`); `e.key` has no duplicates (`E4-SURFACE-CE-012`);
  and `e.domain = dom.name` (`E4-SURFACE-CE-015`).
- `Domain.wellFormed dom` holds exactly when entity names are distinct
  (`E4-SURFACE-CE-013`), every entity is well formed, every `reference` key
  reachable from every entity resolves in `Domain.refs dom`
  (`E4-SURFACE-CE-014`), and the reference graph is acyclic.
- `Entity.key_subset_props` is a `theorem`, not a `#guard`. It is the one
  law of this carrier that a generator downstream may rely on: an identity
  projection of an entity value is total.
- `Entity.rootBag e` is the annotation bag of `e.rep`'s root node, not a new
  field. An entity has a representation, so §15.1's "the root node of every
  surface value's representation" is literally available here; the carriers
  that have no representation (`Endpoint`, `Tool`, `Resource`, `Deployment`,
  `Site`) each gain an `annotations` field instead. See finding 8 of the
  wave-1b report.
- The annotation keys are the exact rc.112 bag key strings `"identifier"`,
  `"title"`, `"description"`, `"documentation"`, `"examples"`, `"default"`,
  `"deprecated"` (`Schema.ts:17105` and the surrounding annotation record).
  Wave 1a publishes them as `AnnotationKey`s in `src/Effect4/Surface/Annotate.lean`;
  the fixtures of this packet write the raw `AnnotationEntry` list so the
  battery does not depend on that module's spelling.
- `spell` returns `none`, never a partial or `Decl.raw` spelling, for a
  representation it cannot express. A `suspend` node is refused in v1
  (`Effect4.Surface.Refusal.recursiveSchema`), and so is a `declaration` node.
- `Domain.tsModule` emits references before referrers when the graph is
  acyclic, and `none` when it is not.

## Assurance allocation

Leaf receipts for the carriers plus one graph edge for the spelling.

`Entity`, `Domain` and `EntityStance` are passive records over strings,
naturals and one representation: leaf receipts (census, well-formedness
positive and negative guards, the two theorems, axiom report).

`spell` is a second rendering of a carrier that already has a canonical
rendering (`Target.TypeScript.Schema.module?`, the persisted-document
spelling). Per `AGENTS.md` a second representation requires an
explicit relation. That relation is **not** a Lean theorem in this packet: it
is the host receipt named in the plan §7,
`toJson(toRepresentation(<spelled>.ast))` deep-equals the emitted document
JSON. Until that receipt lands, the rule `surface.entity.constructor` stays
`Stance.emitted` and this contract claims only that `spell` is total on the
fixture fragment and `none` elsewhere. The edge is `SURFACE-PG-EMIT`
construction; the receipt row lives in `surface-emit.contract.md`.

## What this contract does not claim

It does not claim an entity value round-trips through any host codec. It does
not claim `Entity.tsModule` output typechecks; that is the harness gate. It
does not claim two domains compose, and it does not model cross-domain
references at all: an entity naming another domain is refused, not resolved
(`E4-SURFACE-CE-015`). The `active` flag now has exactly one semantics and no more: it turns clause
10 on. Nothing else in this packet reads it.
