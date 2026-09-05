# Surface kind contract

Status: breaker packet, red, 2026-09-04 (wave 1b of
`docs/research/2026-09-04-surface-library-plan.md`, §3 as revised by §13.1)

Implementation (owed): `src/Effect4/Surface/Kind.lean` (four kinds in wave 1a,
extended in place to seven in wave 2a)

Battery: `Test/Surface/KindContract.lean`

Counterexamples: `E4-SURFACE-CE-001` through `E4-SURFACE-CE-005`

Witnesses: `Test/Counterexamples/Surface/Kind.lean`

## Purpose

`Kind` is the classification a `Representation` must have to occupy a slot of
a surface, and `Sch refs k` is the subtype of representations carrying a
kernel-checked proof of that classification. This is the TyXML transposition
of plan §3: a well-typed Lean term is a well-formed surface.

Plan §13.1 gives the slot table in full. Four kinds carry the v1 emitters
(`json`, `struct`, `text`, `void`); three more exist so that the carrier can
*express* the shapes rc.112 admits and the emitters refuse by rule
(`multipart`, `urlEncoded`, `stream`). Expressibility is the point: a carrier
that cannot spell a shape cannot carry a clause refusing it, so a refusal
about streaming would have nowhere to live and the model would be silently
narrower than it claims.

## Frozen public declarations

All in namespace `Effect4.Surface`.

```lean
inductive Kind
  | json
  | struct
  | text
  | void
  | multipart
  | urlEncoded
  | stream
deriving DecidableEq, Repr

def Kind.name : Kind → String
def Kind.all : List Kind

def kindCheck (refs : List Effect4.ReferenceEntry) :
    Nat → Kind → Effect4.Representation → Bool

structure Sch (refs : List Effect4.ReferenceEntry) (k : Kind) where
  rep : Effect4.Representation
  ok  : kindCheck refs 64 k rep = true

def Sch.of? (refs : List Effect4.ReferenceEntry) (k : Kind)
    (rep : Effect4.Representation) : Option (Sch refs k)

def Sch.propertyNames {refs : List Effect4.ReferenceEntry} {k : Kind} :
    Sch refs k → List String

def Sch.widenToStruct {refs : List Effect4.ReferenceEntry}
    (s : Sch refs .text) : Sch refs .struct

def Sch.widenToJson {refs : List Effect4.ReferenceEntry}
    (s : Sch refs .struct) : Sch refs .json

def JsonRepresentable (refs : List Effect4.ReferenceEntry)
    (rep : Effect4.Representation) : Bool

theorem kindCheck_text_struct (refs) (fuel) (rep) :
    kindCheck refs fuel .text rep = true → kindCheck refs fuel .struct rep = true

theorem kindCheck_struct_json (refs) (fuel) (rep) :
    kindCheck refs fuel .struct rep = true → kindCheck refs fuel .json rep = true

theorem kindCheck_void_iff (refs) (fuel) (rep) :
    0 < fuel → (kindCheck refs fuel .void rep = true ↔ rep.tag = .void)

theorem kindCheck_stream_json (refs) (fuel) (rep) :
    kindCheck refs fuel .stream rep = kindCheck refs fuel .json rep

theorem kindCheck_multipart_struct (refs) (fuel) (rep) :
    kindCheck refs fuel .multipart rep = kindCheck refs fuel .struct rep

theorem kindCheck_urlEncoded_text (refs) (fuel) (rep) :
    kindCheck refs fuel .urlEncoded rep = kindCheck refs fuel .text rep

theorem kindCheck_fuel_mono (refs) (k) (rep) (m n : Nat) :
    m ≤ n → kindCheck refs m k rep = true → kindCheck refs n k rep = true
```

`Sch.of?` and the anonymous constructor with a `by decide` proof are the only
two admitted ways into `Sch`. There is no `Sch.mk!`, no `Inhabited (Sch refs
k)` and no partial constructor that drops the equation.

Plan §13.1 names the three new kinds and does not say which representations
they admit; `Effect4.Representation` has no stream, multipart or form-encoded
node. This packet freezes the three equations above: the new kinds are the
existing sets under new names, and the distinction they carry is made by the
constructor that consumes them (`ResponseBody.stream` versus
`ResponseBody.json` in `surface-api.contract.md`), not by the representation.
See finding 7 of the wave-1b report.

## Observations

1. `kindCheck refs fuel k rep : Bool` on a closed `refs`, a closed `rep` and
   a literal fuel. Every other receipt in this packet is a function of it.
2. `Sch.of? refs k rep |>.isSome`, the constructive form.
3. `Sch.propertyNames s`, which the API contract's params law mentions.
4. The type of a slot, read by an ascribed definition. A slot that changes
   from `Sch refs .text` to `Sch refs .json` is a visible change of this
   contract even when no `#guard` moves.

## Acceptance conditions

- `.text` admits `string`, `number`, `boolean`, a string literal, a number
  literal, an `anyOf` of those, and an optional property of those, and admits
  them only as the property types of one non-nested `objects` node.
- `.text` refuses a property whose type is `objects`, `arrays`, `reference`
  or `suspend` (`E4-SURFACE-CE-001`).
- `.struct` admits any `objects` node whose property keys are all
  `PropertyKeyKind.string` and whose index-signature list is empty
  (`E4-SURFACE-CE-002`).
- `.void` admits a `Representation` whose tag is `.void` and nothing else
  (`E4-SURFACE-CE-003`), and is disjoint from `json`, `struct` and `text`.
- `.json` refuses every representation with no JSON inhabitant: `undefined`,
  `bigint`, `symbol`, `uniqueSymbol`, a bigint literal, `declaration`,
  `templateLiteral`, and an `objects` node with duplicate property keys
  (`E4-SURFACE-CE-004`). These are the refusals `Effect4.Arch.Accepts`
  already names; `kindCheck` does not invent a second refusal alphabet.
- `.json` admits an `objects` node with an index signature: that is the one
  representation `json` admits and `struct` refuses, so the two kinds are not
  the same set and `kindCheck_struct_json` is not an equality.
- `.stream`, `.multipart` and `.urlEncoded` are the three equations above.
- `kindCheck` is fuel bounded through `reference` (resolved in `refs`) and
  `suspend` (its thunk). Exhausted fuel answers `false`; that answer is a
  frontier of the check, not a refusal of the representation, and no `Refusal`
  constructor, error value or theorem may name it as one
  (`E4-SURFACE-CE-005`).
- The containment theorems hold for every fuel, not only 64.
- `kindCheck` reaches no axiom beyond `propext` and `Quot.sound`.

## Assurance allocation

Leaf receipts. `Kind` is a seven-constructor passive alphabet and `Sch` is a
subtype whose only content is one Boolean equation; neither carries a
judgment, a denotation or an interpreter, so neither opens a proof graph.

The receipts are the constructor census (one admitted and one refused
representative per kind), the eight theorems above with `#print axioms`
receipts in `Test/Surface/SurfaceAxiomReport.lean`, and the slot
ascriptions of `Test/Surface/ApiContract.lean`.

The leaf attaches to `SURFACE-PG-EMIT` through the `JsonRepresentable`
precondition every emitter requires, and to `SURFACE-PG-FACTS` through the
`kindMismatch` clause every carrier's `check` may return.

## What this contract does not claim

It does not claim a `Sch refs .json` value encodes to bytes any host accepts;
that is `surface-jsonschema.contract.md` and the harness. It does not claim
`kindCheck` agrees with rc.112's type-level `ParamsConstraint`,
`PayloadConstraint` or `SuccessConstraint`; the claim is one-directional and
the counterexample rows state it: what `kindCheck` admits, rc.112 constructs
without throwing. It does not order the kinds as a lattice. It does not claim
`.stream`, `.multipart` or `.urlEncoded` model anything of the wire format
they are named after: they are expressibility markers, the v1 emitters refuse
them by rule id, and `surface-emit.contract.md` carries those refusal rows.
