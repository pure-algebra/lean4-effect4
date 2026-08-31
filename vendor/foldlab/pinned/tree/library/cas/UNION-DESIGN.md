# Union (C1) — ratified design

**Status: RATIFIED by the operator 2026-08-29, in-session. ORDER IS
IDENTITY — confirmed explicitly. Stage 1 ordered to land. The
identity calls (1-5) and the staged obligations stand as proposed;
open ruling 2 resolves as proposed (both modes carried and admitted
immediately, validation semantics staged); R17's register revision
(order-is-identity clause, mode always spelled) is owed to the
register's next pass.**

Evidence: the pinned Effect 4 source (`Schema.ts` Union at :4912,
TaggedStruct :6185, TaggedUnion :6397, toTaggedUnion :6274, Literals
:4958, NullOr/UndefinedOr :5001/:5024; `SchemaAST.ts` Union :2820 with
`~sentinels` discrimination :2574; `SchemaIssue.ts` AnyOf :698 / OneOf
:757; `SchemaRepresentation.ts` Union :395-398), the estate's
normalizer (`CanonicalSchema.normalizeRepresentationJson`: "Union,
tuple, check, and reference order remain semantic and are never
rearranged"), the register (R14 `schema literals`, R16 `schema tagged
struct`, R17 `schema union [..]`), and the ratified plan (S4, S5).

## Why careful

Union is where Effect's power concentrates: `TaggedUnion` (the
workhorse of real Effect codebases), literal unions, `NullOr` sugar,
sentinel-driven discrimination, and two distinct semantics (`anyOf`
try-first vs `oneOf` assert-unique, with `OneOf` failures reporting
the *successes*). It is also where identity gets subtle: unlike struct
fields, **member order is semantic** — the estate's own TS normalizer
already rules this — so union identity is the ordered tree, and two
reordered unions are different codes at different addresses.

## The identity calls (proposed)

1. **Order is identity.** No canonical sorting of members — carried
   from the existing normalizer ruling. (Contrast: struct fields sort.
   The register should say this out loud when R17 is revised.)
2. **No flattening.** `union [a, union [b, c]]` ≠ `union [a, b, c]` —
   the tree is the identity, mirroring the FilterGroup left-nesting
   ruling (B-effect-identity hard call 5) and Effect, which does not
   flatten.
3. **No deduplication.** Effect does not dedupe; neither do we.
   Pathological for `oneOf` (a duplicated member can never validate
   uniquely) — that is a *validation* property, not an identity one.
4. **Empty unions refused at WF.** The empty union is `Never`'s job
   and `Never` is deferred (admission map rows 13-18). `WF` requires
   nonempty members, all members `WF`.
5. **Mode is data.** Both `anyOf` and `oneOf` carried, as an inductive
   (`UnionMode`, wire names exactly Effect's strings), Effect's
   default `anyOf` NOT defaulted on our side — the mode is always
   spelled (D4, deterministic elisions only).

## The carrier

`Ast.union (members : List Ast) (mode : UnionMode)` — additive, `.ref`
and everything else untouched. Names per S5/R17: `union` reads
identically in code, register, and prompt. `WF (.union ms m)` =
`ms ≠ [] ∧ ∀ member WF` (order free, per call 1).

Rev-1 wire shape (from `RepresentationSchema`, exactly):
`{"_tag":"Union","checks":[],"mode":"anyOf"|"oneOf","types":[...]}` —
note alphabetical keys hold (`_tag < checks < mode < types`), so the
Slice B unconditional canonicality theorem extends arm-wise.
`repNorm`: recurses into members, introduces **no new collapse** —
the literal-null member `union [x, lit null]` arrives as
`union [x, Null-keyword]` under the existing R13 collapse, which is
exactly Effect's `NullOr`.

## Staged obligations (the doom-loop control)

**Stage 1 — carriage (the C1 slice proper):** constructor, WF/wf,
rev-1 encoder + decoder + round trip + injectivity + canonicality
(all extend Slice B's proofs arm-wise), `repNorm` laws, the door
(ingest of union envelopes), fixture + TS hand mirror + pin. No El,
no value-plane codec. This makes unions store content — mintable,
addressable, materializable via Effect (`fromRepresentation` gives
the live validator for free, including sentinel discrimination).

**Stage 2 — denotation, discriminated first — LANDED:** `El` for a
general union is a dependent sum with try-order semantics — proof-heavy
and semantically muddy for `anyOf` overlap. The staged answer follows
Effect's own sentinel insight: land `El`/value-codec/`Described` only
for **discriminated unions** (every member a struct carrying the same
literal-tagged field — the `TaggedUnion` shape), where decoding is
deterministic by tag dispatch and the exactness laws are tractable.
This is also precisely what `deriving Described` for inductives emits
(DERIVING-DESIGN §2), so Stage 2 and the deriving growth are one
slice. General-union denotation stays a named obligation until a
consumer demands it.

What landed, and the two calls it forced:

- `El (.union ms m) = cond (discriminatedB ms) (ElMembers ms) Empty`.
  Discrimination is a DENOTATION precondition and stays out of
  `Ast.WF`, because `WF` is the store's admission discipline and
  Stage 1 already admits every union. The guard is what keeps Stage
  1's unconditional laws true rather than merely unchanged.
- The tag field is `_tag` (Effect's `TaggedStruct` name), required,
  string-literal, and FIRST — which the canonical-fields discipline
  makes a deterministic position.
- **D1, the generator's spelling.** Order is identity, so a GENERATOR
  has to pick one member order, and `deriving Described` picks
  ascending tag string rather than source order: shuffling an
  inductive's constructors must not move its address. The carrier
  still never rearranges anything; the sorting happens once, before a
  code exists. **R17's register row owes this clause too** — order is
  semantic to the carrier AND canonical at the generator.
- The mode a derived union carries is `oneOf`, spelled: the members are
  pairwise disjoint by construction, so the stronger reading is the
  true one, and D4 forbids eliding it.

Restrictions the constructor-alternative path enforces, each with its
own refusal message: non-recursive, non-mutual, non-nested (as before),
**parameter-free** (the union code has nowhere to spell type
parameters — the structure path keeps its parameter support), every
constructor field NAMED, no field named `_tag`, and no field whose JSON
name sorts before `_tag`.

**Stage 3 — validation semantics:** `oneOf` uniqueness as a checkable
property (the `OneOf`-successes shape) belongs to the validation-gen
lane (Effect's parser already implements it; the Lean side owes a
statement only when a gate consumes it).

## Open rulings for the operator

1. Confirm identity calls 1-5 (especially order-is-identity, stated
   once, register-visible).
2. Whether ADMISSION (not carriage) of `anyOf` unions should be gated
   until Stage 2 — i.e. the door accepts `oneOf`/tagged first, `anyOf`
   as data later — or both immediately. Proposal: both immediately
   (carriage is faithful; validation semantics are staged), recorded
   per A-1.
3. R17's register row gains the order-is-identity clause and the mode
   spelling; owed to the register's next revision pass.
