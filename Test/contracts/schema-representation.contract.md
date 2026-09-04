# Schema representation tag census contract

Status: FROZEN breaker packet, 2026-08-31; its pre-implementation revision is
required to be RED, and fired findings are recorded below

Ruling input: `docs/SCHEMA-CUTOVER.md`, "Frozen rc.112 persisted census"

Implementation fence: `Effect4/Schema/Representation.lean`

Battery: `Effect4Test/Schema/RepresentationContract.lean`

Counterexamples: `test/counterexamples/REGISTER.md`, rows
`E4-SCHEMA-CE-017` through `E4-SCHEMA-CE-019`, with executable witnesses in
`Effect4Test/Counterexamples/Schema/`

## Claim boundary

This packet freezes the *tag* layer of Effect4's Schema representation: the
exact 22-member rc.112 persisted alphabet, its canonical census listing, and
the case-sensitive wire spelling of each member.

It deliberately does **not** freeze the payload carrier. `Representation`
itself, its per-tag persisted fields, `Check`, annotations, `Document`, and
`MultiDocument` remain unopened. In the obligation graph of
`docs/SCHEMA-CUTOVER.md` this packet targets the tag portion of `SC-REP-02`
(`Nodup` and lexical source completeness) and the tag portion of `SC-REP-03`
(structural equality and the exact dependent recursor). Those edges remain
open while this breaker packet is red. `SC-REP-01` (payload declaration and
persisted-field snapshot) and `SC-REP-04` (field admission matches the frozen
rc.112 constraints) are outside this packet and stay open.

No denotation, admission, codec, wire, profile, or document claim is made here.
A tag is a name, not a meaning.

## Proof-graph threshold

`RepresentationTag` needs a parent Schema representation proof graph because
it is the canonical, host-observable persisted node alphabet. Its source,
representation, spelling, trust, and coverage edges are cutover-critical and
must be composed before a representation cutover can close.

A proof graph is **not** required merely because a finite helper enumeration
exists. A leaf alphabet with no independent semantics, bridge, refinement, or
cutover claim is frozen by its local declaration contract, executable attacks,
and axiom receipt. The companion packet's five leaf alphabets attach those
receipts and any cross-alphabet relation to the parent Schema graph; they do
not each receive an otherwise empty graph.

## Source authority and its limit

The census is taken from the frozen table in `docs/SCHEMA-CUTOVER.md`, whose
authority pins are `effect@4.0.0-rc.112` and upstream revision
`2600f62f4532026928454dcea8d1c48557b3f942`.

The pinned bytes **are** on the build host, in the Foldlab checkout at
`library/effects/node_modules/effect/src/SchemaRepresentation.ts`, verified at
SHA-256 `a0a7a1537cfe3a9159a80210e3de92342cc9e98651f0e8273a75ccdcccae69bc`.
The lexical extractor used by the source census gate has been run against
those bytes and returned exactly the spellings frozen here. This is a scoped
source-extraction observation, not a proof of the payload model or denotation.

An earlier revision of this packet stated the bytes were absent. That was
wrong: the search pattern used only matched version-stamped directory names
and missed a plain `node_modules/effect`. Other copies on the host
(`beta.103`, `beta.91`, and some rc.109-111 vendor trees) are off-pin and are
not authority.

## CATEGORIES

- `inductive-data` — the tag alphabet is a finite, first-order enumeration;
- `specification-design` — census listing, duplicate freedom, and coverage are
  three separate obligations rather than one;
- `algebraic-laws` — wire spelling is injective and round-trips through
  parsing;
- `claim-scope` — a membership census is not a parser precedence, and a tag is
  not a payload.

## REQUIRES

1. Lean core and Std at the repository's pinned Lean 4.33.1 toolchain. No
   Mathlib, and therefore no `Fintype`; coverage is proved by case analysis
   rather than by a finiteness instance.
2. No dependency on `Effect4.Algebra`, `Effect4.Flow`, or `Effect4.Data`. The
   tag layer is free-standing.
3. Every declaration is safe and total. The repository trust gate rejects
   `unsafe`, `partial`, and `sorry`.

## Public declaration DAG

Binder names may differ. Names, constructor identity and order, result types,
and theorem propositions are frozen by the Lean battery. Constructor order is
observed through the exact dependent type of `RepresentationTag.rec`; a swap
that leaves `census` and every spelling unchanged still breaks the battery.

### D0 — the tag alphabet

```lean
inductive RepresentationTag where
  | declaration | reference | suspend
  | null | undefined | void | never | unknown | any
  | string | number | boolean | bigint | symbol
  | literal | uniqueSymbol | objectKeyword | enum
  | templateLiteral | arrays | objects | union
```

Exactly 22 constructors, in the source order of the frozen census table.
`DecidableEq`, `Repr`, and `Inhabited` are required.

The flat 22-constructor shape is an explicit **native API and minimality
ruling**. A parameterised `keyword (kind : KeywordKind)` representation could
preserve all twelve keyword-shaped values if `KeywordKind` itself retained all
twelve cases; shared field shape therefore does not refute that design. This
packet nevertheless freezes the flat carrier because the extra helper
alphabet would duplicate the same nominal distinction without adding a new
semantic layer. Any later alternative must be a separately named view with an
explicit conversion law, not a replacement for this canonical carrier.

The constructors are **nominal**. Several carry identical persisted field
shapes in rc.112 — the eleven keyword tags and `objectKeyword` all persist as
optional annotations plus ordered checks — and they are still distinct tags,
because the persisted `_tag` string is observable. Field-shape equality is not
a licence to merge constructors.

### D1 — the canonical census

```lean
def RepresentationTag.census : List RepresentationTag
```

The listing of all 22 tags in the frozen table's order.

This order is a **membership census** and an exact source/API snapshot. It is
not a claim about parser precedence, decode order, union member preference, or
any other operational ordering. No semantic or coverage theorem interprets a
position as precedence; the coverage theorem below is stated so that it holds
under any permutation, while the battery separately freezes the exact ordered
listing.

### D2 — wire spelling

```lean
def RepresentationTag.tagName : RepresentationTag -> String
def RepresentationTag.ofTagName : String -> Option RepresentationTag
```

`tagName` returns the exact case-sensitive rc.112 `_tag` string:

```text
Declaration Reference Suspend Null Undefined Void Never Unknown Any String
Number Boolean BigInt Symbol Literal UniqueSymbol ObjectKeyword Enum
TemplateLiteral Arrays Objects Union
```

`ofTagName` recognises exactly those strings and nothing else.

The list above is read **positionally against the census only as a
presentation convenience**. What this packet freezes is the tag-to-spelling
*map*, member by member. An ordered `census.map tagName = …` equation does not
freeze that map: it is invariant under applying one permutation to `census`
and the same permutation to `tagName`, which leaves the equation true while
every persisted `_tag` string moves to a different constructor. The battery
therefore pins each of the 22 tags pointwise, in both directions, and the
ordered equation is retained only to pin the census listing on top of that.

## ENSURES

The builder must prove these exact edges without `sorry`, `admit`, custom
axioms, unsafe declarations, partial declarations, or `Classical.choice`:

1. `census_length` — `census.length = 22`.
2. `census_nodup` — `census` has no duplicate entry.
3. `mem_census` — every `RepresentationTag` occurs in `census`.
4. `tagName_injective` — equal wire spellings force equal tags.
5. `ofTagName_tagName` — `ofTagName t.tagName = some t` for every tag.
6. `tagName_ofTagName` — `ofTagName s = some t` implies `t.tagName = s`.
7. per-tag wire spelling — for each of the 22 tags *individually*, `tagName`
   returns the exact string listed in D2 for that tag, and `ofTagName` returns
   that tag from that string. This is 44 ground equations rather than a
   quantified law, so it adds no exported declaration and is discharged by the
   battery. Obligations 1 through 6 and the ordered census equation are all
   satisfiable by a permuted spelling map; this one is not.

Obligations 1, 2, and 3 are stated separately because deriving any one from
the other two needs a cardinality argument this packet deliberately does not
import. They are **not** logically independent: length plus duplicate freedom
implies coverage by pigeonhole, and duplicate freedom plus coverage forces the
length. What `E4-SCHEMA-CE-019` refutes is the weaker belief that
`census_length = 22` alone establishes the census.

Obligation 4 is likewise **not** independent of obligation 5. Given
`ofTagName_tagName`, injectivity follows in three lines: rewrite
`a.tagName = b.tagName` inside `ofTagName a.tagName = some a` and read `a = b`
off the resulting `some b = some a`. `Effect4/Schema/Representation.lean`
proves it exactly that way and its docstring says so. Obligation 4 is listed
separately because it is the statement a consumer of the wire layer cites, and
because it survives a later reformulation of recognition; it is not listed
because it carries content the round-trip law lacks. No pairwise comparison of
the 484 tag pairs is performed or required.

Obligations 5 and 6 together state that `ofTagName` is a partial inverse of
`tagName` on its domain. Neither states that `ofTagName` is total, and neither
licenses any claim about how a full representation decodes.

## Falsification battery

- `E4-SCHEMA-CE-017`: identical persisted field shapes do not license semantic
  collapse: all twelve keyword-shaped cases remain distinct inhabitants with
  distinct spellings. This witness alone does **not** forbid a lossless
  parameterised representation; the exact recursor separately freezes the
  flat native API/minimality ruling.
- `E4-SCHEMA-CE-018`: wire spelling is exact and case-sensitive; a plausible
  lowercase or camelCase variant is rejected by `ofTagName`.
- `E4-SCHEMA-CE-019`: a 22-entry listing that repeats one tag and omits
  another has the right length and still fails both duplicate freedom and
  coverage.

`E4-SCHEMA-CE-001` through `E4-SCHEMA-CE-016`, reserved by
`docs/SCHEMA-CUTOVER.md`, attack the payload, denotation, codec, and wire
layers. They are owned by later packets and are **not** discharged here. See
`test/counterexamples/schema/ATTACKS.md`.

## Decrease, frame, and trust

Every function is a finite case split over a 22-constructor enumeration or a
finite list recursion. Nothing mutates state, invokes a handler, executes a
host callback, or allocates a resource. The frame is the tag value alone.

The public proof ceiling is Lean's kernel plus the repository allowlist
`[propext, Quot.sound]`. No custom axiom or `Classical.choice` is permitted,
and `Quot.sound` is not reached. The builder records the actual receipt for
every exported theorem.

Exactly nine exported theorems across this packet and its companion elaborate
through `propext`, and they are of two kinds, not one:

- the six `mem_census` coverage proofs — `RepresentationTag`, `UnionMode`,
  `CheckTag`, `LiteralKind`, `EnumValueKind`, and `PropertyKeyKind` — which are
  finite list-membership decisions; and
- the three partial-inverse proofs `RepresentationTag.tagName_ofTagName`,
  `UnionMode.modeName_ofModeName`, and `CheckTag.tagName_ofTagName`, which are
  not membership proofs at all. They reach `propext` through the `simp` call
  that discharges the `none` branch of a `split` over the recogniser, not
  through any list.

Every other exported theorem in both packets depends on no axiom. An earlier
revision of this section described the `propext` surface as list-membership
proofs alone; the allowlist always covered the three partial inverses, but the
prose named a narrower set than the receipt.

## Source-extraction evidence obligation

The `SC-REP-CENSUS-PIN` evidence edge is closed **only for lexical extraction
at the named pin**. `./scripts/check-schema-census.sh` extracted 22
representation tag spellings and 2 check tag spellings from the pinned
`SchemaRepresentation.ts`; that extracted set agrees with the set frozen by
this packet. Constructor and census order are frozen separately by the exact
recursor and ordered battery above. This does not establish payload, decoder,
denotation, or generated-host fidelity.

The gate reports pin-matched evidence only when the supplied file matches the
pinned digest, and refuses other bytes unless `--dry-run` is given. Its drift
detection is exercised by `./scripts/test-schema-census-gate.sh`, whose finite
suite shows that ten specified defects are rejected, including a tag copied
across the nominal family boundary. This is detector
reaction evidence, not an exhaustive theorem about every possible defect.

## RED and acceptance commands

The breaker records the intended red state with:

```text
lake env lean Effect4Test/Schema/RepresentationContract.lean
```

It must fail only because the frozen declarations do not yet exist. After
implementation, acceptance additionally requires:

```text
lake env lean Effect4Test/Schema/RepresentationContract.lean
lake clean && lake build
```

The builder then records the axiom receipt without editing this contract or
its Lean battery.


## Fired findings

### `E4-SCHEMA-CE-017` excluded less than it claimed

BROKE: the row and `ATTACKS.md` said the attacked design was merging the
twelve shape-identical keyword tags into one `keyword (kind : KeywordKind)`
constructor, and that the battery excluded it.

LAW: against the original battery, an independent reviewer built exactly that
design and it passed all six ENSURES theorems, the source census example, and
every original `E4-SCHEMA-CE-017` and `-018` example. It does not pass the
current exact recursor snapshot; that later check enforces the separately
ratified native API ruling.

CLASS: claim scope. The examples witness *inhabitant*-level distinctness, and a
parameterised type has the same 22 inhabitants and the same 22 spellings. The
prose conflated constructor count with inhabitant count.

FIXED-BY: the row now claims only what it witnesses — semantic distinction of
the twelve keyword-shaped inhabitants and their spellings. Separately, the
operator froze a native minimality/API ruling: `RepresentationTag` remains a
flat 22-constructor carrier so a second `KeywordKind` alphabet is not minted
without a distinct semantic role. The exact `RepresentationTag.rec` signature
mechanically freezes that carrier and its constructor order. The API ruling is
not presented as a theorem derived from field shape.

### `E4-SCHEMA-CE-019` independence was overclaimed

BROKE: "Any two of them are satisfiable by a wrong listing", and the matching
Lean docstring "none of the three implies another".

LAW: mechanized by the reviewer against these declarations — length plus
duplicate freedom implies coverage by pigeonhole
(`List.Nodup.length_le_of_subset`, Lean core), and duplicate freedom plus
coverage forces the length.

CLASS: claim scope. The register row was already honest; only the contract
prose and the docstring overreached.

FIXED-BY: both restated. The three stay separate because deriving one needs a
cardinality argument the packet does not import, not because they are
independent.

### Source-authority section rewritten after freeze

BROKE: the packet was frozen stating the pinned bytes were absent from this
checkout, and that section was later rewritten in place when they were found.

LAW: the bytes are present; the original search pattern only matched
version-stamped directory names.

CLASS: process. A frozen packet should record a finding rather than have its
prose edited silently. The rewrite was disclosed in the text but not recorded
here.

FIXED-BY: this entry. The declaration DAG and every ENSURES row were unchanged
by that rewrite.

### Wire spellings were pinned per census position, not per tag

BROKE: the ENSURES list carried no per-tag spelling obligation. The only
statement tying any spelling to any tag was the single battery example
`census.map tagName = expectedTagNames`.

LAW: that equation is invariant under applying one permutation to `census` and
the same permutation to `tagName`. Executed against the frozen packet:
swapping the `Declaration` and `Reference` spellings in both `tagName` and
`ofTagName`, and reordering `census` to match, left `lake build
Effect4.Schema.Representation`, `RepresentationContract.lean`,
`SubAlphabetContract.lean`, `WireSpellingDrift.lean`,
`SemanticTagSeparation.lean`, and `CensusCoverage.lean` all at exit 0. Only
five constructors were incidentally pinned elsewhere — `objectKeyword`,
`uniqueSymbol`, `templateLiteral`, and `bigint` in `WireSpellingDrift.lean`,
and `null` in `NoNullLiteralKind.lean` — leaving the other seventeen free to
permute. Roughly 3.6e14 spelling maps satisfied the entire packet, and every
one of them but the intended map emits a wrong persisted `_tag`.

WITNESS: the `spelling-permutation` mutant of
`scripts/test-schema-alphabet-mutations.sh`. It remains source-buildable, it
was verified to pass the pre-repair battery and every counterexample module,
and it is killed by the repaired battery.

CLASS: specification design. This is the defect `E4-SCHEMA-CE-018` already
names — pin the case-sensitive wire string *per tag*. The row's claim was
correct; the discharge was implemented per census position instead, which is a
strictly weaker statement.

FIXED-BY: ENSURES obligation 7 and a new paragraph under D2 state the per-tag
scope and why the ordered equation cannot carry it.
`Effect4Test/Schema/RepresentationContract.lean` gains 22 pointwise `tagName`
examples and 22 pointwise `ofTagName` examples. The companion packet's battery
gains the same treatment for its spelled alphabets. The mutation gate carries
the permutation as its fifth specified mutant. No implementation declaration
changed: every pointwise obligation was already true of
`Effect4/Schema/Representation.lean`, so no wire-format defect was live.

### `tagName_injective` non-independence was left unstated

BROKE: the ENSURES list corrected exactly this class of overclaim for
obligations 1, 2, and 3 in the `E4-SCHEMA-CE-019` finding above, then one
paragraph later left obligations 4 and 5 side by side with no relation stated,
implying that injectivity is separate content.

LAW: `tagName_injective` follows from `ofTagName_tagName` in three lines, and
`Effect4/Schema/Representation.lean` proves it that way and says so in its
docstring. The companion packet's `UnionMode.modeName_injective` and
`CheckTag.tagName_injective` are derived identically.

CLASS: claim scope. No theorem is wrong and no receipt changes; the ENSURES
list presented six independent edges where there are five and a corollary.

FIXED-BY: a paragraph after the ENSURES list stating the derivation and why
the corollary is still listed separately, and the equivalent paragraph in the
companion packet. The declaration set and every ENSURES proposition are
unchanged.

### The `propext` surface was described more narrowly than the receipt

BROKE: "Finite list-membership proofs may elaborate through `propext`", which
names one kind of proof.

LAW: `#print axioms` over the exported theorems of this packet and its
companion returns `[propext]` for nine of them — the six `mem_census` proofs,
plus `RepresentationTag.tagName_ofTagName`, `UnionMode.modeName_ofModeName`,
and `CheckTag.tagName_ofTagName`. Those last three are partial-inverse proofs
by `unfold`, `split`, and `simp at h`; no list occurs in them. Every other
exported theorem depends on no axiom, and `Quot.sound` is never reached.

CLASS: claim scope. Not a trust violation: the allowlist `[propext,
Quot.sound]` covers all nine, and the sentence was permissive rather than
prohibitive. The prose simply named a smaller `propext` surface than the
receipt shows.

FIXED-BY: the trust section now names the actual nine and separates the two
kinds. No proof, allowlist entry, or receipt changed.
