# Effect4 port manifest

Effect4 now has one independent algebra carrier and a mechanically bounded
cutover inventory. Foldlab remains the downstream compatibility target; no
Foldlab module is an Effect4 dependency.

Status: P1/P3 closure active, 2026-08-31. The generic algebra is implemented
and its current breaker battery is green, but independent review found
retained source declarations that still require row-level dispositions.
Schema, flow, runtime, concurrency, target, and Foldlab compatibility rows
remain open until their declared assurance routes close: proof graphs for
semantic owners, and exact leaf receipts for passive finite declarations.

## Authority pins

| Authority | Exact pin or digest | Role |
| --- | --- | --- |
| Foldlab source | commit `feb29321fd50204aa338209d313e84a3f8b71c66` | Source declarations, tests, and downstream compatibility target |
| Effect4 toolchain | `leanprover/lean4:v4.33.1`; `lean-toolchain` SHA-256 `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` | Kernel, elaborator, compiler, and standard library |
| Effect runtime | `effect@4.0.0-rc.112`; upstream commit `2600f62f4532026928454dcea8d1c48557b3f942`; tree `648a01b9c249448716e1a9474f511b17898f9d93` | Sole Effect TypeScript API and runtime semantic authority |
| Installed Effect package | integrity `sha512-wXxwuh1Ywnv4cPRM3Wfa0vDwuOHnZ1TsTgHJkG9XgzND6inhBH9n1vBxhg3iIXOia/OrpmvVmd3lrD4vq6bF3A==` | Exact host bytes exercised by Foldlab |
| TypeScript | `typescript@7.0.2`; integrity `sha512-8FYau96o3NKOhbjKi/qNvG/W5jhzxkbdm5sj9AbZ/5T5sWqn3hJgLfGx27sRKZWTvyzCP8dLRBTf5tBTSRVUNA==` | Target typechecker |
| Installed Effect diagnostic gate | `@effect/tsgo@0.38.0`; integrity `sha512-eazN0kX+WNT1jNjIm/l5esnkpKVfd1wNh2ig0pfaULKuI2PZh0JwjbepDPUr6MWx5cqOiUgwStNf5hGhg2w00g==` | Auxiliary target diagnostic gate; never semantic authority |
| Language-service research clone | commit `5e4d380b6fcd20f048dd8d41515bcd9ea47ffda4`; Effect v4 harness at `4.0.0-beta.107` | Diagnostic designs and negative fixtures, version-indexed |
| PolyFun acceptance probe | commit `3937f7ff0830cca33d6b35a24aef55bcbe3b6bc9`; Lean `v4.33.1`; Mathlib `v4.33.1`; cslib `v4.33.1` | Prior-art API and optional comparison source; not an Effect4 dependency |

Three `internal/schema/` files are cited by module annotations and by the
payload contract but appeared in no authority table. They are recorded here at
first use, against the installed package bytes:

| Cited host file | SHA-256 |
| --- | --- |
| `internal/schema/toRepresentation.ts` | `677449c734ac6373598a81207ba0573f86fb8bd2c9fb25d1369aa1e710d614a2` |
| `internal/schema/fromRepresentation.ts` | `0b95c360800d3c1dfe3e6c5683f79265fa7217494c8ce9cedb5c6dcbf936d82e` |
| `internal/schema/annotations.ts` | `4b3bedcae279fcb3a1dff4e8eb718d42f450d59c8b45912070a586adcdcb077c` |

`toRepresentation.ts` is the one that matters most: it is the sole
implementation of the live-AST-to-persisted-representation arrow the cutover
depends on, and it was unpinned while being cited as evidence.

The Effect npm version and upstream revision come from Foldlab's
`.reference/provenance/sources.lock.json` runtime row. The installed package
bytes remain a separate pin because an upstream tag does not prove what a
package manager placed on disk. This distinction is material for Schema:
installed `Schema.ts` has SHA-256
`9358710e2c0d613371d8feeeccb3716fe98a43f67e6aa1076b00d4079a258784`,
while the pinned upstream file has
`f0ecfa4511a62c2eb7ed820449d12653a2bbb8ef82ead842189a56b503d0de2f`.
The exact matching and differing source/declaration digests are recorded in
`docs/SCHEMA-CUTOVER.md`.

## Dispositions

Every source row receives one of these dispositions. A refusal explains why
the row is outside a profile; it is not an additional disposition.

**This is a rule, and it is not yet satisfied on the Effect side.** A survey of
the `Schema.ts` public surface at the pin (`docs/SCHEMA-SURFACE-SURVEY.md`)
found 348 exports carrying a runtime value, established by two routes — a
declaration-site count and `Object.keys` over the shipped `dist/Schema.js`,
which agree. Six whole faces of that surface appear in neither this file nor
`docs/SCHEMA-CUTOVER.md`: `Optic`, `Bottom`, `TemplateLiteralParser`,
`StandardSchema`, `JsonSchema`, and `Formatter`, covering roughly 31 exported
names including the optics and `Iso` face, Arbitrary, Equivalence, JSON Schema,
Standard Schema V1, and JSON Patch/XML. A `grep -ic` for each returns zero in
both documents.

Those rows are therefore undisposed, not refused. The rule above states the
requirement; it does not report the current state, and no gate checks the two
against each other.

| Disposition | Meaning |
| --- | --- |
| `owned` | Effect4 owns the only generic carrier and its laws. |
| `split` | Generic declarations move to Effect4; domain declarations remain downstream. |
| `downstreamAdapter` | Foldlab retains the type and later relates it to Effect4 in both directions. |
| `separateCalculus` | The family has its own syntax, indices, and semantics rather than becoming a core operation. |
| `derivedExpansion` | The surface lowers to already admitted operations or another admitted calculus. |
| `foreignBoundary` | A stable registered identity crosses to host code; arbitrary closures are not canonical content. |
| `targetOnly` | The item belongs to runtime execution or target tooling, not canonical program data. |
| `evidenceOnly` | A workshop, old implementation, or dependency informs a contract but supplies no carrier. |
| `excludedInternal` | A package-private implementation has no public reification row. |

## Generic algebra extraction

The source files below were hashed at the Foldlab pin. The Effect4 contract is
`test/contracts/algebra-extraction.contract.md`; its central attacks are
`E4-ALG-CE-001` through `E4-ALG-CE-007`.

| Foldlab source | Retained span | SHA-256 | Effect4 owner | Disposition |
| --- | ---: | --- | --- | --- |
| `library/cas/Cas/Lang/Sig.lean` | 1-27 | `91e9d984fead2a36c4503bb8db979e8f085123db754a655846888aac41e87cd6` | `Effect4/Algebra/Signature.lean` | `owned`; operation and answer universes generalized |
| `library/cas/Cas/Lang/Prog.lean` | 1-54 | `a8ac15632d155f9558db1969f2a25faf548e337c35b584f54316d5aba0f958aa` | `Effect4/Algebra/Program.lean` | `owned`; well-founded higher-order proof carrier only |
| `library/cas/Cas/Lang/Handler.lean` | 39-67 | `7170bd9c6de8743d10fff712644fa1d6ce59100e5dc33e0458b17897de933bf9` | `Effect4/Algebra/Handler.lean` | `split`; generic handler moved, CAS reference handler retained |
| `library/cas/Cas/Lang/Representation.lean` | 35-118 | `5ca0f4cfeeb396c0f084d547a72825ddbe8a6c6a37e0786dbed9e94d68b652a8` | `Effect4/Algebra/Laws.lean` | `split`; generic laws moved, CAS observation retained |
| `library/cas/Cas/Lang/Representation.lean` | 119-128 | same file digest | `Effect4/Semantics/Equivalence.lean` | open `downstreamAdapter` |
| `library/cas/Cas/Lang/Tower.lean` | 63-85 | `02b348347431dd80544427bb93fd0c0878b37ac010196ee1faf0c5925773027a` | `Effect4/Algebra/Handler/Composition.lean` | `split`; generic composition moved, byte plane retained |
| `library/cas/Cas/Backend/SumAlgebra.lean` | 172-173, 196-467 | `d6a67f6efa75d81662f79945ce84ce54e83392b786bd9ce5a4884c01c2f7070b` | `Effect4/Algebra/Sum.lean` | `split`; generic sum laws moved |
| `library/cas/Cas/Backend/Universal.lean` | 127-223 | `cce4f2a50a7e2a2e8b57b4de1a82f90c86efcb9749683795fd2b9e96d2ad8010` | `Effect4/Algebra/MonadLaws.lean` | `split`; minimal equation bundles moved |
| `library/cas/Cas/Backend/Universal.lean` | 294-349, 469-625 | same file digest | `Effect4/Algebra/Universal.lean` | `split`; freeness and model initiality moved |
| `library/cas/Cas/Backend/Universal.lean` | 739-749, 757-768, 785-790 | same file digest | `Effect4/Algebra/Handler/Category.lean` | `split`; category laws and endomorphism monoid moved |

There is one `Signature`, one `Program`, and one `Handler` family in Effect4.
`Program` stores Lean continuations and is not serializable content. The later
checked `Flow` graph is not a second free-monad carrier: it owns finite public
identity, sharing, cycles, admission, and generation, with an explicit
elaboration relation into semantic programs.

The algebra landed in three commits with separate roles:

- `bbefc6beaf69f6ac5d3bb8f2f5f62c80ddc956a7` froze the breaker contract;
- `424863e6487c160fcfbdb023ce0ba465f44a47b3` repaired two test elaboration
  sites without changing the contract; and
- `fb6f64571a42f12cc342582f72c917b016093a5b` implemented the algebra and
  made the contract and axiom report part of the default Lake build.

Independent review found that the file-span rows above were broader than the
public declarations actually extracted. The implementation satisfies the
frozen native proposal, but those source rows are not cutover-closed. Their
required dispositions are now explicit:

| Retained Foldlab declaration | Effect4 decision | Closure requirement |
| --- | --- | --- |
| `Representation.eq_of_forall_interpret` | port as generic interpreter-separation theorem | exact statement, proof, axiom receipt |
| `interpret_vis` | port as the named handler beta equation | exact minimal assumptions and receipt |
| `interpret_op_of_rightUnit` | expose the existing private sharp helper as public API | right-unit-only statement and receipt |
| `interpret_isMonadMorphism_of_equations` | port | left-unit/bind-associativity statement and receipt |
| `interpret_inhabits_the_pin` | port | anti-vacuity companion at the same equation boundary as the pin |
| `IsMorphE`, conversions, function-equality initiality | supersede with a first-class `ModelMorphism` API | conversions to the existing predicate plus initial-object uniqueness theorem |
| `syntactic_hyp_iff*` and wide `Prog.inl_unique`/`inr_unique` | port with native names distinguishing one-target strength from all-model corollaries | both directions and adapter aliases proved |
| `existsUnique_handler`, `interpret_satisfies_the_property` | downstream compatibility aliases | aliases resolve to the native freeness and anti-vacuity theorems without a second proof carrier |

No row is closed merely because the missing result is likely derivable. The
derivation theorem and its axiom receipt are the closure evidence.

The retained closure packet is now implemented:

- `4385457` freezes the exact retained declarations, including their binder
  order and universe levels, and is red only on those missing declarations;
- `47575b1` supplies interpreter separation, the named `vis` and sharp
  operation equations, one `ModelMorphism` wrapper around the existing law
  predicate, equality-form initiality, and strength-qualified injection
  theorems; and
- a clean default build checks 102 modules and 317 declarations. The new
  theorem receipts contain only `propext` and `Quot.sound`; several are
  axiom-free.

This closes the native retained algebra implementation, subject to its
independent assurance pass. The two Foldlab-only compatibility aliases remain
downstream work and do not enter Effect4's public vocabulary.

## Existing Foldlab effect-core material

| Source set | Observed state | Disposition |
| --- | --- | --- |
| `formal/effect-core-v1/EffectCore/**` | 57 empty modules; no semantic declarations | `evidenceOnly`; module breadth informs Effect4 stubs but no code is ported |
| `.staging/effect-core-v1/workshop/EffectCoreProbe.lean` | self-contained finite probe | `evidenceOnly`; eligible as a later first-order-flow regression fixture |
| S1 workshop | 39 Lean files: 13 scouts, 13 local implementations, 13 attacks; 13 incompatible carrier families; no production declaration | `evidenceOnly`; keep surviving closure and census obligations, reject every local carrier |
| S2 workshop | 24 Lean files: eight scouts, eight local implementations, eight attacks; seven raw carriers, six incompatible `AER`s, eight incompatible `ProgramWF`s | `evidenceOnly`; one ruled raw/checked flow replaces them all |
| Layer workshop | 16 Lean files plus three research documents; semantic Layer uses existing `Program`, `Handler`, sums, and state-outside-failure | `evidenceOnly`; reuse proved law shapes and counterexamples, not its `String -> Addr32` service environment or unstratified floor |
| `library/effects/archive/lean-model-0.3/**` | older conformance, replay, remote, and mutation estate | `evidenceOnly`; mine proof and test shapes, never revive its carriers wholesale |

The Layer result is adopted with two corrections. A semantic Layer is a
program whose result is a service handler, and Scope is a separate signature
summand. The rc.112 target has no public `Layer.scoped`; `Layer.effect`
already excludes `Scope` in its result. Effect4 therefore creates no
`Layer.scoped` row or duplicate scoped-layer carrier.

The completed late batch is retained as a byte-pinned evidence set, not
silently promoted. A fresh rerun against Foldlab's pinned toolchain elaborated
all 79 Lean files, exercised 2,246 axiom-print commands, and found zero errors
and zero `sorryAx`; one unused-`simp` warning is non-semantic. The final report
digests are S1
`d870f81454df29c32f3fb16926010c91df9e0aaf6f86cb8fe252ed08f230e3a2`,
S2 `2324ad78f58504263531eae170ffd57cb9b439532ea700e54803924fafe9f35d`,
and Layer
`7338063c1d1277a7dfa52129a4ab69af153affee158dd203bcc0722abcd9e3ec`.
Those results establish that the individual probes elaborate. They close zero
production rows because Foldlab's 57 formal Effect Core modules still contain
no semantic declarations.

The batch sharpens the next contracts:

- Flow admission owns payload-bearing diagnostics and a fixed `(clause, table
  index)` priority; foreign registry checks are environment-relative; all
  referenced content, including unreachable blocks, must be structurally
  closed; and static error rows are not claimed to overapproximate Foldlab's
  table-walker refusals.
- `Layer.provideMerge` carries the associative composition laws, while
  `Layer.provide` is explicitly non-associative. Overlapping service rows need
  a keyed merge, not `Handler.sum`.
- Foldlab's current residual row keeps the inner duplicate service while its
  handler meaning lets the outer clause win. This is a registered design
  counterexample to resolve before a Layer representation is frozen, not a
  behavior Effect4 copies.
- Content-plane graph sharing, runtime Layer memoization, first-order release
  identity, failed finalizers, interruption, and parallel scope remain
  separate obligations.

## Canonical row extraction

The S2 row above disposes of that workshop's *flow* carriers. It does not
dispose of its *row* material, which has a different Effect4 owner:
`Effect4/Data/Row.lean`. `docs/SCHEMA-CUTOVER.md` makes that module the sole
requirement carrier for the Schema getter lane (`DATA-ROW-01`, `DATA-ROW-02`,
`DATA-ROW-03`) and forbids Context from minting a second row carrier, so the
row lane needs its own dispositions before either family opens.

All rows below are late evidence with no Git blob identity. They are cited by
the SHA-256 recorded in `vendor/foldlab/LATE-MANIFEST.tsv`.

| Foldlab late evidence | SHA-256 | Disposition |
| --- | --- | --- |
| `s2/T016.lean` canonical-row kit | `a9c0ab063152c20bbf9652769abc610c73ce74a8707fe50c4985ae61d52a1394` | `evidenceOnly`; adopt the proof shapes named below, not the `RawProgram`/`AER` carrier |
| `s2/T017.lean` least-fixpoint row synthesis | `97e08c766717a09c9580c624dfb8a22a7bcdac3e219f45175f29e67f7fc2aa61` | `evidenceOnly`; reserved for a later requirement-synthesis packet, not for `DATA-ROW-01`-`03` |
| `s2/attack-EC1-T012.lean` row-spelling attacks | `414aef9a43de48359801d74282a8b2072db3416852b9325c631ccdefa3606b93` | `evidenceOnly`; supplies rejected-design witnesses |
| `s2/attack-EC1-T011.lean` normalization attack | `19ea91a8c0d6d9c35a39177d64a273c527c301b440c4874991f4d234c1433cf2` | `evidenceOnly`; supplies the normalization/denotation witness |

### Adopted proof shapes

These are shapes to re-prove natively over Effect4's own carrier. No Foldlab
declaration is imported, aliased, or copied.

- Canonicality is *strictly ascending*, spelled `List.Pairwise (· < ·)`
  (`T016:165 Ascending`). It entails `Nodup` rather than requiring a separate
  clause, and it already matches the convention `FlowWF` uses for `IdsWF` and
  `RootsWF`, so Effect4 gains no second canonical-order notion.
- Normalization is sorted insertion folded over the list (`T016:200
  ascending_ins`, `T016:230 ascending_canon`), hand-rolled so it reduces in
  the kernel. Effect4 has the same constraint Foldlab records at `T017:192`:
  Lean core and Std only, no Mathlib `List.dedup`.
- `T016:238 ascending_ext` is the load-bearing lemma: two ascending lists with
  the same members are equal. Union associativity, commutativity, and
  idempotence (`DATA-ROW-02`) reduce to membership rewriting through it, and
  membership plus requirement weakening (`DATA-ROW-03`) reads off the same
  extensionality. `T016:274 canon_of_ascending` is the matching idempotence.

### Rejected designs and their Foldlab witnesses

Each rejection below is condemned by an elaborated Foldlab probe, not by
assertion. The witnesses are evidence for an Effect4 counterexample row; they
are not themselves Effect4 gates.

- **Order-preserving dedup is not normalization.** `T012:498 dedupTags` drops
  repeats while preserving table order, and `attack-EC1-T012:679
  synth_row_not_ascending` shows its output fails `T016:290 RowsWF`. Effect4's
  row normalization must sort, not merely deduplicate.
- **A row is not determined by its members alone.** `attack-EC1-T012:610
  row_spelling_decides_admission` shows admission turning on spelling, and
  `attack-EC1-T012:806 row_does_not_pin_the_payload` shows membership failing
  to fix the payload. Single-valuedness has to come from canonical spelling
  against a canonical alphabet, which is exactly what `ascending_ext` buys.
- **Canonicality is an independent clause, not a derived one.** `T016:542
  declPerm` satisfies the agreement clause with a permuted declared row, and
  `T016:550 declShort` satisfies canonicality with a short one. Neither clause
  implies the other.
- **Normalization erases multiplicity.** `attack-EC1-T011:1031
  synthAER_hides_the_duplicate` exhibits normalization collapsing a duplicated
  contribution. This is the same hazard as the open `SC-WIRE-06`
  `normalization_preserves_denotation` edge in `docs/SCHEMA-CUTOVER.md`:
  idempotence of normalization licenses no semantic-preservation claim, and
  the two must not be reported as one result.

### Open

`Effect4/Data/Row.lean` is still an empty breadth stub, and no declaration may
enter it before a breaker freezes the `DATA-ROW` contract and its
counterexample rows. This section supplies that breaker's source material; it
closes no row and asserts no Effect4 theorem.

## Environment key declaration dispositions

The L0 key implementation is native Effect4 work; no Foldlab type is ported.
These rows make the existing public types explicit and prevent a later
Context, Layer, target, or Foldlab adapter from minting a second key or service
type-code carrier. Local signatures and axiom receipts are green, but every
row remains `required-open` until the generated declaration/owner/receipt join
exists. `ENV-KEY-INTERP` remains an open edge of the shared Context graph.

| Stable type row | Exact Lean declaration and owner | Canonical role | Native origin and source disposition | Duplicate-prevention relation | Assurance allocation |
| --- | --- | --- | --- | --- | --- |
| `E4-TYPE-ENV-SERVICE-NAME` | `Effect4.ServiceName`; `Effect4.Context.Key` | sole native nominal service identity; first-order `Nat` wrapper; no wire spelling | native contract `test/contracts/environment-context-key.contract.md`; `owned`; no Foldlab declaration ported | distinct from `ServiceTypeCode`; a later Effect string tag is a target/profile spelling, not another native identity | `leafReceiptId = ENV-LEAF-KEY-IDENTITY`; `receiptId = ENV-AX-KEY`; `evidenceId = ENV-EV-KEY-CONTRACT`; `required-open` |
| `E4-TYPE-ENV-SERVICE-TYPE-CODE` | `Effect4.ServiceTypeCode`; `Effect4.Context.Key` | sole native first-order code selecting a service carrier relative to a supplied universe | same native contract and disposition | distinct from `ServiceName`; neither a Lean `Type`, an inverse of one, nor a second operation/answer alphabet | same key-identity leaf; `required-open` |
| `E4-TYPE-ENV-SERVICE-KEY` | `Effect4.ServiceKey`; `Effect4.Context.Key` | sole native context-key identity, the ordered pair `(name, service)` with the frozen name-major order | same native contract and disposition | not type-indexed and not Effect's later string-only `Context.Tag` target view; no second Context or Requirement key carrier | same key-identity leaf; `parentGraphEdge = ENV-PG-CONTEXT/identity`; `required-open` |
| `E4-TYPE-ENV-SERVICE-UNIVERSE` | `Effect4.ServiceUniverse`; `Effect4.Context.Key` | supplied semantic boundary reading codes as Lean types; never canonical content, persisted data, or a source of code identity | same native contract; `foreignBoundary`; no Foldlab declaration ported | one shared Context interpretation boundary; no universe field on `ServiceKey`, no inverse `Type -> ServiceTypeCode`, and no per-service duplicate universe | `proofGraphId = ENV-PG-CONTEXT`; `nodeId = ENV-KEY-INTERP`; `receiptId = ENV-AX-KEY`; `required-open` |

## Schema extraction ruling

The complete ruling and proof graph are in `docs/SCHEMA-CUTOVER.md`. The
source audit rejects a directory copy:

| Foldlab source family | Effect4 disposition |
| --- | --- |
| `Cas.Schema.Ast` | `downstreamAdapter`; an admitted CAS subset/view over the native representation, not a base carrier |
| `Cas.Schema.El` | `evidenceOnly`; its `Empty` branches make it an incomplete denotation |
| pure `Cas.Schema.Codec` | downstream CAS codec; not Effect's directional, effectful four-index calculus |
| generic union/guardedness/discrimination algorithms | `split`; refactor over the native representation and retain their proof patterns |
| deriving handlers | metaprogramming technique only; `Lean.Expr` remains input and checked rows are output |
| CAS declaration rows, admission, refusals, bytes, projections, and store bridges | Foldlab-owned until per-type compatibility closure |

Effect4 will own one first-order representation with all 22 rc.112 persisted
tags, one document-relative relational denotation, one open first-order
reviver registry, one versioned rc.112 wire profile, and one four-index
`Codec decoded encoded decodeRequirements encodeRequirements`. `Getter` and
`Transformation` first reuse the existing `Program` as their proof-level
semantics. Their later serializable face uses the one common checked Flow and
an elaboration theorem back to that semantics; no Schema-specific effect
monad or program carrier is admitted. `Schema`, `Decoder`, `Encoder`, and
`Top` are existential views of that codec rather than new carriers.

That list is this repository's modelling choice and is narrower than the pin
in two ways worth recording before `SC-CODEC-08` freezes. rc.112 exports more
carrier and view types than the four named here, and it spells them as
widenings to `unknown` — `Encoder<E, RE> extends Schema<unknown>` — rather
than as existential quantification, so the existential reading is a choice and
should be labelled as one. And the underlying `Bottom` (`Schema.ts:283`)
carries **15** type parameters, of which the four-index `Codec` names four;
at least `TypeParameters`, `Type`/`EncodedOptionality`, and
`Type`/`EncodedMutability` have persisted consequences. Neither point
invalidates the four-index model, and both bound what "view" may be claimed to
mean.

### Where an authored schema can be refused

Two facts bound every coverage claim about the Effect authoring surface, both
read off the pin and one of them checkable in a line.

**The projection into the tag alphabet is total.**
`internal/schema/toRepresentation.ts` (361 lines, SHA-256
`677449c734ac6373598a81207ba0573f86fb8bd2c9fb25d1369aa1e710d614a2`) contains
**no throw site and no default case** — `grep -n 'throw\|errorWithPath\|Error('`
returns nothing. It maps the 21-member live `SchemaAST.AST` sum into the
22-tag alphabet without refusing. The consequence is worth stating because it
supports the census closure from the authoring side: no combinator in
`Schema.ts` can mint a 23rd persisted tag, because the only function that
produces tags cannot fail and has no case that emits an unnamed one. Every
refusal an author actually sees comes later, from `toJson`.

**Five first-party exports are nevertheless unpersistable.** The BigDecimal
comparison family — `isGreaterThanBigDecimal` (`Schema.ts:8793`),
`isGreaterThanOrEqualToBigDecimal` (`:8805`), `isLessThanBigDecimal`
(`:8816`), `isLessThanOrEqualToBigDecimal` (`:8828`), and
`isBetweenBigDecimal` (`:8844`) — omit the optional `annotate` argument
(`:7733`), so a schema carrying one throws at `toJson` with `Missing key at
["representation"]["checks"][0]["representation"]`. This is the same shape as
`E4-SCHEMA-CE-042`: an rc.112 value its own codec refuses.

No coverage wording in this repository may treat the authoring surface as
uniformly persistable. Some of it is not, in shipped first-party code, and
that is a property of rc.112 rather than of any Effect4 narrowing. Evidence
and counts are in `docs/SCHEMA-SURFACE-SURVEY.md`; the executed part is a
finite probe on one host and is not reproducible from this checkout alone.

### Schema tag declaration dispositions

These rows are the identity boundary for the six implemented public types.
They allocate one owner and one canonical role. Every row remains
`required-open` until its frozen signature, counterexamples, theorem receipt,
and evidence ID are joined by a generated assurance check; implementation and
local receipts alone close no cutover row.

| Stable type row | Exact Lean declaration and owner | Canonical role | Native origin and source disposition | Duplicate-prevention relation | Assurance allocation |
| --- | --- | --- | --- | --- | --- |
| `E4-TYPE-SCHEMA-REPRESENTATION-TAG` | `Effect4.RepresentationTag`; Lean module `Effect4.Schema.Representation`; file `Effect4/Schema/Representation.lean` | sole canonical carrier for the 22 persisted representation-node identities; it is neither the future payload `Representation` nor its denotation; content identity: none | native contract `test/contracts/schema-representation.contract.md`; `owned`; constrained by the pinned rc.112 source census, with no Foldlab carrier ported | intentionally separate from `Effect4.CheckTag`; equal payload shapes never merge nominal tags or justify a second parameterized keyword alphabet | `proofGraphId = SCHEMA-PG-REPRESENTATION-TAG`; `receiptId = SCHEMA-AX-REPRESENTATION-TAG`; `evidenceId = SCHEMA-EV-REPRESENTATION-TAG-CENSUS`; `required-open` |
| `E4-TYPE-SCHEMA-UNION-MODE` | `Effect4.UnionMode`; Lean module `Effect4.Schema.Representation`; file `Effect4/Schema/Representation.lean` | sole canonical finite selector for persisted `anyOf` versus `oneOf`; operational branch meaning remains in the later denotation; content identity: none | native contract `test/contracts/schema-subalphabets.contract.md`; `owned`; exact spellings are source evidence delegated to the parent graph | separate from representation tags and from union payloads; no duplicate mode carrier | `leafReceiptId = SCHEMA-LEAF-UNION-MODE`; `receiptId = SCHEMA-AX-UNION-MODE`; `evidenceId = SCHEMA-EV-UNION-MODE-CENSUS`; `parentGraphEdge = SCHEMA-PG-REPRESENTATION-TAG/representation`; `required-open` |
| `E4-TYPE-SCHEMA-CHECK-TAG` | `Effect4.CheckTag`; Lean module `Effect4.Schema.Representation`; file `Effect4/Schema/Representation.lean` | sole canonical finite tag carrier for persisted `Filter | FilterGroup`; it is not the future `Check` payload; content identity: none | native contract `test/contracts/schema-subalphabets.contract.md`; `owned`; exact spellings are source evidence delegated to the parent graph | intentionally separate from `Effect4.RepresentationTag`; no second `CheckTag` may be minted by `Schema.Check` | `leafReceiptId = SCHEMA-LEAF-CHECK-TAG`; `receiptId = SCHEMA-AX-CHECK-TAG`; `evidenceId = SCHEMA-EV-CHECK-TAG-CENSUS`; `parentGraphEdge = SCHEMA-PG-REPRESENTATION-TAG/representation`; `required-open` |
| `E4-TYPE-SCHEMA-LITERAL-KIND` | `Effect4.LiteralKind`; Lean module `Effect4.Schema.Representation`; file `Effect4/Schema/Representation.lean` | sole canonical finite classifier for literal payload kinds; it is not a literal value carrier; content identity: none | native contract `test/contracts/schema-subalphabets.contract.md`; `owned`; the ruling invents no independent wire spelling | distinct from the `RepresentationTag.literal` node and from `EnumValueKind`; absence of `null` is part of this alphabet | `leafReceiptId = SCHEMA-LEAF-LITERAL-KIND`; `receiptId = SCHEMA-AX-LITERAL-KIND`; `evidenceId = SCHEMA-EV-LITERAL-KIND-CENSUS`; `parentGraphEdge = SCHEMA-PG-REPRESENTATION-TAG/representation`; `required-open` |
| `E4-TYPE-SCHEMA-ENUM-VALUE-KIND` | `Effect4.EnumValueKind`; Lean module `Effect4.Schema.Representation`; file `Effect4/Schema/Representation.lean` | sole canonical finite classifier for enum-entry value kinds; it is not an enum value carrier; content identity: none | native contract `test/contracts/schema-subalphabets.contract.md`; `owned`; the ruling invents no independent wire spelling | narrower than `LiteralKind`; `SCHEMA-REL-ENUM-TO-LITERAL-KIND` records the injective kind map but does not decide either the separately frozen total raw value embedding or D7 field admission | `leafReceiptId = SCHEMA-LEAF-ENUM-VALUE-KIND`; `receiptId = SCHEMA-AX-ENUM-VALUE-KIND`; `evidenceId = SCHEMA-EV-ENUM-VALUE-KIND-CENSUS`; `parentGraphEdge = SCHEMA-PG-REPRESENTATION-TAG/representation`; `required-open` |
| `E4-TYPE-SCHEMA-PROPERTY-KEY-KIND` | `Effect4.PropertyKeyKind`; Lean module `Effect4.Schema.Representation`; file `Effect4/Schema/Representation.lean` | sole canonical finite classifier for portable property-key kinds; it is not a property-key value carrier; content identity: none | native contract `test/contracts/schema-subalphabets.contract.md`; `owned`; the ruling invents no independent wire spelling | separate from literal and enum kinds; absence of a local-symbol constructor prevents a duplicate portable identity for a host-local symbol | `leafReceiptId = SCHEMA-LEAF-PROPERTY-KEY-KIND`; `receiptId = SCHEMA-AX-PROPERTY-KEY-KIND`; `evidenceId = SCHEMA-EV-PROPERTY-KEY-KIND-CENSUS`; `parentGraphEdge = SCHEMA-PG-REPRESENTATION-TAG/representation`; `required-open` |

### Schema payload frozen ownership and assurance allocation

These rows allocate names before implementation under the Pass-B frozen
packet. `required-blocked` means the owner and route are decided, but
implementation admission remains blocked until the fixed production
payload-surface and ownership gate is green. Cutover and semantic closure stay
open. A leaf is promoted only if it later acquires an independent semantic,
admission, bridge, target, or cutover claim.

| Stable type row | Exact future declaration and owner | Canonical role and duplicate prevention | Assurance allocation |
| --- | --- | --- | --- |
| `E4-TYPE-SCHEMA-FLOAT64` | `Effect4.Float64`; `Effect4.Data.Json` | nominal 64-bit IEEE payload datum; not Lean `Float`, host equality, or a five-value classification | `leafReceiptId = SCHEMA-LEAF-FLOAT64-BITS`; parent `SCHEMA-PG-PAYLOAD`; `required-blocked` |
| `E4-TYPE-SCHEMA-JSON` | `Effect4.Json`; `Effect4.Data.Json` | recursive JSON payload with ordered object-entry lists so duplicate keys remain representable; not map-like `Lean.Json` | `nodeId = SCHEMA-NODE-JSON-FINITENESS`; parent `SCHEMA-PG-PAYLOAD`; `required-blocked` |
| `E4-TYPE-SCHEMA-REFERENCE-KEY` | `Effect4.ReferenceKey`; `Effect4.Schema.Payload` | raw reference spelling; non-emptiness is admission, not hidden construction | `leafReceiptId = SCHEMA-LEAF-PAYLOAD-SCALARS`; parent `SCHEMA-PG-PAYLOAD`; `required-blocked` |
| `E4-TYPE-SCHEMA-GLOBAL-SYMBOL-KEY` | `Effect4.GlobalSymbolKey`; `Effect4.Schema.Payload` | portable global-symbol identity only; local symbols have no constructor | same scalar leaf receipt; `required-blocked` |
| `E4-TYPE-SCHEMA-ANNOTATION-ENTRY` | `Effect4.AnnotationEntry`; `Effect4.Schema.Payload` | one retained JSON annotation entry; encode-side pruning remains a wire policy | same scalar leaf receipt; `required-blocked` |
| `E4-TYPE-SCHEMA-ANNOTATIONS` | `Effect4.Annotations`; `Effect4.Schema.Payload` | exact alias `Option (List AnnotationEntry)` preserving absent versus present-empty | same scalar leaf receipt; `required-blocked` |
| `E4-TYPE-SCHEMA-LITERAL-VALUE` | `Effect4.LiteralValue`; `Effect4.Schema.Payload` | four-constructor decoded literal value; no null or symbol constructor | same scalar leaf receipt plus constructor-cap receipt; `required-blocked` |
| `E4-TYPE-SCHEMA-ENUM-VALUE` | `Effect4.EnumValue`; `Effect4.Schema.Payload` | two-constructor enum value; `EnumValue.toLiteralValue : EnumValue -> LiteralValue` is the sole total injective raw embedding and preserves every binary64 payload, while literal finiteness is owned separately by `SCHEMA-PG-FIELD-ADMISSION` | same scalar leaf receipt plus `SCHEMA-REL-ENUM-TO-LITERAL-VALUE`; `required-blocked` |
| `E4-TYPE-SCHEMA-ENUM-ENTRY` | `Effect4.EnumEntry`; `Effect4.Schema.Payload` | enum name/value pair; duplicate names and aliases remain representable | same scalar leaf receipt; `required-blocked` |
| `E4-TYPE-SCHEMA-PROPERTY-KEY` | `Effect4.PropertyKey`; `Effect4.Schema.Payload` | string, number, or global-symbol portable key; no local-symbol constructor | same scalar leaf receipt plus constructor-cap receipt; `required-blocked` |
| `E4-TYPE-SCHEMA-REPRESENTATION-ANNOTATION` | `Effect4.RepresentationAnnotation`; `Effect4.Schema.Payload` | required `id`/`payload` record; intentionally has no `schemas` field | `leafReceiptId = SCHEMA-LEAF-PAYLOAD-RECORDS`; parent `SCHEMA-PG-PAYLOAD`; `required-blocked` |
| `E4-TYPE-SCHEMA-CHECK-REPRESENTATION-ANNOTATION` | `Effect4.CheckRepresentationAnnotationOf`; `Effect4.Schema.Payload` | parameterized check annotation with optional referenced schemas; not merged with `RepresentationAnnotation` | same record leaf receipt; `required-blocked` |
| `E4-TYPE-SCHEMA-ELEMENT` | `Effect4.ElementOf`; `Effect4.Schema.Payload` | parameterized array-element record; applied alias `Element` adds no carrier | same record leaf receipt; `required-blocked` |
| `E4-TYPE-SCHEMA-PROPERTY-SIGNATURE` | `Effect4.PropertySignatureOf`; `Effect4.Schema.Payload` | parameterized property record; applied alias adds no carrier | same record leaf receipt; `required-blocked` |
| `E4-TYPE-SCHEMA-INDEX-SIGNATURE` | `Effect4.IndexSignatureOf`; `Effect4.Schema.Payload` | exactly parameter and result type; applied alias adds no carrier or annotations field | same record leaf receipt; `required-blocked` |
| `E4-TYPE-SCHEMA-REPRESENTATION` | mutually recursive `Effect4.Representation` and `Effect4.Check`; `Effect4.Schema.Representation` | sole 22-constructor payload and two-constructor check family; reuses existing tag/kind alphabets and mints no second `Check` in `Schema.Check` | `proofGraphId = SCHEMA-PG-PAYLOAD`; `required-blocked` |
| `E4-TYPE-SCHEMA-REFERENCE-ENTRY` | `Effect4.ReferenceEntry`; `Effect4.Schema.Document` | ordered raw reference-table entry; duplicates remain representable for the wire boundary | `leafReceiptId = SCHEMA-LEAF-DOCUMENT-CONTAINERS`; parent `SCHEMA-PG-PAYLOAD`; `required-blocked` |
| `E4-TYPE-SCHEMA-DOCUMENT` | `Effect4.Document`; `Effect4.Schema.Document` | one-root container, nominally distinct from a multi-document | same document-container leaf; later semantics move to `SCHEMA-PG-DOCUMENT`; `required-blocked` |
| `E4-TYPE-SCHEMA-MULTI-DOCUMENT` | `Effect4.MultiDocument`; `Effect4.Schema.Document` | multi-root container; non-emptiness is field admission rather than hidden construction | same document-container leaf; later semantics move to `SCHEMA-PG-DOCUMENT`; `required-blocked` |
| `E4-JUDGMENT-SCHEMA-FIELD-ADMISSIBLE` | `Annotations.FieldAdmissible`, `Representation.FieldAdmissible`, `Check.FieldAdmissible`, `Document.FieldAdmissible`, `MultiDocument.FieldAdmissible`; `Effect4.Schema.Check` | one recursive persisted/decode-side structural judgment family with Boolean reflection; retained ordinary bags require finite JSON; failed judgment is not an issue or refusal value | `proofGraphId = SCHEMA-PG-FIELD-ADMISSION`; `required-blocked` |
| `E4-JUDGMENT-SCHEMA-PROPERTY-KEYS-UNIQUE` | future owner after `PropertyKey` equivalence freezes | profile narrowing; no declaration in this packet because structural binary64 equality would silently decide `+0`/`-0` and NaN key cases | future node, graph allocation deferred with key equivalence; `required-blocked` |
| `E4-JUDGMENT-SCHEMA-REFERENCE-KEYS-UNIQUE` | future predicates for both `Document` and `MultiDocument`; `Effect4.Protocol.Bytes` | raw-wire duplicate-key condition before either ordered table becomes a map; no declaration in this packet | node `SC-WIRE-REFERENCE-KEY-UNIQUE` in `SCHEMA-PG-WIRE`; `required-blocked` |

The frozen payload packet has exactly two graph-bearing families:
`SCHEMA-PG-PAYLOAD` for recursive `Json` and `Representation`/`Check`, and
`SCHEMA-PG-FIELD-ADMISSION` for the recursive persisted/decode-side judgment.
Float64, scalar sums, parameterized records, and passive document containers
attach as leaf receipts. `Effect4.Schema.Value` remains denotation-only.

The isolated pre-implementation reconstruction receipt used `lake env lean -DmaxErrors=10000 --json Effect4Test/Schema/PayloadContract.lean` against battery SHA-256
`e80d4be2f6385228aa87766d61ad4056fef68f947d0347cc15e1ac9279c6d27f`:
all 909 of 909 error records were `lean.unknownIdentifier._namedError`, with
no other diagnostic class, exit 1, and the sweep reached the last positive
obligation at source line 1173. The earlier 907/907 receipt through line 1080
is superseded. Lean's default 100-diagnostic cap is insufficient evidence for
this packet. Independent Pass-B re-review accepted the packet after the
declaration-free upward-import mutant was killed. The clean-red receipt freezes
the breaker; it does not admit implementation or close semantics.

`SCHEMA-PG-REPRESENTATION-TAG` is the one standalone proof graph in the earlier
tag packet because `RepresentationTag` is source-facing and carries the Schema tag
cutover boundary. It owns the source pin and extracted spelling-set edge, the
exact declaration signature and constructor order, nominal separation,
registered counterexamples, axiom receipt, and export coverage. The five
auxiliary enums are finite leaves: their constructors, census, local spelling
laws where applicable, counterexamples, and axiom receipts fit in their named
`leafReceipt` records. A leaf must be promoted to its own graph if it later
acquires independent admission, denotation, bridge, target, compatibility, or
host-boundary obligations.

The parent graph has no implicit fourth state. Its ten standard edges are
allocated before implementation as follows:

| `SCHEMA-PG-REPRESENTATION-TAG` edge | Initial state | Exact scope |
| --- | --- | --- |
| `identity` | `required-open` | unique owner, stable Lean name/module, native-contract origin, and pinned source disposition |
| `construction` | `required-open` | exact 22 constructors, dependent recursor order, census length, duplicate freedom, and coverage |
| `semantics` | `not-applicable` | this tag-only carrier owns no denotation, judgment, admission, or observation |
| `laws` | `not-applicable` | no composition or operational law is claimed; spelling laws are classified under `representation` |
| `representation` | `required-open` | exact tag spellings, partial inverse, nominal separation, lexical pin evidence, five attached leaf receipts, and `SCHEMA-REL-ENUM-TO-LITERAL-KIND` |
| `counterexamples` | `required-open` | durable `E4-SCHEMA-CE-017` through `E4-SCHEMA-CE-022` witnesses and reserved later-layer rows retained centrally |
| `bridges` | `not-applicable` | no alternate Lean, Foldlab, or host carrier is related by this packet |
| `targets` | `not-applicable` | this packet defines no TypeScript lowering, generated bytes, or host execution claim |
| `trust` | `required-open` | complete exported-theorem axiom receipt under the repository ceiling |
| `coverage` | `required-open` | exact public declaration/constructor export snapshot and pinned lexical source census |

Every `required-open` edge remains open until its evidence is mechanically
joined. A later semantic, bridge, or target claim must first change the
corresponding `not-applicable` row through a new breaker packet.

The native tag packets are `test/contracts/schema-representation.contract.md` and
`test/contracts/schema-subalphabets.contract.md`; their declaration-changing
attacks use `E4-SCHEMA-CE-017` through `E4-SCHEMA-CE-022`. The payload and
field-admission breaker is Pass-B frozen and every allocated row above is
`required-blocked` until the fixed production ownership gate turns green; the
table supplies ownership, not closure. No tag
declaration, theorem count, source gate, host probe, or reserved
counterexample in the working tree is a whole-slice closure claim.

The exact rc.112 bytes are present in the Foldlab checkout at SHA-256
`a0a7a1537cfe3a9159a80210e3de92342cc9e98651f0e8273a75ccdcccae69bc`.
`./scripts/check-schema-census.sh` compares two lexical source extractions
against the Lean tag-name extraction and, on those pinned bytes, reports exact
set agreement for 22 representation spellings and 2 check spellings. This is
source-spelling evidence only: it is not payload, decoder, denotational, or
whole-host faithfulness.

Profile ownership is settled before those stubs open. `Effect4.Protocol.Profile`
owns versioned profile identity, and `Effect4.Protocol.Admission` owns generic
profile membership and admission policy. `Effect4.Schema.Check` owns only
Schema-specific structural predicates as a consumer of those Protocol
facilities; predicate failure alone precommits no diagnostic or issue API. It
does not own `SC-PROFILE` identity or mint a second profile carrier. Ownership
of `SC-ISSUE-01` typed issue exit remains open.

### Authored usage profile

A read-only survey of authored Effect code on the build host counted 77,010
Schema member accesses across 3,318 files in 76 projects, excluding library
clones and vendored Effect sources. About half the estate is on Effect 4, and
`foldlab` pins `4.0.0-rc.112` — the exact revision this census is frozen
against.

This is dated machine evidence, not a sealed corpus: it is re-derivable but
carries no digest pin, and it is authority for **what people write**, never
for what rc.112 admits.

Eleven tags cover more than 99.4% of authored nodes: `String`, `Objects`,
`Number`, `Union`, `Arrays`, `Literal`, `Boolean`, `Unknown`, `Declaration`,
`Null`, and `Suspend`.

Four census tags were never used in any domain model. `Enum`, `Symbol`,
`UniqueSymbol`, and `ObjectKeyword` account for 24 occurrences in total, all
in test fixtures, two of which are *negative* refusal fixtures. `Reference` is
never authored at all — it is encoder-only output.

No symbol property key exists anywhere in the surveyed estate. All 503 index
signatures are `Schema.String`-keyed, plus two `TemplateLiteral`.

This survey is a *prioritisation* input for the future work named
`SC-PROFILE-01` through `SC-PROFILE-03`; it closes none of those edges. It
supports starting with a narrow profile, while the carrier still models all
22 tags: a profile is a checked subset of the full alphabet, never a smaller
alphabet.

Three findings bear on specific obligations:

- **Recursion is used**: 58 occurrences across 19 projects, including mutual
  recursion and recursion across a class boundary. `SC-DOC-*` is not
  hypothetical work.
- **`declare` is used**: 48 occurrences across 11 projects, in three distinct
  shapes — opaque pass-through, real `instanceof` guards, and content-address
  carriers. That is the `foreignBoundary` surface, and it is load-bearing.
- **Lossy transformations are real and estate-wide**, which is why no
  universal round-trip law may be assigned to all codecs. Witnesses include a
  decode that lowercases against an identity encode, a case-folding decode
  against a passthrough encode, an estate-wide `SchemaTransformation.trim()`,
  a canonicalising encode, and an `encodeURIComponent`/`decodeURIComponent`
  pair underpinning one service's whole route-param layer. These are the
  real-world form of `E4-SCHEMA-CE-005`.

### Guarded document prior art

The Foldlab tree carries substantial, directly reusable evidence for the
`SC-DOC-*` family, and almost none for `SC-REP-01`/`SC-REP-04`. All rows are
`evidenceOnly`; proof shapes are re-proved natively, carriers are not imported.

| Foldlab source | Effect4 obligation | What transfers |
| --- | --- | --- |
| `Cas/Schema/Guarded.lean:191-193` `Document.settles` | `SC-DOC-05` | bounded cost evidence only: an independent breaker measured 302,915 ms on one 25-entry acyclic fan table; an asymptotic exponential theorem remains open |
| `Cas/Schema/Guarded.lean:449-462` `settleAll` | `SC-DOC-04` | the memoised checker. Two decisive properties: the memo is fuel-free, and a name enters it only on the way back out, so a cycle never enters the memo |
| `Cas/Schema/Guarded.lean:708-722` `guardedMemo_eq_guarded` | `SC-DOC-04` | the memo changed the schedule and not the answer — this is `SC-DOC-04` verbatim |
| `Cas/Schema/Guarded.lean:734-748` `fanOutTable` | `E4-SCHEMA-CE-015` | the library-resident family used by the bounded fan-out cost witness; the observed 25-entry run is not an asymptotic proof |
| `Cas/Schema/Ingest.lean:881-891` `aliasCycle`, `bareStructCycle` | `E4-SCHEMA-CE-013` | bare self-reference, with cyclicity exhibited as explicit reachability derivations rather than asserted |
| `Cas/Schema/Ingest.lean:871-875` `guardedList` | `E4-SCHEMA-CE-014` | the guarded recursive control, which decodes in about a millisecond on the same path |

Two obligations were added to the Schema graph from this evidence and remain
owed before `SC-DOC` or `SC-DEN` can close:

- **Guardedness decides constructibility, not productivity.** `Ast.susp` is a
  delay, not a constructor: putting a recursive occurrence under one defers
  the loop rather than breaking it. Foldlab records three documents that are
  `Guarded`, admitted by both of its doors, and still have no value — Effect's
  own validator runs forever on `{"A": susp (reference "A")}`, overflows the
  stack on `{"A": susp (union [reference "A", null])}`, and knots at one
  remove on `{"A": susp (reference "B"), "B": reference "A"}`
  (`Cas/Schema/Guarded.lean:29-50`). Effect4 must not read `SC-DEN-07` or
  `SC-DEN-08` as termination claims. Deciding productivity needs a second
  relation over head positions — what a name reaches through `susp` wrappers
  alone, before any constructor builds anything — and `union` builds nothing
  either.
- **A generator must fix a canonical union member order.** Order is identity
  for unions, so without a canonical emission order a generated document's
  address depends on source arrangement
  (`library/cas/UNION-DESIGN.md:100-106`).

`Cas/Schema/El.lean:187-192` confirms and sharpens the ruling's rejection of
`El` as a denotation: six of its fourteen constructors map to `Empty` —
`.decl` (registry), `.union` when undiscriminated (order-dependent), `.enum`
(aliasing), `.tuple` (optionals shorten arrays), and `.reference` and `.susp`
(table-relative). Those are not gaps to fill in place; they are exactly the
cases the ruling says need a document-relative relational denotation.

Foldlab supplies no payload-carrier prior art for `Check`, annotations, or
`MultiDocument`. It has no `Filter`/`FilterGroup` type at all, emits
`("checks", .arr [])` literally, refuses inline representation annotations to
a sidecar CAS kind, and its `Document` is single-root. Effect4 must therefore
take two designs Foldlab explicitly refused — tuple `rest` as an array, and
inline annotations — and rebuild the injectivity and cost arguments that
Foldlab's refusals were resting on.

Decode and encode requirements remain distinct, and transformation encoding
composition runs in reverse order. No universal round-trip law is assigned to
all codecs because lossy transforms are part of the source surface. Schema
issue, wire issue, profile issue, Foldlab `IngestRefusal`, general Cause/Exit,
cutover refusal, and live frontier are separate classifications.

## Effect TypeScript family defaults

These defaults organize the exhaustive surface ledger. Every overload still
needs its own profile row and evidence.

| Family | Default disposition | Required semantic distinction |
| --- | --- | --- |
| Effect success/failure, service lookup, scope close, fiber lifecycle, and primitive state handles | `owned` core operations | Typed failure, defect, interruption, refusal, and live frontier remain distinct. |
| `map`, bind-derived combinators, `gen`, tagged catches, admitted resource brackets, and collection conveniences | `derivedExpansion` | The expansion and preservation theorem are explicit. |
| Schema and Codec | `separateCalculus` | Decoded, encoded, decoding-service, and encoding-service indices are independent. |
| Context and Service | `separateCalculus` feeding core requirements | Stable typed keys own identity; default References have an explicit ambient boundary. |
| Layer | `separateCalculus` | Output, error, input, memo identity, build order, and scoped lifetime remain observable. |
| Runtime and ManagedRuntime | `targetOnly` plus a Lean reference machine | ManagedRuntime lazily builds once, caches Context, owns Scope and fibers, and has disposed state. |
| Scope and Resource | `separateCalculus` with core operations | Registration, delimiter, exit-aware finalization, and state after failure are separate. |
| Fiber, scheduler, race, and interruption | `separateCalculus` | A decision tape fixes replay; safety theorems do not assume fairness. |
| Ref, Deferred, Queue, PubSub, and SubscriptionRef | primitive state operations plus `derivedExpansion` | Allocation, wakeups, shutdown, ownership, and subscriptions are observable. |
| Channel, Stream, Sink, Pull, and Take | `separateCalculus` | Pull suspension, end/error, leftovers, backpressure, cancellation, and cleanup are not list semantics. |
| Schedule | `separateCalculus` | State, input, output, error, environment, and time decisions remain explicit. |
| Config and ConfigProvider | recipe `separateCalculus`; provider `foreignBoundary` or finite-map model | Process environment is not a pure map unless supplied as one. |
| Cause and Exit | pure first-order data outside `Program` | rc.112 Cause is an ordered reason list; richer trees lower through a named lossy quotient. |
| callback, promise, arbitrary thunk, custom Schema predicate or transform | named block, registered `foreignBoundary`, or refusal | Host closures and promises never enter canonical syntax. |
| run functions, runtime handles, and concrete scheduler installation | `targetOnly` | Host execution supplies evidence, not denotational identity. |

Legacy names found in the corpus but absent from rc.112 are profile refusals
or versioned migrations, not new rc.112 declarations:
`Context.Tag`, `Context.GenericTag`, `Layer.scoped`, `Effect.async`,
`Schema.TaggedErrorClass`, `Schedule.intersect`, `Schedule.both`, and
`Schedule.compose`.

## Wild-type corpus baseline

The validation corpus is independent evidence, not a source of semantic
authority. A read-only mechanical sample selected 14 of 34 repositories and
counted 10,138 TypeScript-family files after excluding `.git`,
`node_modules`, `dist`, and `generated` trees.

| Representative repository | Pin | Files |
| --- | --- | ---: |
| Effect language service | `5e4d380b6fcd20f048dd8d41515bcd9ea47ffda4` | 802 |
| anomalyco/opencode | `df35e842f59bc115bb7c0479a8e11f017d443f2c` | 3,276 |
| brandhaug/b2b-saas-starter | `752d4a23551054731adec35b30a9751698f4dff4` | 338 |
| latitude-dev/latitude-llm | `a1a723e8b0e1241592745bd2f6090bf0d2ac3d0e` | 4,250 |
| typeonce-dev/effect-machine | `68092b83e4ab0d131598a5593565e10a2ff02f04` | 209 |
| tim-smart/dfx | `23988a4f182eb5cebc6c3bbac3f3c35fd303168f` | 49 |
| PaulJPhilp/EffectPatterns | `f3a0da2299717cf31d31313c5661cebd2446d5a3` | 613 |
| kitlangton/motel | `c49ab0f1bdb92fdbe27c144881f1d1e45efc864f` | 104 |
| remaining six sampled repositories | exact pins recorded by the corpus audit | 497 |

The first host harness must include direct rc.112 type and runtime tests in
addition to the installed diagnostic gate. The language-service clone is
behind rc.112, and the installed gate still has version-specific gaps.

## Dependency ruling

PolyFun passed its own build, test, validation, and axiom sweep at the exact
pin: 10,588 declarations across 270 modules, with no `sorry` or nonstandard
axiom taint. It is not an Effect4 dependency because its public adoption would
add Mathlib and cslib, a measured full validation checkout of about 8 GB, and
a rapidly changing API. Effect4 instead keeps its small algebra facade and
borrows the stronger API shapes: signature maps, first-class monad morphisms,
handler composition, finite paths, and an optional later ITree comparison.
PolyFun `FreeM` remains higher-order syntax and cannot replace checked
first-order `Flow`.

## Automated gates

| Gate | Command | Current scope |
| --- | --- | --- |
| Default Lean gate | `lake clean && lake build` | all `Effect4.*` and `Effect4Test.*` source files through Lake globs; root-reachability and axiom allowlist enforced |
| Exhaustive module/axiom gate | default build, invoked by `Effect4Test.lean` | the gate prints its own census rather than trusting this row; the current Schema-alphabet build observed 115 modules and 1756 declarations on 2026-08-31; semantic/test ceiling `propext`, `Quot.sound`; the audit implementation alone also permits `Classical.choice` |
| Narrow algebra gate | `lake env lean Effect4Test/Algebra/ExtractionContract.lean` | frozen public algebra signatures and the `E4-ALG-CE-*` counterexamples |
| Narrow retained-closure gate | `lake env lean Effect4Test/Algebra/RetainedClosureContract.lean` | exact retained Foldlab declaration signatures, binder order, universes, and their closure theorems |
| Narrow flow admission gate | `lake env lean Effect4Test/Flow/AdmissionContract.lean` | frozen Flow declarations plus `E4-FLOW-CE-001`-`005`, `007`, `013`, and `014` |
| Narrow flow privacy gate | `lake env lean Effect4Test/Flow/PrivacyContract.lean` | `E4-FLOW-CE-015`; both unchecked `CheckedFlow` construction paths must stay unresolvable from an importing module |
| Narrow schema census gate | `lake env lean Effect4Test/Schema/RepresentationContract.lean` | the 22-member rc.112 tag alphabet, its census listing and exact wire spellings, plus `E4-SCHEMA-CE-017`-`019` |
| Narrow schema sub-alphabet gate | `lake env lean Effect4Test/Schema/SubAlphabetContract.lean` | the union-mode, check-tag, literal-kind, enum-value, and property-key alphabets, plus `E4-SCHEMA-CE-020`-`022` |
| Schema census drift gate | `./scripts/check-schema-census.sh <SchemaRepresentation.ts>` | lexically extracts the closed type-union and codec-call spelling sets and compares them with Lean `tagName`; refuses off-pin bytes unless `--dry-run`; reports pin-matched spelling evidence but does not assign cutover closure or semantic faithfulness |
| Schema census gate reaction test | `./scripts/test-schema-census-gate.sh` | exercises fourteen specified lexical defects, including union-only and union-plus-codec additions, a tag copied across the representation/check family boundary, a 23rd member hidden behind a comment inside the closed union, a single-quoted codec tag literal, and a Lean spelling hidden behind a trailing comment; the last three were confirmed to pass the previous extractors on real pinned bytes and are now regression mutants; runs against a synthetic fixture, so it tests detector reaction and not the real census, payloads, or semantics |
| Schema field drift gate | `./scripts/check-schema-fields.sh <SchemaRepresentation.ts>` | extracts 22 structural field routes from the pinned source: 21 `Schema.Struct` shapes, including both helper-created shapes, plus the shared `KeywordFields` fragment; compares them with a frozen table and covers drift a tag census cannot see; refuses off-pin bytes unless `--dry-run`, and refuses `--expect` without it; single-route extraction only, because no Lean-side field carrier exists yet to cross-check against, so it assigns no cutover closure and no semantic faithfulness |
| Schema field gate reaction test | `./scripts/test-schema-fields-gate.sh` | exercises twelve specified source mutations, including the keyword helper, scalar envelope, and a quoted key, plus three invocation-safety refusals; runs against a synthetic fixture, so it tests detector reaction and not the real field set, payload types, or optionality |
| Schema payload declaration-surface and import-ownership gate | `./scripts/check-schema-payload-surface.sh`; `./scripts/test-schema-payload-surface-gate.sh` | the elaborated surface checker covers 24 carrier/alias surfaces and 67 constructor/field entries; its reaction test kills the four specified mutations and rejects two source-override routes. The production gate also materializes the contract's Payload-only import boundary, proves D0-D3 reachability and D4-D7 non-leakage there, and inspects declaration owners along `Check -> Document -> Representation -> Payload -> Data.Json`. The reaction receipt is green; the fixed production command is intentionally red until the builder creates `Effect4.Schema.Payload` and moves D2-D3 into it. This is a finite declaration/ownership receipt, not a proof graph or semantic claim |
| Schema alphabet mutation gate | `./scripts/test-schema-alphabet-mutations.sh` | five bounded local mutants exercise constructor order, duplicate-carrier rejection, coordinated spelling drift, and a coordinated spelling permutation with a matching census reorder; the permutation mutant was confirmed to SURVIVE the pre-repair packet and to be killed by the pointwise spelling obligations added after it, so the kill is attributable to the repair rather than to a pre-existing check; the local receipt feeds the parent graph and attached leaves but is neither itself a proof graph nor an exhaustive completeness claim |
| Flow admission mutation gate | `./scripts/test-flow-admission-mutations.sh` | four specified mutants (swapped scan order, weakened dangling jump, dropped `perform` answer equality, and substituted unrelated diagnostic witness) must each stay buildable and be killed by the matching frozen battery; Flow source and both batteries are verified byte-unchanged |
| Human-readable axiom receipts | `lake env lean Effect4Test/Algebra/AxiomReport.lean`; `lake env lean Effect4Test/Flow/AxiomReport.lean`; `lake env lean Effect4Test/Schema/AxiomReport.lean` | every currently exported algebra, flow, and Schema-alphabet theorem, with its axiom dependencies printed |
| Source trust gate | `./scripts/test-trust-gate.sh` | planted `unsafe` and `partial` declarations are rejected; the same vocabulary inside comments and strings is not. The detector is an elaboration-time check in the root aggregator, which Lake builds last, so any earlier module failure previously meant the detector never ran at all — verified by planting a `partial` during a red battery phase and observing the module build clean with no diagnostic emitted. The gate therefore EXCISES the modules declared in `test/fixtures/trust-gate/known-red.txt` from its throwaway probe copy and asserts against a genuinely green tree. That declared set is self-checking in both directions, each verified by perturbation: an undeclared failing target is rejected by name, and a declared module that is actually green is also rejected by name, so an entry cannot outlive its red phase. The gate reports which modules it excised and states that the trust property is unverified for exactly those |
| Foldlab evidence gate | `./scripts/check-vendor-foldlab.sh`; `./scripts/test-vendor-foldlab.sh` | closed inventory of 911 files and 11,940,983 bytes at pin `feb29321fd50204aa338209d313e84a3f8b71c66`; one omission, one extra file, and one byte mutation are each rejected |
| Internal citation gate | `./scripts/check-internal-citations.sh` | rejects every `<doc>:<line>` or `<doc>:<line>-<line>` citation naming `docs/SCHEMA-CUTOVER.md`, `PLAN.md`, `AGENTS.md`, `docs/ARCHITECTURE.md`, or `PORT-MANIFEST.md` anywhere under `Effect4/`, `Effect4Test/`, `docs/`, `test/`, or `scripts/`, because those documents are authored and edited continuously so a line number silently retargets; line citations into the pinned host sources, into `vendor/foldlab/`, and into `.lean` sources are examined and deliberately accepted; a lexical scan only, so it resolves no anchor, does not check that a cited section still says what the citing sentence claims, and assigns no cutover status |
| Internal citation gate reaction test | `./scripts/test-internal-citations-gate.sh` | seventeen specified cases — eleven refusals covering one violation per protected document including `docs/AGENT-ROUTING.md`, bare-basename, `./`-prefixed and `.lean`-hosted variants, total extraction failure, empty root, and a stray argument; and six acceptances covering pinned host sources, `vendor/foldlab/`, `.lean` sources, near-miss basenames, and the anchored spelling. Runs against a synthetic tree, never the live one, so it tests detector reaction and not whether any real citation resolves to the claim citing it |
| Diff hygiene | `git diff --check` | Authored source formatting |
| Effect target gate | pending P11 | rc.112 typecheck, installed tsgo, direct runtime vectors, negatives, and mutations |
| Foldlab compatibility gate | pending P12 | Both builds plus per-type round trips and interpretation agreement |

## Open closure edges

No full cutover claim is available while any row below is open.

1. The algebra assurance review must close the exact retained-span omissions
   listed above; current proofs and gates do not by themselves close Foldlab
   compatibility.
2. Exact type ascriptions must replace existence-only declaration checks, and
   the well-founded-but-not-globally-finite `Program` witness must remain in
   the breaker battery.
3. Signature-map and explicit universe-lift bridges need their own breaker
   packet; no implicit lift is admitted.
4. One raw/checked first-order Flow carrier must replace all S2 workshop
   variants and relate finite sequential bodies to `Program`.
5. Refusal, frontier, Cause, Exit, relational runs, nondeterminism, and
   divergence need separate observations and counterexamples.
6. The Schema representation and directional Codec calculus need a frozen
   public declaration graph before porting Foldlab proofs.
7. Context, Service, Layer, Scope, Resource, Runtime, ManagedRuntime, Fiber,
   scheduling, and interruption each need a representative contract before
   any one family is developed deeply.
8. The recursive rc.112 export and overload census must generate a closed
   surface ledger with no manual completeness override.
9. Generated TypeScript needs typed lowering, deterministic bytes,
   independent decoding/typechecking, simulation, and direct runtime tests.
10. Foldlab may cut over a type only after conversion round trips,
   interpretation agreement, source digest, counterexample coverage, and
   axiom receipt all close for that type.
