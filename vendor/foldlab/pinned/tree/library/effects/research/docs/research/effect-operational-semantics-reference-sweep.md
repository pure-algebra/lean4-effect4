# Effect operational semantics: reference sweep and first proof boundary

Status: initial research note  
Research snapshot: 2026-08-24

## Purpose

The project should define a deliberately restricted, executable operational model for selected public Effect v4 and Effect Schema operations, then prove properties of that model in Lean 4. The first milestone is not a claim that Effect's internals, scheduler, TypeScript compiler, JavaScript engine, or host runtime have been verified. It is a claim about a pinned public source surface and an explicitly related Lean model, with every stronger bridge guarded by separate evidence.

This boundary is necessary because Effect's public `Effect<A, E, R>` documentation describes a lazy workflow that can succeed with `A`, fail with `E`, and require services `R`, while TypeScript erases types before execution and the ECMAScript specification delegates scheduling and I/O facilities to a host environment. These are three distinct semantic layers, not one theorem target: the [Effect v4 `Effect` source contract](https://github.com/Effect-TS/effect/blob/main/packages/effect/src/Effect.ts), the [TypeScript erased-type/runtime boundary](https://www.typescriptlang.org/docs/handbook/typescript-from-scratch.html#erased-types), and [ECMA-262 hosts and implementations](https://tc39.es/ecma262/2024/multipage/overview.html#sec-hosts-and-implementations).

The intended long-term use is tooling for robust, higher-order verified data structures. Effect Schema is the strongest initial proving ground because the public v4 source exposes a runtime, discriminated `SchemaAST.AST` and separate parsing/encoding operations. That source is evidence that an algebraic AST exists; it is not, by itself, a proof that every AST is well formed, that its combinators obey algebraic laws, or that an exported JSON Schema matches a particular specification draft. Those are precisely the judgments and theorems this project should state. See [`SchemaAST.ts`](https://github.com/Effect-TS/effect/blob/main/packages/effect/src/SchemaAST.ts) and [`SchemaParser.ts`](https://github.com/Effect-TS/effect/blob/main/packages/effect/src/SchemaParser.ts).

## Claim ladder

Every result should carry one of these labels. A later label requires evidence for all earlier boundaries it crosses.

| Level | Permitted claim | Required evidence |
| --- | --- | --- |
| Model | A theorem holds of the Lean definitions. | Kernel-checked theorem, axiom report, pinned Lean toolchain. |
| Specification | The Lean definitions implement the project's cited formal contract. | Requirement-to-definition traceability, examples and counterexamples, review of quantifiers and observables. |
| Extraction | A pinned source fragment elaborates or normalizes to the Lean model. | Defined translation, accepted-source judgment, and preservation/reflection theorem for the translation. |
| Implementation conformance | A pinned Effect/TypeScript implementation agrees with the model on a stated domain. | Reproducible differential and conformance tests; this remains sampled evidence unless the bridge is proved. |
| Compilation preservation | Emitted JavaScript refines the source/model semantics. | A theorem or a separately validated translation for the pinned compiler, options, and accepted subset. |
| Hosted execution | A named JS engine and host preserve the modeled observations. | Host-specific semantics or a validated boundary plus runtime tests; ECMA-262 alone is insufficient. |

Lean's own reference makes the same specification/acceptance distinction: kernel acceptance establishes that a proof term follows from the definitions and axioms actually imported, while confidence still depends on the formal statement matching its intended informal meaning. It also documents axiom reporting and external re-checking as stronger audit gates. See [Validating a Lean Proof](https://lean-lang.org/doc/reference/latest/ValidatingProofs/).

## Proposed semantic vocabulary

The following are project definitions to adopt, not claims about Effect's implementation.

### Carriers and constructors

- `JsonText`: bytes plus a declared UTF-8 decoding policy.
- `JsonValue`: `null`, Boolean, decimal number, Unicode string, ordered array, or finite string-keyed object. Decide explicitly whether object construction rejects duplicate keys or resolves them; RFC 8259 says names *should* be unique and reports incompatible receiver behavior when they are not. See [RFC 8259 §§4 and 8](https://www.rfc-editor.org/rfc/rfc8259.html#section-4).
- `SchemaCore`: a frozen subset of the pinned Effect v4 Schema AST. Start with null, Boolean, finite number, string, literals, arrays/tuples, records with required fields, and finite unions. Defer declarations, suspension/recursion, checks with opaque callbacks, transformations, context requirements, annotations with operational meaning, and effectful parsers.
- `Outcome A E`: `success A` or `failure E` for the first pure slice. Defects, interruption, cancellation, finalizers, concurrency, and service lookup must be added as distinct constructors rather than silently folded into typed failure.
- `Event`: an intentionally small observable alphabet, initially empty for pure evaluation or limited to decoder/encoder entry, result, and typed failure. Host events are not modeled until their host contract is pinned.
- `Trace`: a finite sequence of `Event` plus a terminal `Outcome`, with divergence introduced only when the first recursive or asynchronous slice requires it.

Lean already supplies a useful implementation carrier: `Lean.Json` has constructors for null, Boolean, a decimal `JsonNumber`, string, array, and tree-map object, and its parser and printer are separate definitions. Reusing it avoids needless infrastructure, but conformance must still be proved or tested rather than inferred from its presence. See [`Lean.Data.Json.Basic`](https://github.com/leanprover/lean4/blob/master/src/Lean/Data/Json/Basic.lean), [`Parser`](https://github.com/leanprover/lean4/blob/master/src/Lean/Data/Json/Parser.lean), and [`Printer`](https://github.com/leanprover/lean4/blob/master/src/Lean/Data/Json/Printer.lean).

### Judgments and functions

- `SchemaWF s`: every child is well formed; unions satisfy the chosen non-emptiness/canonicality policy; object keys satisfy uniqueness; checks and transformations are in the accepted subset; recursive nodes, when later admitted, satisfy an explicit guardedness/productivity condition.
- `HasType v τ`: a semantic typing judgment over the model's carriers, separate from TypeScript assignability.
- `Subtype τ₁ τ₂`: a preorder on semantic value sets. Do not identify it with TypeScript structural assignability, JSON Schema subsumption, or program refinement.
- `Step : Config → Event → Config → Prop`: a labeled small-step relation for operations whose intermediate behavior matters.
- `Evaluates : Config → Trace → Outcome A E → Prop`: the reflexive/transitive observable closure of `Step`.
- `decode : SchemaCore → JsonValue → Outcome DomainValue DecodeIssue` and `encode : SchemaCore → DomainValue → Outcome JsonValue EncodeIssue` for the executable pure fragment.
- `normalize : SchemaCore → SchemaCore` and, if source ingestion is added, `elaborate : SourceSnapshot → Outcome SchemaCore ElabIssue`.
- `Traces p`: all observable traces allowed by program/model `p`.

PLF is a suitable methodological template for defining inductive reduction, multi-step closure, normal forms, progress, and preservation, while its program-equivalence chapter shows how behavioral equivalence must account for divergence rather than only equal final values. These are Rocq teaching developments, not normative definitions for Effect. See [Small-step Operational Semantics](https://softwarefoundations.cis.upenn.edu/plf-current/Smallstep.html), [Type Systems](https://softwarefoundations.cis.upenn.edu/plf-current/Types.html), and [Program Equivalence](https://softwarefoundations.cis.upenn.edu/plf-current/Equiv.html).

### Relations and laws

Use one declared orientation throughout:

```text
p refines q  :=  Traces(p) ⊆ Traces(q)
p ≈ q        :=  p refines q ∧ q refines p
```

Under this convention, an implementation refines a specification when it exhibits no observation forbidden by the specification. Equality of results is appropriate only after determinism and termination are established. Trace inclusion is the safer default for nondeterminism, host choice, partial specifications, and later concurrency.

The first candidate theorem families are:

1. **Well-formedness preservation:** evaluating, decoding, encoding, or normalizing a well-formed term does not manufacture an ill-formed model value.
2. **Progress for the pure subset:** a well-formed closed configuration is terminal or can step; expected decoder rejection is a typed terminal result, not “stuck.”
3. **Determinism:** pure decoding, encoding, and normalization have at most one result under a fixed issue-ordering policy.
4. **Normalization:** `normalize` preserves denotation and is idempotent. If it also produces a canonical form, prove uniqueness separately.
5. **Codec laws:** `decode (encode x) = success x` only for values admitted by the schema and encoding preconditions. The reverse direction should generally be `encode (decode j) = canonicalize j`, not textual identity, because JSON Schema's data model deliberately excludes whitespace and numeric lexical form. See [JSON Schema Core §4.2.1](https://json-schema.org/draft/2020-12/json-schema-core#section-4.2.1).
6. **Equational laws:** identity, composition, associativity, distributivity, or absorption laws for admitted constructors and operations. State every side condition; do not import familiar monad or lattice laws as facts about the implementation.
7. **Coherence:** two supported elaboration or normalization paths with the same source meaning produce equivalent denotations, even when their AST shapes differ.
8. **Semantic preservation:** accepted source elaboration and later code generation preserve or refine traces. PLF's constant-folding and partial-evaluation developments illustrate local transformation correctness; CompCert illustrates a pass-by-pass simulation whose composition yields a compiler theorem. See [PLF Program Equivalence](https://softwarefoundations.cis.upenn.edu/plf-current/Equiv.html), [PLF Partial Evaluation](https://softwarefoundations.cis.upenn.edu/plf-current/PE.html), and the [CompCert correctness overview](https://compcert.org/man/manual001.html).
9. **Trace properties:** safety properties quantify over every trace; liveness claims require an explicit infinite-trace or fairness model and are deferred from the first slice.

CompCert is especially useful for claim discipline: its manual names the exact AST-to-AST verified phase, records preprocessing, assembling, and linking outside that phase, and states compiler correctness as preservation/improvement of observable behavior. This is a better model than calling a whole toolchain “verified” when only one pass or model is proved. See [CompCert compiler structure and trust boundaries](https://compcert.org/man/manual001.html#sec8) and its top-level [`backward_simulation` theorem](https://compcert.org/doc/html/compcert.driver.Compiler.html).

## Normative sources

These sources own the external behavior. Pin an edition, draft, commit, and host/runtime version in the project's source ledger before freezing theorem statements.

### JSON text

- [RFC 8259: The JavaScript Object Notation Data Interchange Format](https://www.rfc-editor.org/rfc/rfc8259.html) is an IETF Standards Track definition and interoperability guide. It requires parsers to accept conforming texts, permits parsers to accept extensions, and requires generators to emit strictly conforming grammar. It also identifies duplicate names, number range/precision, Unicode, and unpaired-surrogate behavior as interoperability hazards.
- [ECMA-404: The JSON Data Interchange Syntax](https://www.ecma-international.org/publications-and-standards/standards/ecma-404/) is the corresponding Ecma syntax standard. RFC 8259 says their JSON-text grammars are intended to agree while RFC 8259 adds interoperability recommendations.
- [ECMA-262 `JSON.parse` and `JSON.stringify`](https://tc39.es/ecma262/2024/multipage/structured-data.html#sec-json-object) specify the ECMAScript algorithms over JS values. They are a distinct layer from JSON grammar: revivers, replacers, object property operations, exceptions, and ECMAScript numeric/string values can affect observations.

The most important modeling hazards are concrete. JSON objects are unordered at the RFC/JSON Schema data-model level, but a JS API can expose property traversal order; JSON numbers are unbounded decimal syntax/data-model values while JS `number` is binary64; non-finite JS numbers are not JSON numbers; duplicate object names and unpaired surrogates are not portable. The relevant requirements are in [RFC 8259 §§4, 6, 8–10](https://www.rfc-editor.org/rfc/rfc8259.html#section-4), the [JSON Schema data model](https://json-schema.org/draft/2020-12/json-schema-core#section-4.2.1), and the [ECMAScript JSON algorithms](https://tc39.es/ecma262/2024/multipage/structured-data.html#sec-json-object).

### JSON Schema

- [JSON Schema Draft 2020-12 Core](https://json-schema.org/draft/2020-12/json-schema-core) defines schema resources, dialects, vocabularies, references, annotations, applicators, and output structure.
- [JSON Schema Draft 2020-12 Validation](https://json-schema.org/draft/2020-12/json-schema-validation) defines the validation vocabulary. In particular, `format` is annotation by default; full assertion support belongs to the optional Format-Assertion vocabulary.
- [JSON Schema Test Suite](https://github.com/json-schema-org/JSON-Schema-Test-Suite) is the project-maintained language-agnostic corpus for specified behavior. The repository says coverage is broad but welcomes missing cases; passing it is conformance evidence, not a completeness proof.

A schema-draft claim must therefore identify its dialect and vocabularies, supported keyword set, reference-resolution policy, output mode, annotation collection, `format` mode, numeric model, and treatment of unknown keywords. “JSON Schema compliant” without those qualifiers is too broad. The core specification allows unknown keywords as annotations and makes some keyword behavior depend on collected annotations, including `unevaluatedProperties` and `unevaluatedItems`; see [Core §§4.3.1 and 11](https://json-schema.org/draft/2020-12/json-schema-core#section-11).

Two non-normative research papers are useful when the project reaches subsumption and full modern-schema semantics: [Validation of Modern JSON Schema: Formalization and Complexity](https://arxiv.org/abs/2307.10034) gives a formal account of modern validation, and [Type Safety with JSON Subschema](https://arxiv.org/abs/1911.12651) studies subschema checking as a static typing relation. They should inform definitions but never override the draft documents.

### JavaScript and the host

- [ECMA-262, edition 2024](https://tc39.es/ecma262/2024/) is a stable language edition suitable for a first pin; the living editor draft should be used only if its commit is recorded.
- [ECMA-262 Hosts and Implementations](https://tc39.es/ecma262/2024/multipage/overview.html#sec-hosts-and-implementations) explicitly delegates host-defined facilities, including input and output, to an external host environment.
- [ECMA-262 Jobs](https://tc39.es/ecma262/2024/multipage/executable-code-and-execution-contexts.html#sec-jobs-and-host-operations-to-enqueue-jobs) specifies constraints on jobs but uses host hooks to enqueue them. It is not a complete Node, Bun, Deno, or browser event-loop specification.
- [Test262](https://github.com/tc39/test262) is TC39's implementation-conformance corpus for ECMA-262, ECMA-402, and ECMA-404. TC39 describes its coverage as extensive but incomplete, so use a pinned subset as differential evidence, not as a theorem.

The initial model should consequently be host-free. A later scheduling theorem must name the host, runtime version, timer/clock model, Promise-job policy, and observable event alphabet. Effect interruption, concurrency, scopes, finalization, clocks, randomness, network calls, and process environment remain gated until those definitions exist.

### TypeScript and Effect's compiler tooling

TypeScript's own documentation says its compiler roughly erases types to produce JavaScript and that its type system does not alter runtime behavior; its design goals explicitly list a fully erasable structural type system and list a sound or provably correct type system as a non-goal. See [TypeScript for the New Programmer](https://www.typescriptlang.org/docs/handbook/typescript-from-scratch.html#erased-types) and [TypeScript Design Goals](https://github.com/microsoft/TypeScript/wiki/TypeScript-Design-Goals).

Do not use the historical TypeScript 1.8 language specification as current authority. The maintained public materials are the compiler implementation, compiler tests, handbook/reference pages, and release notes; even the official repository discussion identifies the published language specification as outdated. See [microsoft/TypeScript issue #61485](https://github.com/microsoft/TypeScript/issues/61485). Pin the compiler package, commit, `tsconfig`, module resolution mode, target, JSX/decorator settings, and all transforms that can change emitted JS.

The Effect-specific [`@effect/tsgo`](https://github.com/Effect-TS/tsgo) repository describes itself as a wrapper/superset of a pinned TypeScript-Go version that adds Effect diagnostics, quick fixes, and refactors. Its diagnostics are valuable acceptance gates, but neither an accepted TypeScript program nor a clean Effect diagnostic run proves the public operational model or the emitted runtime behavior.

### Effect v4 subject sources

The repository pins the Effect commit and exported package version in
[`sources.lock.json`](../../.reference/provenance/sources.lock.json). The `main`
links below remain discovery links; project traceability must resolve the
corresponding paths through that lock before freezing a theorem statement.

- [`Effect.ts`](https://github.com/Effect-TS/effect/blob/main/packages/effect/src/Effect.ts): public workflow type and operations.
- [`Exit.ts`](https://github.com/Effect-TS/effect/blob/main/packages/effect/src/Exit.ts) and [`Cause.ts`](https://github.com/Effect-TS/effect/blob/main/packages/effect/src/Cause.ts): public result and failure/cause vocabulary to classify before adding defects or interruption.
- [`Schema.ts`](https://github.com/Effect-TS/effect/blob/main/packages/effect/src/Schema.ts): public Schema constructors and types.
- [`SchemaAST.ts`](https://github.com/Effect-TS/effect/blob/main/packages/effect/src/SchemaAST.ts): runtime AST carrier, node variants, checks, encoding links, and context.
- [`SchemaParser.ts`](https://github.com/Effect-TS/effect/blob/main/packages/effect/src/SchemaParser.ts): public construction, checking, decoding, and encoding runners.
- [`package.json`](https://github.com/Effect-TS/effect/blob/main/packages/effect/package.json) and [`src/index.ts`](https://github.com/Effect-TS/effect/blob/main/packages/effect/src/index.ts): the exported surface, which is the claim boundary rather than internal files.

## Mechanization and prior art

### Lean 4 foundations and metaprogramming

Lean's official pipeline parses characters into `Syntax`, expands macros, elaborates user syntax into core expressions, has the kernel check those expressions, and separately compiles executable code. A source transformer must specify which representation it consumes and which stage is trusted. See the [official elaboration and compilation pipeline](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/) and [Lean definitions reference](https://lean-lang.org/doc/reference/latest/Definitions/).

The community [Metaprogramming in Lean 4 overview](https://leanprover-community.github.io/lean4-metaprogramming-book/main/02_overview.html#elaboration-and-delaboration) is the practical guide for `Syntax`, `Expr`, elaboration, delaboration, and formatter output. Use it for implementation technique, but use the official language reference and pinned Lean source when behavior differs. Delaborated/pretty-printed output should be a separate observable with an explicit normalization relation, not assumed to be a textual inverse of elaboration.

[Lean4Lean](https://github.com/digama0/lean4lean) is relevant prior art for an executable checker related to an abstract theory by proofs. Its README also warns that its implementation is derived from the C++ kernel and may share bugs, a useful reminder that a second implementation is not automatically independent evidence.

### Translation and independent executable models

[Aeneas](https://github.com/AeneasVerif/aeneas) demonstrates a disciplined translation pipeline: Charon extracts Rust crate information and simplified MIR into LLBC, Aeneas translates supported programs into functional proof-assistant models, and the Lean backend supports extrinsic proofs. The project links formal work on the translation and borrow-checking, but its current README limits the tool to a subset of safe Rust and excludes unsafe code and concurrency. External definitions may require handwritten models. See the [Aeneas ICFP 2022 paper link and formalization references](https://github.com/AeneasVerif/aeneas#formalization), [current limitations](https://github.com/AeneasVerif/aeneas#targeted-subset-and-current-limitations), and [Charon's extraction boundary](https://github.com/AeneasVerif/charon#why-charon).

The lesson for this project is architectural, not a transfer of Aeneas's Rust guarantees: define an accepted subset, preserve the original source, generate a separate Lean model, isolate handwritten external models, and prove the translation relation before claiming “verify code as-is.” The Lean website's [Aeneas use case](https://lean-lang.org/use-cases/aeneas/) is a useful overview, but the repository, limitations, and paper should govern technical claims.

[Cedar's Lean specification](https://github.com/cedar-policy/cedar-spec/tree/main/cedar-lean) is a particularly close pattern for a definitional engine, validator, symbolic compiler, and proofs of typechecking, slicing, compilation, equivalence, and implication. Cedar's project also uses differential testing between the Lean model and a separately implemented Rust system; this cleanly separates proof about the model from evidence about the production implementation. See the [Cedar Lean verified-property index](https://github.com/cedar-policy/cedar-spec/blob/main/cedar-lean/README.md#verified-properties) and AWS's [verification-guided development report](https://assets.amazon.science/d3/86/99db1aa142ffb6981d86dc849e4c/how-we-built-cedar-a-verification-guided-approach.pdf).

[Strata](https://github.com/strata-org/Strata) is Lean 4 prior art for extensible language syntax/semantics dialects, symbolic evaluation, verification-condition generation, and external SMT discharge. It is under active development, so borrow architectural vocabulary and inspect proof/trust boundaries rather than taking API stability for granted.

### JavaScript mechanizations

- [JSCert](https://jscert.org/) mechanized ECMAScript 5 semantics in Coq and paired the inductive semantics with an executable reference interpreter. It shows the value of keeping a proof-oriented relation and executable evaluator connected, but its language edition is far behind current Effect targets. See the [JSCert code and publication index](https://jscert.org/publications.html).
- [KJS](https://github.com/kframework/javascript-semantics) supplied an executable K semantics and tested it against a historical Test262 corpus. Its own README lists partial and unsupported built-ins, including JSON, so it is precedent for feature accounting and semantic coverage rather than a current full-JS oracle.
- [ESMeta](https://github.com/es-meta/esmeta) extracts a mechanized model from a pinned ECMA-262 source and provides parsing, execution, CFG construction, specification type analysis, and Test262 execution. It is strong differential/oracle prior art, but it is not a Lean proof that a JS engine or TypeScript compiler preserves semantics.
- [Thales](https://github.com/jessealama/thales) is experimental Lean 4 prior art that accepts a strict, immutable subset of TypeScript and emits Lean sidecars with explicit `Option`/`Except` structure. Its narrow subset and documented axioms are more relevant than a headline “TypeScript-to-Lean” claim; it does not establish semantics for Effect's async, mutation, class, or full numeric/runtime surface.

No mature, end-to-end Lean 4 mechanization located in this sweep establishes semantic preservation for current full TypeScript, current ECMAScript, the Effect runtime, and a named host. The available pieces are useful but non-substitutable: historical JS mechanizations, executable spec extraction, narrow TypeScript-to-Lean experiments, and general Lean language-framework projects. This gap is the reason to begin with a frozen pure subset and an explicit conformance bridge rather than a whole-language claim.

### JSON and JSON Schema in Lean 4

[predictable-machines/lean4-json-schema](https://github.com/predictable-machines/lean4-json-schema) is the most directly relevant Lean 4 prior art found. It provides an inductive schema type, total validation function, deriving handlers, and named soundness/completeness goals. Its own warning says the library does not yet fully cover the standard, its API may change, and its proofs may not cover all functionality. Treat it as code and theorem-pattern reference, not evidence that this project or Effect Schema conforms to Draft 2020-12.

Lean's standard `Lean.Json` implementation is useful infrastructure but does not advertise an RFC 8259 correctness theorem in the cited source files. The first project slice should either prove the required parser/printer properties for the used subset or keep text parsing outside the theorem and operate on already-constructed `JsonValue`s.

## Tutorials and contextual reports

These are useful for onboarding or design judgment, but they are not normative specifications and should not support conformance claims.

- [Software Foundations, Programming Language Foundations](https://softwarefoundations.cis.upenn.edu/plf-current/toc.html): machine-checked teaching patterns for operational semantics, equivalence, Hoare logic, type systems, subtyping, normalization, and partial evaluation.
- [How to Prove It with Lean](https://djvelleman.github.io/HTPIwL/): introductory proof-writing material.
- [HashCloak's Introduction to Formal Verification with Lean](https://hashcloak.com/blog/tutorial-introduction-to-formal-verification-with-lean-(part-1)): applied tutorial material and examples, not a language or protocol standard.
- [Unison in production](https://www.unison-lang.org/blog/experience-report-unison-in-production/): first-party experience showing that typed values, code identity, serialization, versioned definitions, runtime behavior, ecosystem support, and human project/release ergonomics all matter in production. It is contextual evidence for designing practical verified-data tooling, not evidence about Effect, JavaScript, or semantic preservation.

The Unison report is especially useful as a caution against equating an elegant semantic core with a complete usable system: it records runtime bugs, missing libraries, tooling friction, and later ergonomic improvements while also describing typed distributed values and hash-addressed definitions. Those observations motivate explicit integration and usability gates but prove no theorem about this project.

## Recommended first proof slice

### Slice: pure Schema-to-JSON value semantics

Freeze a small Effect Schema source snapshot and formalize only its pure, synchronous, host-free value behavior:

1. **Source ledger:** pin Effect commit/package, Lean toolchain, ECMA-262 edition, RFC 8259, JSON Schema Draft 2020-12 documents, TypeScript/@effect/tsgo versions, `tsconfig`, and test-suite commits.
2. **Accepted AST:** null, Boolean, finite decimal-compatible number, string, literal, array/tuple, required-field object, and finite union. Record every excluded `SchemaAST` constructor and feature.
3. **Well-formedness:** define unique keys, accepted checks, no suspended recursion, no opaque declaration, no effectful transform/context, and an explicit issue-order policy.
4. **Value semantics:** define deterministic decode/encode relations over `JsonValue`, not JSON text or `JSON.parse`/`JSON.stringify`.
5. **Internal theorems:** well-formedness preservation, progress, determinism, normalization preservation/idempotence, and conditional codec round trips.
6. **JSON Schema subset:** if a schema emitter is included, define the supported Draft 2020-12 vocabulary relation and prove validator soundness/completeness only for that subset. Defer `$dynamicRef`, unevaluated applicators, annotation-sensitive composition, regex portability, and `format` assertion.
7. **Conformance harness:** run pinned JSON Schema Test Suite cases that fall inside the subset and differential fixtures against the pinned Effect package. Treat results as observed agreement, with unsupported and disputed cases reported separately.
8. **Claim gate:** publish “proved for the Lean model; observed against pinned Effect fixtures” until the source-to-model extraction or implementation correspondence is itself proved.

This slice directly supports higher-order verified data structures without prematurely modeling fibers, schedulers, services, clocks, async host hooks, resource scopes, defects, or interruption. It also forces the project to solve the highest-leverage representational problems first: carriers, well-formedness, typed failures, normalization, equivalence, and external-spec conformance.

### Minimum theorem inventory

```text
schemaWF_children
decode_progress
decode_deterministic
encode_deterministic
decode_type_sound
normalize_wf
normalize_denotation
normalize_idempotent
decode_encode_roundtrip
encode_decode_canonical
jsonSchema_validate_sound_supported
jsonSchema_validate_complete_supported
```

Names are provisional. Each final theorem should carry the supported-feature predicate or other side conditions in its statement instead of relying on prose.

### Exit criteria before expanding scope

- No `sorry` or unreviewed custom axioms in release theorems; record `#print axioms` output and use the official [proof-validation guidance](https://lean-lang.org/doc/reference/latest/ValidatingProofs/).
- Every modeled constructor has positive, negative, boundary, and near-miss examples.
- Every external requirement maps to a definition or theorem and cites a section/commit.
- The executable evaluator and relational semantics agree on the supported subset.
- Official JSON/JSON Schema fixtures used by the subset are pinned and reproducible; failures and excluded cases are machine-readable.
- Differential Effect fixtures record package version, host runtime, compiler, options, input, raw result, normalized observation, and model result.
- The public claim names all exclusions and never generalizes from the pure Schema subset to Effect scheduling, runtime internals, performance, full TypeScript, or a complete JSON Schema draft.

## Open gaps and risks

1. **The external-source ledger is incomplete.** Effect is pinned by
   [`sources.lock.json`](../../.reference/provenance/sources.lock.json), but
   conformance-suite commits, TypeScript/`@effect/tsgo`, runtime versions, and
   project-specific standards decisions still require pins before their gates.
2. **No maintained normative TypeScript semantics.** The compiler and tests are operational authority, and the type system is intentionally erasable and not sound. Full TypeScript typing or transpilation correctness is a separate research program.
3. **Host semantics are incomplete without a host.** ECMA-262 delegates scheduling and I/O facilities; Node, Bun, Deno, and browsers are not interchangeable theorem targets.
4. **Schema AST existence is not algebraic correctness.** Effect exposes a discriminated runtime AST, but well-formedness, denotation, laws, and JSON Schema correspondence remain project obligations.
5. **JSON value equality is underspecified unless chosen.** Object order, duplicate keys, number equality/precision, Unicode, and issue ordering can invalidate naive round-trip and equivalence statements.
6. **JSON Schema is vocabulary- and annotation-sensitive.** `$ref`/`$dynamicRef`, recursive resources, unevaluated applicators, regex dialects, output formats, and optional `format` assertion are high-risk expansion points.
7. **Tests are not proofs.** Test262 and the JSON Schema Test Suite both describe incomplete or extensible coverage. Differential agreement can find translation errors but cannot quantify over untested inputs.
8. **Translation can verify the wrong model.** Aeneas and Cedar show the value of explicit generated/handwritten boundaries and differential testing. This project still needs a proved or independently validated source-to-model link.
9. **Lean execution and proof checking are different boundaries.** The kernel checks elaborated proof terms; compiled executables, native evaluation, FFI, solvers, and external generators require their own trust declarations.
10. **Prior art is partial and heterogeneous.** JSCert/KJS target older JavaScript, ESMeta is an executable spec framework rather than a Lean proof, and current Lean TypeScript efforts accept narrow subsets or carry axioms. Reuse concepts and fixtures, not umbrella claims.

## Source priority for the first milestone

1. Pinned Effect v4 public source: `SchemaAST`, `Schema`, `SchemaParser`, exports, and package manifest.
2. RFC 8259 and ECMA-404 for JSON text/value boundaries.
3. JSON Schema Draft 2020-12 Core and Validation for the exact supported vocabulary.
4. Stable ECMA-262 edition for JS value behavior and explicit host deferrals.
5. Lean Language Reference for definitions, elaboration, compilation, and proof validation.
6. PLF and CompCert for semantic-relation and preservation proof patterns.
7. JSON Schema Test Suite and Test262 for pinned external conformance fixtures.
8. Cedar, Aeneas, Lean4Lean, ESMeta, JSCert/KJS, Strata, and lean4-json-schema as prior-art implementations whose stated boundaries must remain attached.
9. Velleman, HashCloak, the community metaprogramming book, and Unison's first-party report for education and context only.
