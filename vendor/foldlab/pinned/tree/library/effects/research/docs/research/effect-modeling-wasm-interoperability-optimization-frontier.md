# Effect modeling, WebAssembly interoperability, and equivalence-guided optimization

Status: frontier research note
Research snapshot: 2026-08-24
Source policy: primary specifications, project documentation and repositories, and original research papers only

## Purpose

This note maps the active frontier around effect syntax and semantics, portable algebraic data, WebAssembly execution boundaries, concurrency languages, and equivalence-guided optimization. Its purpose is not to select a finished architecture. It identifies which parts of the desired Foldlab architecture already exist, which claims those artifacts actually support, and where a new formal contribution remains possible.

The central result is:

> The field has mature foundations for algebraic effects, increasingly strong models for higher-order and concurrent effects, deployable cross-language value interfaces in the WebAssembly Component Model, and practical equivalence and optimization engines. It does not yet have one open standard that combines a versioned effect grammar, a durable encoding, a handler ABI, operational semantics, observational equivalence, and independently checkable optimization evidence.

That gap is real and well aligned with Foldlab's canonical-descriptor philosophy. The right response is not to invent a universal surface language immediately. It is to define a small canonical effect core and make every other artifact—a source syntax, Effect TypeScript program, WIT world, trace, runtime machine, optimizer input, or proof certificate—a named projection or interpretation of that core.

## Claim discipline for this survey

This note uses the project's claim ladder from
[`CLAIM-GATES.md`](../effect-typescript-semantics/CLAIM-GATES.md). The following
evidence classes must remain distinct.

| Evidence class | What it establishes | What it does not establish |
| --- | --- | --- |
| Formal calculus in a paper | A grammar and mathematical semantics have stated metatheoretic results, subject to the paper's proof boundary. | That a production compiler or runtime implements the calculus. |
| Mechanized theorem library | A proof assistant accepts the named theorems under its recorded assumptions. | Conformance of an external runtime unless a correspondence theorem is present. |
| Specification or proposal | A standards body or project has defined a candidate interoperability contract. | Wide deployment, stability, or implementation correctness. |
| Shipped tool or runtime | A usable implementation exists and can supply conformance or performance evidence. | A theorem about all executions. |
| Differential or replay evidence | Named implementations agree on recorded cases or a history can be replayed. | Universal equivalence outside the sampled or replayed domain. |

For Foldlab, a theorem about a Lean effect model is G2. Agreement with a pinned Effect source slice requires G3 evidence. A verified translation is G4 only for its accepted domain and observation. A named JS or Wasm engine remains a G5 boundary.

### Frontier maturity at this snapshot

| Area | Formal status | Implementation status | Correct reading |
| --- | --- | --- | --- |
| First-order algebraic effects and handlers | Mature calculi and mechanizations | Multiple research and production implementations | Solid semantic foundation, no universal runtime ABI |
| Scoped/higher-order/parallel handlers | Active formal development, several recent calculi | Research-language implementations | Important open design space |
| Handler refinement and program logics | New mechanized and automated research systems | Research artifacts | Capable of proving selected implementations, not whole mainstream runtimes |
| OCaml 5 handlers | Published runtime design | Shipped, public API still unstable; no static effect safety | Production runtime evidence with an explicit language boundary |
| Koka/Effekt/Lexa | Formal translations and cost studies | Active research languages/compilers | Best laboratory for handler compilation, not stable interoperability standards |
| WIT/Component Model 0.2–0.3.1 | Detailed algorithms/tests; complete formal spec still pending | Developer-preview support used by Wasmtime and binding tools | Usable cross-language contract inside a still-phase-1 umbrella proposal |
| Candid | Precise IDL, binary format, coercion, and structural-subtyping rules; some metatheoretic goals remain open | Deployed Internet Computer wire format and bindings | Actual self-describing typed serialization and evolution, not effect semantics |
| RichWasm | Coq-mechanized progress, preservation, and type safety | Research compilers and interoperability examples | Typed shared-memory IL experiment, not a Component Model standard or verified compiler chain |
| DimSum | Coq-mechanized event semantics and module refinement | Research framework and case studies | Decentralized multi-language reasoning; sequential/safety scope in the published model |
| WASI 0.3 async | Normative interface release | Ratified and shipped in current tooling | Real async component interface, not a proof of every host implementation |
| Stack switching/WasmFX | Formal calculus, mechanized work, program logic | Phase-3 proposal and prototypes | Strong future continuation substrate, not standardized core Wasm yet |
| wRPC | Draft wire specification | Used by wasmCloud | Networked WIT evidence with unresolved portable resource semantics |
| Bisimulation/equality-saturation optimizers | Mature theory and specialized tools | mCRL2, FDR, egg, Alive2, Ruler, others | Powerful for constrained models; no general arbitrary-effect optimizer |

## Is effect modeling an active research area?

Yes. The frontier has moved beyond the basic observation that first-order algebraic operations form a free syntax interpreted by handlers. Recent work concentrates on five harder problems.

### 1. Higher-order and scoped effects

First-order algebraic operations receive values and resume with values. Important programming constructs instead contain or delimit computations: exception handling, resource bracketing, masking, local state, transactions, nondeterministic scopes, parallel loops, and stream regions. These do not fit a naive first-order signature without an elaboration.

The 2024 [framework for higher-order effects and handlers](https://doi.org/10.1016/j.scico.2024.103086) defines generic higher-order signatures, a free syntax, fold-style interpreters, and a categorical account covering scoped, parallel, latent, writer, and bracketing effects. The 2024 [calculus for scoped effects and handlers](https://doi.org/10.46298/lmcs-20(4:17)2024) supplies a formal grammar, operational semantics, row-polymorphic type-and-effect system, type inference, and type safety. [Hefty Algebras](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/hefty-algebras-modular-elaboration-of-higherorder-effects/A33FE759BB81EA94A180798C92E16283) studies modular elaboration of higher-order syntax into algebraic effects and develops equational reasoning infrastructure in Agda.

This is directly relevant to Effect. A formal model of `succeed`, `fail`, and `flatMap` can begin first order, but scopes, acquisition/release, interruption masking, races, and streams require a higher-order or explicitly machine-based account. Treating all of them as ordinary requests would hide the part of the computation over which the operation has authority.

The typing frontier is also looking for a common account beneath row- and capability-oriented surface systems. [Modal Effect Types](https://doi.org/10.1145/3720476) separates effect tracking from every function arrow by treating effects modally, while [Rows and Capabilities as Modal Effects](https://arxiv.org/abs/2507.10301) gives type- and semantics-preserving translations from row-based and capability-based systems into a modal framework. These are formal convergence results, not a settled interchange standard, but they strengthen the case for a canonical core that can admit several source presentations.

### 2. Parallel and concurrent handlers

[Parallel Algebraic Effect Handlers](https://arxiv.org/abs/2110.07493) studies handlers over parallelizable computations, gives calculi connecting parallel semantics to a typed implementation language, and supplies a Haskell realization. This is not yet a general theory of distributed scheduling, but it demonstrates that parallel structure must be represented separately from sequential bind if the compiler is to retain useful independence information.

At the runtime level, OCaml 5 has shipped efficient one-shot delimited continuations and effect-handler primitives. The official manual nevertheless labels the interface unstable and explicitly says OCaml does not statically ensure that every performed effect is handled; see the [OCaml 5.4 `Effect` API](https://ocaml.org/manual/5.4/api/Effect.html) and [effect-handler manual](https://ocaml.org/manual/5.4/effects.html). The implementation paper, [Retrofitting Effect Handlers onto OCaml](https://arxiv.org/abs/2104.00250), reports a segmented-stack design and performance evidence. This is strong runtime prior art, not an effect-safety theorem for OCaml programs.

### 3. Relational verification of handler implementations

The verification question is changing from “is this effect program type safe?” to “does this handler-based implementation refine a simpler specification?”

[Specification and Verification for Unrestricted Algebraic Effects and Handling](https://doi.org/10.1145/3674656) develops a specification logic for imperative higher-order programs with continuation-enabled handlers and an automated prototype. The 2026 [Relational Separation Logic for Effect Handlers](https://doi.org/10.1145/3776676) targets program refinement and equivalence for handlers, heap state, stored continuations, and primitive concurrency, with a Rocq/Iris artifact. This line is especially close to the desired Effect-runtime question: relate a direct specification to a continuation-bearing implementation without pretending the continuation representation is the specification.

### 4. Effect-handler compilation

There is no single accepted implementation strategy. Active systems explore CPS, capability passing, evidence passing, segmented stacks, stack switching, handler fusion, and JIT specialization.

- Koka is a live research language with row-polymorphic effect types, algebraic data types, and effect handlers; its repository explicitly remains research-grade rather than production-ready. Its [compiler and bibliography](https://github.com/koka-lang/koka) document generalized evidence passing and reference-counting work.
- [Generalized Evidence Passing for Effect Handlers](https://doi.org/10.1145/3473576) gives a sequence of semantic refinements from handlers through delimited control and evidence passing to a form compilable to C, and evaluates implementations in Koka and Haskell.
- Effekt is an active research language with lexical handlers and effect polymorphism. Its [compiler documentation](https://github.com/effekt-lang/effekt-website/blob/main/docs/implementation.md) exposes Source, Core, capability-passing, optimization, and multiple backend stages, while warning that parts remain work in progress.
- [Zero-Overhead Lexical Effect Handlers](https://doi.org/10.1145/3763177) gives a type-directed translation and implementation intended to remove handler overhead from effect-free mainline paths while preserving lexical handler identity.
- [Tracing Just-in-Time Compilation for Effects and Handlers](https://se.cs.uni-tuebingen.de/publications/gaissert2025tracing.pdf) explores specializing control effects in a tracing JIT and reports performance experiments across handler strategies.

These projects confirm that an effect calculus and its runtime representation should not be identified. CPS, evidence passing, and stack switching are alternative implementations whose relationship to a shared observation can be proved or validated.

### 5. Model checking and abstract interpretation for effectful higher-order programs

Recent work studies decidable fragments of higher-order programs with algebraic effects, handler restrictions, answer-type modification, and temporal safety. The important lesson for Foldlab is negative but useful: unrestricted higher-order effects quickly make automated equivalence and model checking undecidable. Automation therefore needs an accepted finite or symbolic fragment, bounded exploration, or a proof-producing abstraction. A universal optimizer cannot simply “run bisimulation” on arbitrary TypeScript closures.

## A canonical effect artifact needs more than a grammar

A stable syntax is only one layer. A useful portable artifact should make at least the following objects explicit:

```text
surface source
  -> parsed syntax with provenance
  -> elaborated, well-kinded descriptor
  -> normalized canonical core
  -> semantic process / interaction tree
  -> target program or runtime machine
  -> observable trace and evidence
```

The stable interchange form should be the canonical core, not source text and not a pretty-printed Lean term. The corresponding theorem inventory is:

```text
parse (print p) = normalize p
decode (encode p) = success p
denote (normalize p) ≈ denote p
denote (decode (encode p)) ≈ denote p
runTarget (compile p) refines denote p
```

The first two are syntax and codec laws. The latter three are semantic laws. None implies the others automatically.

A durable effect artifact also needs:

- a versioned operation signature;
- typed request and response indices;
- explicit success, typed failure, defect, interruption, and divergence distinctions as they enter scope;
- named code references or defunctionalized frames instead of opaque closures;
- a handler-resolution policy;
- a scheduler, ordering, cancellation, fairness, and backpressure policy when concurrency is admitted;
- an observation declaration saying which internal actions are hidden;
- a durable codec with canonicalization rules;
- source and dependency identities, ideally content-addressed after normalization; and
- an evidence ledger stating which parser, elaborator, optimizer, translation, and runtime boundaries were proved, checked, tested, or assumed.

## Existing pieces of a portable effect language

No existing project supplies the entire stack, but several solve important adjacent problems.

### Interaction Trees and PolyFun: semantic syntax

[Interaction Trees](https://www.cis.upenn.edu/~stevez/papers/XZHH%2B20.pdf) represent recursive, effectful, and potentially nonterminating computations using returns, silent steps, and visible indexed events. Handlers interpret event signatures, and equivalence up to weak bisimulation hides finite internal activity. The [Interaction Trees library](https://github.com/DeepSpec/InteractionTrees) is mechanized in Rocq.

[PolyFun](https://github.com/Verified-zkEVM/PolyFun) is the closest current Lean-native substrate. It provides polynomial functors, free monads, interaction trees, strong and weak bisimulation, simulation, handlers, event signatures, and sequential, two-party, multiparty, and concurrent interaction frameworks. Its repository builds without `sorry` or `admit` according to its stated status, but that fact licenses only its generic theorems—not a correspondence to Effect.

Interaction trees are a semantic interchange candidate. They are not a standard byte encoding, a package/version scheme, or a handler ABI.

### SpecTec: one source for a language standard

The WebAssembly community has adopted [SpecTec](https://webassembly.org/news/2025-03-27-spectec/), a DSL from which specification prose, executable interpreter material, test artifacts, and proof-assistant definitions can be generated. The project reports partial transfer of Wasm soundness proofs and explicitly aims to remove “eyeball correspondence” between handwritten prose and formal definitions. The original [Wasm SpecTec paper](https://arxiv.org/abs/2311.07223) describes this executable-specification architecture.

SpecTec is strong prior art for Foldlab's grammar discipline: one normalized semantic source can generate several consumers. It is not evidence that the WebAssembly Component Model or an Effect calculus already has a complete mechanization.

### DimSum: decentralized multi-language semantics

[DimSum](https://doi.org/10.1145/3571220) is a Coq framework in which independently defined language modules are labeled transition systems that communicate through events. Language-agnostic combinators link modules, while wrappers translate between languages and express protocols with an environment. Its case studies relate a high-level language, assembly, and specifications; abstract assembly libraries to source-level specifications; and verify a multipass compiler compatible with those libraries. This is unusually direct prior art for Foldlab's view of a canonical entity being projected into a local context: interoperation need not require one global syntax or one fixed memory model, provided the event boundary and refinement relation are explicit.

The published model is fully mechanized using Interaction Trees and Iris, but it is a research framework, not a deployed cross-language ABI. Its evaluated scope is sequential and safety-oriented; concurrency and liveness are left as future work. DimSum therefore supports an architectural pattern—independent semantics joined by events and proved wrappers—not a claim that Effect TypeScript and a Wasm runtime are already related.

### Unison: content-addressed code and mobile computations

Unison stores code as ASTs and identifies definitions by hashes of their implementations. Its [repository overview](https://github.com/unisonweb/unison) describes content-addressed code, semantic version control, and cached compilation; its [“big idea” documentation](https://www.unison-lang.org/docs/the-big-idea/) describes moving a computation and synchronizing missing hashed dependencies. Unison also has an effect system (“abilities”) and operational support for distributed computations.

This is shipped language/runtime prior art for code identity and mobility. It is not an open, language-neutral effect wire standard, nor does the cited material prove semantic preservation across arbitrary Unison runtime versions. Its main Foldlab lesson is that content-addressing should apply to normalized closed code plus its dependency closure, not to surface spelling.

### IPLD Schemas: typed, content-addressed data with explicit representations

[IPLD Schemas](https://ipld.io/docs/schemas/) separate a logical type from its representation strategy over a common data model and codec layer. They support products, sums, maps, lists, links, and representation choices suited to content-addressed immutable graphs. The [schema introduction](https://ipld.io/docs/schemas/intro/) explicitly distinguishes a user-facing DSL from a more stable reified schema form.

This separation is a close analogue for Foldlab:

```text
EffectCore type/meaning
    != serialized representation
    != target runtime object
```

IPLD describes data and links, not control, resumptions, cancellation, or handlers. It is nevertheless relevant for content-addressed descriptors, traces, proof objects, and dependency graphs.

### Durable-execution runtimes: reified histories rather than effect ASTs

Temporal persists workflow event histories and requires deterministic replay: given the same input and history, workflow code must reproduce the same command sequence. The official [event-history documentation](https://github.com/temporalio/documentation/blob/main/docs/encyclopedia/event-history/go.mdx) explains replay mismatch and nondeterminism; Temporal's [history-service architecture](https://github.com/temporalio/temporal/blob/main/docs/architecture/history-service.md) states that the event sequence is sufficient to recover workflow state.

[Restate](https://docs.restate.dev/references/architecture) similarly documents a log-first runtime for durable actions, state, timers, RPC, and promises. [Golem](https://github.com/golemcloud/golem) runs WebAssembly components as durable distributed workers; its [durability](https://learn.golem.cloud/v1.5/develop/additional) and [persistence](https://learn.golem.cloud/v1.5/operate/persistence) documentation describes journaling typed host interactions and replaying or simulating them during recovery.

These systems demonstrate that effect boundaries can be journaled and replayed across failures. Their histories are execution evidence, not necessarily complete program syntax, and the cited projects do not provide Lean or Rocq proofs that every SDK/runtime implementation refines one common operational semantics. Foldlab should therefore distinguish:

- **program descriptor** — what may be executed;
- **command/event log** — what was requested or observed;
- **checkpoint** — enough machine state to resume; and
- **replay witness** — evidence that a new execution agrees with a history.

## WebAssembly as an interoperability target

WebAssembly currently provides two different opportunities: a typed component boundary and a future low-level continuation substrate. They should not be conflated.

### Core WebAssembly has unusually strong formal foundations

Core WebAssembly has a mathematical specification and executable reference artifacts. [WasmCert-Coq](https://github.com/WasmCert/WasmCert-Coq) mechanizes Wasm 2.0 plus named extensions, with type safety, interpreter soundness, type-checker soundness/completeness, and conformance testing; its README also identifies an experimental unverified binary-parser boundary. SpecTec is being adopted to generate more of the normative and formal artifacts from one source.

This makes core Wasm a plausible later theorem target. It does not make every engine, JIT, host import, WASI service, or component-model feature verified.

### WIT and the Component Model provide cross-language algebraic values

The [WebAssembly Component Model](https://github.com/WebAssembly/component-model) defines separately compiled components and language-neutral imports/exports. Its current developer-preview milestones distinguish:

- **0.2**: typed values, resources, shared-nothing/shared-everything linking, WIT, and the initial Component Model boundary;
- **0.3**: native concurrency additions including async functions, `future`, `stream`, and new canonical ABI operations.
- **0.3.1**: `map<K,V>` plus `implements` and `external-id` annotations.

These are developer-preview compatibility islands supported by producer and consumer tools, not a completed W3C 1.0 formal specification. At this snapshot, the umbrella Component Model remains a [phase-1 WebAssembly proposal](https://github.com/WebAssembly/proposals), while [WASI 0.3 has separately been ratified](https://github.com/WebAssembly/WASI/releases/tag/v0.3.0) and makes async native to WebAssembly components. Wasmtime 46 reports Component Model async enabled by default in its [versioned release notes](https://github.com/bytecodealliance/wasmtime/blob/v46.0.0/RELEASES.md). This is shipped runtime evidence for the developer-preview contract, not a completed formal semantics. The Component Model repository still lists a full formal specification and reference interpreter as future work. The exact milestone text is pinned here to the surveyed [Component Model snapshot](https://github.com/WebAssembly/component-model/blob/1af0b35e1bfc03bd4ad9603be2f676316ff9f420/README.md).

The [pinned WIT specification](https://github.com/WebAssembly/component-model/blob/1af0b35e1bfc03bd4ad9603be2f676316ff9f420/design/mvp/WIT.md) defines packages, semantic versions, interfaces, worlds, imports and exports, records, variants, enums, flags, tuples, lists, maps, options, results, resources, ownership/borrowing handles, and gated features. It explicitly presents WIT packages as the basis for sharing types and definitions among components. Current WIT/component value types are non-recursive; recursive structures need resource handles, explicit indices, or another encoding.

The [pinned Canonical ABI](https://github.com/WebAssembly/component-model/blob/1af0b35e1bfc03bd4ad9603be2f676316ff9f420/design/mvp/CanonicalABI.md) lowers and lifts those abstract values across core Wasm functions and linear memories. This is a call ABI with configurable memory/string details—not a general archival serialization format. An application that persists a component value still needs a durable codec and version policy above the Canonical ABI.

[Candid](https://github.com/dfinity/candid/blob/7cc578c060df6aabdb6654abe9c0f09a8df6584c/spec/Candid.md) provides the missing contrast. Its deployed Internet Computer IDL defines a binary representation that carries an actual type with each value, making the value self-describing, and it applies structural subtyping and coercion during deserialization to support interface evolution. Candid is therefore prior art for a real typed wire codec, not merely an in-process calling convention. Its specification is also candid about the boundary: it does not specify behavioral constraints, transitive coherence of repeated coercion/reserialization does not hold in general, and subtyping completeness has not been formalized. It serializes typed values and references, not an effect program's handler, scheduler, resumption, or observation semantics.

[RichWasm](https://doi.org/10.1145/3656444) explores a different point in the design space: a richly typed intermediate language for safe, fine-grained shared-memory interoperability between source languages with different memory-management disciplines. Its [research artifact](https://github.com/RichWasm/RichWasm-artifact/tree/62c4bbcd67f4613304b3ae5bc6a85a901c2e9c8d) includes a Coq-mechanized type-safety development, ML and L3 compilers, a RichWasm type checker, a RichWasm-to-Wasm compiler, and interoperability examples spanning garbage-collected and manually managed memory. Unlike the Canonical ABI's portable shared-nothing path, RichWasm makes ownership, capabilities, and shared layout part of the typed IL. The mechanized result is RichWasm type safety; the compiler implementations are research artifacts, not a proved end-to-end translation or a standardized Component Model mode.

There is also an official open [Wasm GC Canonical ABI pre-proposal](https://github.com/WebAssembly/component-model/issues/525) that would let components select compatible core GC representations, potentially avoiding copies when passing records, variants, lists, and resources. As of this snapshot it is an issue-level pre-proposal with implementations under development, not merged normative Component Model behavior. It narrows the performance gap between canonical value passing and shared heap representations; it still does not create a durable or self-describing wire format.

Working tooling already exists:

- [`wit-bindgen`](https://github.com/bytecodealliance/wit-bindgen) generates guest bindings for Rust, C, C++, C#, and Go and points to JS and Python componentization tools;
- [`wasm-tools`](https://github.com/bytecodealliance/wasm-tools) parses, validates, prints, packages, mutates, and fuzzes components and WIT, while explicitly enabling some not-yet-stage-4 proposals for experimentation;
- [`jco`](https://github.com/bytecodealliance/jco) provides JavaScript component tooling and Preview 2/3 shims.

This is the most deployable current answer to “cross-platform algebraic type and data-structure sharing in Wasm.” It deliberately stops short of higher-kinded types, arbitrary language closures, or a universal effect algebra. A WIT `resource` is an opaque owned/borrowed capability handle, not a serialized heap object. A WIT `future<T>` or `stream<T>` specifies an interoperability protocol, not the complete scheduling semantics of a source language.

The [wRPC draft specification](https://github.com/bytecodealliance/wrpc/blob/1b182e762e9e11a32df671ab52303eede2bd3c27/SPEC.md) is the clearest current attempt to carry WIT-shaped calls and values over a network. It defines wire treatment for streams and futures but leaves resources as application-defined opaque byte blobs, so portable remote resource identity and lifetime remain unsolved. [wasmCloud's RPC documentation](https://wasmcloud.com/docs/v1/hosts/lattice-protocols/rpc/) supplies shipped distributed-runtime evidence for WIT-defined operations over wRPC/NATS. Neither source turns wRPC into a proved portable effect semantics.

### Component concurrency is an ABI, not yet a universal concurrency semantics

The Component Model's [concurrency explainer](https://github.com/WebAssembly/component-model/blob/main/design/mvp/Concurrency.md) specifies a language-agnostic async calling convention, tasks, waitables, futures, streams, cancellation, backpressure, and nondeterministic scheduling concerns. Its stated goal is to let diverse language runtimes bind to a common low-level boundary without forcing all source languages into one concurrency model.

This is precisely useful for Foldlab, but it changes the theorem target. A translation into WIT async need not preserve internal scheduling. It should preserve an explicit observation such as visible requests, stream elements, cancellation outcomes, or allowed trace sets.

### Stack switching and WasmFX target effect implementation

[WasmFX](https://wasmfx.dev/) and the paper [Continuing WebAssembly with Effect Handlers](https://arxiv.org/abs/2308.08347) propose typed continuations and instructions for creating, suspending, and resuming computations. The paper gives a formal specification and type-soundness argument and reports both a reference-interpreter implementation and a Wasmtime prototype. The subsequent official [WebAssembly stack-switching proposal](https://github.com/WebAssembly/stack-switching/blob/main/proposals/stack-switching/Explainer.md) targets coroutines, async/await, generators, lightweight threads, and effect handlers using one-shot typed continuations. It is currently listed in [phase 3, the implementation phase](https://github.com/WebAssembly/proposals), but it is not yet a generally standardized and shipped core-Wasm feature.

[WasmFXCert and Iris-WasmFX](https://doi.org/10.1145/3808271), with a [Rocq artifact](https://github.com/logsem/iris-wasmfx), are 2026 research results that mechanize WasmFX operational semantics/type safety and develop an Iris program logic for modular reasoning about stack-switching programs. They demonstrate that continuation-bearing Wasm code can be verified, while also documenting the difficulty introduced by stored continuations and non-well-bracketed control.

The useful architectural split is therefore:

```text
EffectCore operations and data
  -> WIT imports/exports and Component Model async     (interop path)
  -> Wasm continuation/stack-switching instructions    (control path)
```

The interop path can be pursued now using developer-preview tools. The control path remains a research/proposal target. A formal Effect-to-Wasm story may eventually use both, but their preservation statements will be different.

## What counts as shared algebraic data in Wasm?

Several layers are often described as “typed sharing,” but they guarantee different things.

| Artifact | Shared object | Identity/evolution | Execution semantics | Current status |
| --- | --- | --- | --- | --- |
| WIT + Component Model | Products, sums, options, results, lists/maps, resources, futures/streams, functions at component boundaries | Package names, semver, resolved type definitions | Canonical lift/lower and component calling conventions | Implemented developer-preview tooling; standardization ongoing |
| Candid | Self-describing typed values, service/function references | Structural subtyping and type-directed coercion across interface versions | Serialization/deserialization and call signatures, not service behavior | Deployed Internet Computer IDL and codec; specified rather than fully mechanized |
| RichWasm | Fine-grained shared memory across differing source-language disciplines | Typed locations, capabilities, linearity, and polymorphism | Typed IL reduction and compilation experiments | Coq-mechanized type safety plus research compilers; not standardized |
| Wasm GC Canonical ABI pre-proposal | Component values represented directly with selected core GC types | Component/core type compatibility, including recursion-group identity constraints | Proposed canonical lift/lower in GC mode | Open pre-proposal and implementation work, not normative behavior |
| Core Wasm GC/reference types | Runtime heap/reference shapes within compatible engines | Wasm type identities and validation | Core runtime instructions | Core proposal/runtime feature, not a durable cross-language object codec |
| StableHLO | Versioned tensor operations and types | Compatibility policy and versioned opset | ML computation semantics | Shipped domain-specific portable IR, not general application data |
| IPLD Schema + codecs | Typed immutable linked data | Content identifiers and representation strategies | No computation semantics | Deployed data ecosystem, independent of Wasm |
| Unison codebase | Typed AST definitions and dependency graph | Content hashes | Unison runtime and abilities | Shipped language/runtime, not a language-neutral ABI |
| Temporal/Restate/Golem history | Commands, events, results, and durable progress | Runtime-specific workflow/component identities and versioning | Replay/durable-execution contract | Shipped systems; primarily operational evidence |

[StableHLO](https://openxla.org/stablehlo/spec) is worth noting because it shows how a domain can standardize a versioned algebraic operation set for interchange and optimization. It succeeds by restricting the domain to tensor programs. Foldlab should expect the same lesson: a useful Effect Core will need an admitted operation universe and explicit extension mechanism rather than an unconstrained “serialize any TypeScript effect” promise.

## Shared languages of concurrency

There is no single dominant concurrency language because different systems choose different observables and guarantees. Several mature families are relevant.

### Global protocols and choreographies

[Scribble](https://www.doc.ic.ac.uk/~rhu/scribble/ScribbleTypeLanguagev1.0-Draft2.3.html) defines a textual global/local protocol grammar founded on multiparty session types, with projectability as a key well-formedness condition. The [Scribble-Java toolchain](https://www.doc.ic.ac.uk/~rhu/scribble/tutorial/) generates endpoint APIs from multiparty protocols.

[Choral](https://www.choral-lang.org/) is a usable choreographic language/compiler that generates a Java library per role from a global program. Its repository supplies a compiler and tests, but its runtime implementation and theorems should not be inferred merely from the project description.

[Pirouette](https://akhirsch.science/papers/pirouette/) is higher-order typed functional choreography work with endpoint projection and Coq-verified metatheory. It is particularly relevant to Foldlab's “global canonical entity projected into context” direction.

[Verified Library-Level Choreographic Programming with Algebraic Effects](https://arxiv.org/abs/2407.06509) makes the connection explicit: choreographic coordination is exposed as effects in a host-language library while endpoint projection remains the semantic bridge. The newer Lean development [Mech](https://arxiv.org/abs/2607.15174) mechanizes endpoint-projection correctness, communication safety, and deadlock freedom. These are research artifacts, but they are unusually close to Foldlab's intended combination of global descriptions, local effects, and proof-producing projection.

These systems address who communicates with whom and in what order. They do not by themselves model the internal effects, resources, or scheduling implementation of each participant. A Foldlab global descriptor could contain local Effect Core programs while using a choreography/session layer to constrain cross-participant events.

### State machines, temporal specifications, and process algebra

- [P](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/tr-8.pdf) is a language for asynchronous event-driven state machines with systematic exploration and environment modeling; Microsoft reports deployment in a Windows driver stack. That is strong industrial prior art for executable asynchronous models.
- [TLA+ and PlusCal](https://lamport.org/tla/tools.html) model concurrent algorithms as state/action systems and provide explicit-state model checking and proof tools. They are excellent for safety/liveness and algorithm design but are not typed effect IRs.
- [mCRL2](https://github.com/mCRL2org/mCRL2) is both a process specification language and a toolset for state-space generation, simulation, reduction, equivalence, and refinement.
- [FDR](https://cocotec.io/fdr/manual/index.html) checks refinement between CSP processes under traces, failures, and failures/divergence models.
- [MLIR's Async dialect](https://mlir.llvm.org/docs/Dialects/AsyncDialect/) makes dependencies, async values/tokens, groups, await, coroutine lowering, and runtime operations explicit in compiler IR. Its documentation explicitly permits sequential execution of an `async.execute`; concrete concurrency depends on lowering. This is an optimization IR, not a platform-independent liveness contract.

The 2026 work [An Equational Axiomatization of Dynamic Threads via Algebraic Effects](https://homepages.inf.ed.ac.uk/slindley/papers/dynamic-threads.pdf) is notable because it supplies a complete algebraic theory for `fork` and `wait` under labeled-partial-order observations, with soundness, adequacy, and first-order full abstraction results. It is a formal candidate for a small reusable concurrency grammar, not yet a runtime or wire standard.

[Effectful Mealy Machines](https://doi.org/10.4230/LIPIcs.CALCO.2025.1) provides a complementary coalgebraic model for stateful stream transducers whose transitions may perform global effects. It defines both bisimilarity and effectful trace semantics and covers deterministic, nondeterministic, probabilistic, shared-state, and other machine instances. This is a useful semantic candidate for Foldlab's stream-facing observations and topology adapters, especially where equivalence should be stated over causal input/output behavior rather than internal continuation steps. It is a formal model, not a serialization grammar, protocol standard, or optimizer implementation.

These are complementary lenses. A global protocol constrains communication shape; an effect descriptor says which interactions a computation may request; a transition system exposes scheduling and state; temporal logic states safety/liveness; a process algebra supplies equivalence/refinement; and a compiler IR exposes transformation opportunities.

## Equivalence-guided optimization

### Existing techniques

#### Interaction and Choice Trees

Interaction Trees provide weak bisimulation for visible events and silent computation. [Choice Trees](https://arxiv.org/abs/2211.06863) extend the approach with internal and external nondeterminism, transition-system semantics, bisimulation/refinement infrastructure, and examples including CCS and cooperative multitasking. Choice Trees are therefore a strong reference when a Foldlab optimizer begins to distinguish program choice from scheduler/environment choice.

#### Algebraic laws and handler fusion

[Fusion for Free](https://people.cs.kuleuven.be/~tom.schrijvers/portfolio/mpc2015.html) shows how handler sequences over free syntax can be fused to avoid intermediate trees and repeated traversals. The 2025 paper [From High to Low: Simulating Nondeterminism and State with State](https://doi.org/10.1017/S0956796824000133) gives a chain of lowerings—from local state and nondeterminism toward stacks and trails—and proves the transformations using handler fusion laws.

This is an important precedent: runtime-like optimizations can be derived as meaning-preserving handler transformations rather than asserted as compiler folklore.

#### Equality saturation and rule discovery

[egg](https://arxiv.org/abs/2004.03082) uses e-graphs to compactly represent many terms related by supplied equations and extracts a low-cost representative. [Ruler/Enumo](https://github.com/uwplse/ruler) goes further by enumerating terms, evaluating candidates, inferring rewrite rules with equality saturation, and minimizing a theory.

These tools can systematically discover candidate rewrites. Their result is only as sound as the supplied semantics, samples/solver theory, side conditions, and extraction cost. For effectful terms, an equation must be a congruence under the chosen handlers and observations. Reordering two operations because their return values coincide is unsound if logs, service requests, resource lifetime, interruption, or scheduler visibility can distinguish them.

The OOPSLA 2026 work [Efficient Extraction for Effectful E-Graphs](https://2026.splashcon.org/details/oopsla-2026/156/Efficient-Extraction-for-Effectful-E-Graphs) attacks a separate problem after saturation: how to extract a representative while respecting memory and I/O order. It proves that finding an effect-safe extraction is NP-complete, introduces Statewalk DP parameterized by a dataflow measure called statewalk width, and implements the algorithm in the `eqcc` prototype for imperative Bril programs. This is concrete evidence that effect-order-aware extraction can be practical without an external ILP solver. It does not validate the rewrite rules that populated the e-graph, prove equivalence to Effect TypeScript, or turn the prototype into a general effect optimizer.

[Effectful Improvement Theory](https://doi.org/10.1016/j.scico.2022.102792) adds cost as an algebraic effect and develops contextual improvement results for effectful programs, including dead-code and restricted common-subexpression transformations. It supplies an important missing distinction: bisimulation or contextual equality establishes sameness of behavior, while improvement additionally orders equivalent implementations by an explicit cost observation.

#### Translation validation and superoptimization

[Alive2](https://github.com/AliveToolkit/alive2) symbolically executes LLVM IR and checks refinement for individual transformations using SMT. Its [PLDI paper](https://doi.org/10.1145/3453483.3454030) is explicit that validation is bounded and that unsupported interprocedural cases remain outside the tool. [STOKE](https://github.com/StanfordPL/stoke) searches stochastically over x86 code and has equivalence-checking infrastructure, while explicitly identifying itself as a research prototype.

These systems establish a productive division of labor:

```text
candidate producer  ->  semantic validator  ->  independent checker/evidence
```

The candidate producer can be heuristic, enumerative, profile-guided, e-graph based, or LLM assisted. The semantic court of appeal must be independent of that proposal mechanism.

#### Reified optimization schedules

[MLIR's Transform dialect](https://mlir.llvm.org/docs/Dialects/Transform/) represents optimization control as IR interpreted against payload IR. It separates a transformation schedule from the program it transforms and gives transform operations explicit effects and failure modes. This is excellent architectural precedent for making an optimization strategy itself a serializable, inspectable program. MLIR does not thereby prove that arbitrary transform dialect operations preserve a Foldlab semantics.

### Can bisimulation systematically “sniff” optimizations?

Yes, with an important qualification:

> Bisimulation can classify or validate behaviorally equivalent candidates and can expose redundant state. By itself it does not invent a lower-cost implementation and does not prove that one equivalent representative is faster.

For a finite or finitely abstracted effect system, a practical pipeline is:

1. **Freeze the observation.** Define visible operation labels, terminal outcomes, and which administrative steps are `tau`/silent. Decide whether timing, allocation, log order, cancellation, finalizer order, and scheduler choices are visible.
2. **Lower to a labeled transition system.** Give both the source effect term and candidate implementation explicit machine states. Bound data or use a sound abstraction when the state space is infinite.
3. **Minimize or compare.** Use strong bisimulation when every internal step matters; weak or branching bisimulation when administrative steps should be hidden; trace or failures refinement when nondeterminism and refusal/divergence matter. The mCRL2 tools already support LTS conversion, minimization, and strong/branching/weak comparisons; FDR provides CSP refinement models.
4. **Find commuting administrative work.** The mCRL2 [`lpsconfcheck`](https://mcrl2.org/web/user_manual/tools/release/lpsconfcheck.html) tool generates and attempts to prove confluence conditions for internal transitions, producing counterexample valuations when checks fail. This is a concrete existing “optimization sniffer” for opportunities to collapse or reorder silent work in a process model.
5. **Inspect quotient structure.** Equivalent states with different stack depth, handler traversals, allocations, or transition counts identify potential fusion, memoization, batching, dead-frame elimination, handler specialization, or scheduling simplification.
6. **Generalize candidates.** Use e-graphs or Ruler-style theory exploration to infer parameterized rewrite schemas and side conditions from repeated finite examples.
7. **Prove the schema.** In Lean, prove weak bisimulation, simulation, or trace refinement for all accepted terms—not merely the enumerated examples. For Interaction Trees this can be an `eutt`/weak-equivalence theorem; for an abstract machine it can be a forward/backward simulation.
8. **Attach a cost argument.** Define a cost semantics or collect runtime profiles separately. Behavioral equivalence does not imply fewer allocations or lower latency on a named host.
9. **Cross the implementation boundary.** Differentially execute the optimized and reference programs against the pinned Effect runtime and named JS/Wasm hosts. This moves the exact supported slice toward G3/G5 evidence without upgrading the theorem beyond its model.

In schematic form:

```text
EffectCore term
    |
    +--> reference ITree/LTS -----------+
    |                                   |
    +--> candidate generator            | equivalence/refinement
            |                           |
            +--> e-graph / enumerator --+
                         |
                         +--> cost extraction
                         +--> Lean proof obligation
                         +--> runtime differential fixture
```

### Where bisimulation stops scaling

Explicit bisimulation is effective for finite control and bounded data. Arbitrary closures, unbounded queues, recursive services, real clocks, and dynamic topology create infinite-state systems. The available responses are:

- symbolic bisimulation or bisimulation-up-to techniques;
- Interaction Tree coinduction for structurally recursive systems;
- abstract interpretation with a proved simulation to an abstract LTS;
- assume-guarantee or compositional reasoning over participants;
- session/choreography projection to restrict communication shape;
- bounded translation validation that reports its bound; and
- relational program logics for heap state and stored continuations.

Liveness also requires fairness assumptions and infinite observations. A finite trace-equivalence result cannot establish eventual completion under a scheduler.

## A concrete Foldlab research agenda

### Phase 0: freeze vocabulary and evidence

Define and version:

- `Descriptor` — canonical effect program data;
- `Signature` — indexed operations and responses;
- `WF`, `HasKind`, and `HasType` judgments;
- `Step` / `Runs` — relational dynamics;
- `denote` — Interaction Tree or other semantic interpretation;
- `observe` — explicit visible behavior;
- `refines` and `equivalent` — observation-relative relations;
- `Handler` — interpretation from one signature to another;
- `encode` / `decode` / `normalize`;
- `project` — participant or target-language projection; and
- an evidence record aligned with G0–G5.

Do not make Effect's current internal opcode objects the canonical syntax. They are a source artifact to ingest and relate.

### Phase 1: a serializable first-order Effect Core

Admit only:

- pure return;
- typed failure;
- one typed service request;
- sequential composition;
- typed failure handling; and
- one visible event such as logging.

Replace arbitrary continuation closures with named, typed blocks or defunctionalized frames. Give the core a canonical binary/data encoding independent of Effect source text.

Use Candid as a differential design oracle for typed blobs and evolution, not as a format to copy blindly. State whether Foldlab requires self-description, unknown-field retention, structural subtyping, and coherence across decode/re-encode chains; then turn each decision into a law or an explicit non-goal.

Initial theorem inventory:

```text
decode_encode
encode_decode_canonical
normalize_idempotent
normalize_denotation
interpreter_sound
interpreter_complete_deterministic_fragment
handler_identity
handler_composition
codec_denotation_preservation
```

### Phase 2: direct semantics versus a continuation machine

Define:

- an ITree/PolyFun denotation;
- a small-step stack machine with explicit frames; and
- a relation between a machine configuration and a semantic tree.

Prove machine-step simulation and weak observational equivalence for the frozen fragment. This is the minimal result that begins to answer whether a continuation-based implementation adheres to an abstract effect semantics.

Structure later cross-language correspondences as DimSum-style event wrappers: each runtime receives its own state machine and memory assumptions, while the wrapper relates only named boundary events. This avoids baking JavaScript, Wasm, or one Effect runtime revision into the canonical semantics.

### Phase 3: an equivalence and optimization laboratory

Build exporters and importers for a finite fragment:

- Effect Core to an mCRL2 or simple LTS format;
- quotient/minimization results back to provenance-linked states;
- an e-graph language for pure and effectful terms;
- a separate effect-safe extraction constraint and witness, so rewrite validity is not confused with execution-order legality;
- a rule-candidate ledger recording examples, counterexamples, side conditions, and cost estimates; and
- Lean theorem stubs generated for candidate rewrites.

Use Ruler/Enumo or a smaller enumerator only as a candidate producer. Accepted rewrite rules must be Lean theorems or carry a separately checked translation-validation certificate.

Early optimization targets should be structurally obvious but nontrivial:

- handler fusion;
- elimination of administrative `succeed`/`flatMap` frames;
- catch/fail simplification;
- batching adjacent commutative requests under an explicit independence proof;
- normalization of nested maps/flatMaps;
- trace-preserving dead event elimination; and
- specialization of a closed service environment.

### Phase 4: WIT projection and portable components

Define a supported mapping from closed Effect Core data types into WIT records, variants, options, results, lists/maps, and resources. Generate:

- a WIT interface/world;
- TypeScript and one non-JS guest binding;
- a component adapter; and
- normalized trace fixtures at the component boundary.

Keep two codecs:

- the Component Model Canonical ABI for live calls; and
- a durable canonical codec for storage/content addressing.

Evaluate the GC Canonical ABI proposal and a RichWasm-like shared-memory path only as later performance backends. Neither should determine the durable descriptor identity, and each needs its own projection and preservation statement.

Prove the type/schema mapping for the accepted subset in Lean. Treat `wit-bindgen`, component composition, and Wasmtime/jco execution as separately versioned G3/G5 evidence.

### Phase 5: Effect TypeScript conformance bridge

Construct two narrow translations:

```text
accepted TypeScript/Effect source -> Effect Core
Effect Core -> generated Effect TypeScript combinators
```

The source path should consume TypeScript compiler AST, symbol, and type facts rather than regex or pretty-printed source. The target path should generate a normalized supported subset. Differential execution should compare normalized observations against the pinned Effect runtime.

The first G4 target should be a theorem about the generated subset, not arbitrary Effect programs.

### Phase 6: WebAssembly execution paths

Pursue two experiments independently:

1. **Component interpreter:** compile or implement the reference Effect Core interpreter as a Wasm component using WIT imports for capabilities. This can run on current developer-preview toolchains.
2. **Continuation lowering:** compile the continuation machine to the stack-switching/WasmFX model when the proposal/toolchain is sufficiently pinned. Use WasmFXCert/Iris-WasmFX as proof-architecture references.

Eventually, prove that the component and continuation paths preserve the same declared observations. Until then, compare them with generated traces and retain separate claim gates.

### Phase 7: global concurrency and topology

Only after the local effect semantics is stable, add:

- a global choreography/session description;
- endpoint projection into local Effect Core programs;
- explicit channels, queues, delivery guarantees, cancellation, and topology-change events;
- finite and infinite trace semantics;
- fairness parameters; and
- projection soundness plus global/local trace correspondence.

Pirouette, Scribble/MPST, Choral, PolyFun, and process-algebra tools should be evaluated as distinct substrates, not blended before their observation models are reconciled.

## High-value tooling implied by the research

The literature suggests a coherent tool suite rather than one monolithic prover:

1. **Descriptor inspector** — shows normalized syntax, kinds, effect requirements, code/dependency hashes, and unsupported constructs.
2. **Semantic trace viewer** — displays visible events and hidden `tau` steps under a selected observation.
3. **Behavior differ** — compares two descriptors by bounded traces, bisimulation/refinement where decidable, or generated proof obligations.
4. **Optimization explorer** — enumerates/e-saturates candidates, attaches cost estimates, and never promotes a rule without evidence.
5. **Handler law checker** — tests and proves whether a handler respects the equations required by an optimization.
6. **WIT projector** — emits packages/worlds and reports which descriptor types cannot be represented faithfully.
7. **Effect TS bridge** — ingests/generates the admitted Effect subset and records exact source/runtime pins.
8. **Replay validator** — checks event-history compatibility across descriptor/runtime versions.
9. **Evidence ledger** — distinguishes kernel proof, solver certificate, model-check result, differential fixture, compilation result, and host execution.

## Research questions that remain open enough to matter

1. **Portable effect ABI:** Can an indexed operation signature, handler requirements, failure/cancellation vocabulary, and observation policy be standardized above WIT without choosing one source language?
2. **Serializable higher-order effects:** Which scoped effects can be closure-converted and defunctionalized while preserving meaning, resource ownership, and one-shot resumption?
3. **Content-addressed semantics:** What normalization is required before an effect program's hash denotes meaning stably across printer, compiler, and runtime versions?
4. **Versioned replay:** Can history migration be specified as trace refinement rather than a set of ad hoc SDK compatibility rules?
5. **Cross-runtime contextual equivalence:** Which observations survive translation among Effect TS, a Lean interpreter, a Wasm component, and a stack-switching runtime?
6. **Effect-aware equality saturation:** How should e-classes carry effect rows, handler scope, linear resources, interruption regions, and proof side conditions so that equality remains a congruence?
7. **Optimization under concurrency:** Can partial-order reduction, independence proofs, and session structure make useful optimization discovery tractable without fixing a global schedule?
8. **Proof-carrying components:** Can a component package carry its descriptor hash, WIT world, codec theorem identifiers, translation certificate, and runtime conformance record as independently checkable metadata?
9. **Meaning and cost together:** Can Foldlab define a costed weak bisimulation that preserves visible behavior while exposing stack switches, allocations, copies, handler searches, and component-boundary transfers?

## Assessment

The project is not entering a dormant niche. Effects and handlers are an active meeting point for language semantics, type systems, concurrency, runtime implementation, program logic, and compiler optimization. WebAssembly is simultaneously developing the two substrate layers the project would need: rich typed component interfaces and low-level continuation support. Formal WebAssembly work is also moving toward generated, executable standards and modular program logics.

The frontier is fragmented. That fragmentation is the opportunity. A Foldlab contribution would be strongest if it does not attempt to replace Effect, WIT, Interaction Trees, or process algebras. It should define the missing semantic joint:

> a small canonical, serializable, content-addressable effect description with explicit observations, proved transformations, generated interop projections, and evidence that remains attached across runtime boundaries.

## Primary source index

Links below are discovery authorities for this research snapshot. Any source admitted into a theorem or conformance gate should be pinned by edition, release, or commit in the project source ledger.

### Effect semantics, handlers, and verification

- Plotkin and Pretnar, [Handling Algebraic Effects](https://doi.org/10.2168/LMCS-9(4:23)2013).
- Bauer and Pretnar, [Programming with Algebraic Effects and Handlers](https://arxiv.org/abs/1203.1539).
- Xia et al., [Interaction Trees](https://www.cis.upenn.edu/~stevez/papers/XZHH%2B20.pdf); [Rocq repository](https://github.com/DeepSpec/InteractionTrees).
- [PolyFun](https://github.com/Verified-zkEVM/PolyFun), Lean polynomial functors, ITrees, and interaction frameworks.
- Sammler et al., [DimSum](https://doi.org/10.1145/3571220); [Coq artifact](https://zenodo.org/records/7306313).
- van den Berg and Schrijvers, [A Framework for Higher-Order Effects and Handlers](https://doi.org/10.1016/j.scico.2024.103086).
- Bosman et al., [A Calculus for Scoped Effects and Handlers](https://doi.org/10.46298/lmcs-20(4:17)2024).
- [Modal Effect Types](https://doi.org/10.1145/3720476) and [Rows and Capabilities as Modal Effects](https://arxiv.org/abs/2507.10301).
- Xie et al., [Parallel Algebraic Effect Handlers](https://arxiv.org/abs/2110.07493).
- Song, Foo, and Chin, [Specification and Verification for Unrestricted Algebraic Effects and Handling](https://doi.org/10.1145/3674656).
- de Vilhena et al., [A Relational Separation Logic for Effect Handlers](https://doi.org/10.1145/3776676).
- Xie and Leijen, [Generalized Evidence Passing for Effect Handlers](https://doi.org/10.1145/3473576).
- [Koka compiler and language](https://github.com/koka-lang/koka).
- [Effekt compiler](https://github.com/effekt-lang/effekt) and [compiler pipeline](https://github.com/effekt-lang/effekt-website/blob/main/docs/implementation.md).
- Sivaramakrishnan et al., [Retrofitting Effect Handlers onto OCaml](https://arxiv.org/abs/2104.00250); [OCaml 5.4 Effect API](https://ocaml.org/manual/5.4/api/Effect.html).
- [Zero-Overhead Lexical Effect Handlers](https://doi.org/10.1145/3763177).

### WebAssembly semantics, components, and continuations

- [WebAssembly specifications](https://webassembly.org/specs/).
- [SpecTec adoption announcement](https://webassembly.org/news/2025-03-27-spectec/) and [Wasm SpecTec paper](https://arxiv.org/abs/2311.07223).
- [WasmCert-Coq](https://github.com/WasmCert/WasmCert-Coq).
- [Pinned WebAssembly Component Model milestone snapshot](https://github.com/WebAssembly/component-model/blob/1af0b35e1bfc03bd4ad9603be2f676316ff9f420/README.md) and [proposal-phase registry](https://github.com/WebAssembly/proposals).
- [Pinned WIT specification](https://github.com/WebAssembly/component-model/blob/1af0b35e1bfc03bd4ad9603be2f676316ff9f420/design/mvp/WIT.md).
- [Pinned Canonical ABI](https://github.com/WebAssembly/component-model/blob/1af0b35e1bfc03bd4ad9603be2f676316ff9f420/design/mvp/CanonicalABI.md).
- Davies et al., [RichWasm](https://doi.org/10.1145/3656444); [pinned Coq/compiler artifact](https://github.com/RichWasm/RichWasm-artifact/tree/62c4bbcd67f4613304b3ae5bc6a85a901c2e9c8d).
- [Wasm GC Canonical ABI pre-proposal](https://github.com/WebAssembly/component-model/issues/525).
- [Pinned Component Model concurrency explainer](https://github.com/WebAssembly/component-model/blob/1af0b35e1bfc03bd4ad9603be2f676316ff9f420/design/mvp/Concurrency.md).
- [WASI 0.3 release](https://github.com/WebAssembly/WASI/releases/tag/v0.3.0) and [Wasmtime 46 release record](https://github.com/bytecodealliance/wasmtime/blob/v46.0.0/RELEASES.md).
- [`wit-bindgen`](https://github.com/bytecodealliance/wit-bindgen), [`wasm-tools`](https://github.com/bytecodealliance/wasm-tools), and [`jco`](https://github.com/bytecodealliance/jco).
- [wRPC draft specification](https://github.com/bytecodealliance/wrpc/blob/1b182e762e9e11a32df671ab52303eede2bd3c27/SPEC.md) and [wasmCloud RPC runtime](https://wasmcloud.com/docs/v1/hosts/lattice-protocols/rpc/).
- [WasmFX project](https://wasmfx.dev/) and [Continuing WebAssembly with Effect Handlers](https://arxiv.org/abs/2308.08347).
- [WebAssembly stack-switching proposal](https://github.com/WebAssembly/stack-switching/blob/main/proposals/stack-switching/Explainer.md).
- [WasmFXCert / Iris-WasmFX artifact](https://github.com/logsem/iris-wasmfx).

### Content-addressing, schemas, and durable execution

- [Pinned Candid specification](https://github.com/dfinity/candid/blob/7cc578c060df6aabdb6654abe9c0f09a8df6584c/spec/Candid.md).
- [Unison repository](https://github.com/unisonweb/unison) and [content-addressed code overview](https://www.unison-lang.org/docs/the-big-idea/).
- [IPLD Schemas](https://ipld.io/docs/schemas/), [schema introduction](https://ipld.io/docs/schemas/intro/), and [IPLD specifications](https://github.com/ipld/specs).
- [Temporal event-history documentation](https://github.com/temporalio/documentation/blob/main/docs/encyclopedia/event-history/go.mdx) and [history-service architecture](https://github.com/temporalio/temporal/blob/main/docs/architecture/history-service.md).
- [Restate architecture](https://docs.restate.dev/references/architecture).
- [Golem WebAssembly component runtime](https://github.com/golemcloud/golem).
- [Golem durability](https://learn.golem.cloud/v1.5/develop/additional) and [persistence](https://learn.golem.cloud/v1.5/operate/persistence) documentation.

### Concurrency and global protocols

- [Scribble protocol grammar](https://www.doc.ic.ac.uk/~rhu/scribble/ScribbleTypeLanguagev1.0-Draft2.3.html) and [Scribble-Java](https://www.doc.ic.ac.uk/~rhu/scribble/tutorial/).
- [Choral language and compiler](https://www.choral-lang.org/) and [repository](https://github.com/choral-lang/choral).
- Hirsch and Garg, [Pirouette](https://akhirsch.science/papers/pirouette/).
- [Verified Library-Level Choreographic Programming with Algebraic Effects](https://arxiv.org/abs/2407.06509) and [Mech](https://arxiv.org/abs/2607.15174).
- [An Equational Axiomatization of Dynamic Threads via Algebraic Effects](https://homepages.inf.ed.ac.uk/slindley/papers/dynamic-threads.pdf).
- Bonchi, Di Lavore, and Román, [Effectful Mealy Machines](https://doi.org/10.4230/LIPIcs.CALCO.2025.1); [full version](https://arxiv.org/abs/2410.10627).
- [P: Safe Asynchronous Event-Driven Programming](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/tr-8.pdf).
- [TLA+ tools](https://lamport.org/tla/tools.html).
- [mCRL2 toolset](https://github.com/mCRL2org/mCRL2).
- [FDR refinement checker](https://cocotec.io/fdr/manual/index.html).
- [MLIR Async dialect](https://mlir.llvm.org/docs/Dialects/AsyncDialect/).

### Optimization, equivalence, and portable IR

- Wu and Schrijvers, [Fusion for Free](https://people.cs.kuleuven.be/~tom.schrijvers/portfolio/mpc2015.html).
- Schrijvers et al., [From High to Low](https://doi.org/10.1017/S0956796824000133).
- [Choice Trees](https://arxiv.org/abs/2211.06863).
- [Effectful Improvement Theory](https://doi.org/10.1016/j.scico.2022.102792).
- Willsey et al., [egg](https://arxiv.org/abs/2004.03082).
- [Ruler/Enumo](https://github.com/uwplse/ruler), rewrite-rule inference with equality saturation.
- Flatt et al., [Efficient Extraction for Effectful E-Graphs](https://2026.splashcon.org/details/oopsla-2026/156/Efficient-Extraction-for-Effectful-E-Graphs).
- [Alive2 repository](https://github.com/AliveToolkit/alive2) and [PLDI paper](https://doi.org/10.1145/3453483.3454030).
- [STOKE](https://github.com/StanfordPL/stoke).
- [MLIR Transform dialect](https://mlir.llvm.org/docs/Dialects/Transform/) and [tutorial](https://mlir.llvm.org/docs/Tutorials/transform/).
- [StableHLO specification](https://openxla.org/stablehlo/spec).
- [mCRL2 confluence checker](https://mcrl2.org/web/user_manual/tools/release/lpsconfcheck.html) and [LTS comparison tool](https://mcrl2.org/web/user_manual/tools/release/ltscompare.html).
