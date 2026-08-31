# Effect Core v1 — existing-type annotation ledger

Status: **PRE-GRADE / PROPOSED**, 2026-08-31

Claim gate: none

Purpose: annotate the carriers already present in the estate and in the pinned
Effect package before proposing new Effect Core declarations. This is an
organizational and representation-design ledger. It does not ratify a new
type, change an existing declaration, or claim a bridge theorem.

## 1. Annotation contract

Every relevant existing or proposed declaration receives one stable
annotation row with these fields:

```text
ExistingTypeAnnotation =
  annotationId          stable packet-local ID
  declaration           fully qualified Lean name or canonical public TS ID
  source                exact repository/package path and pin
  currentAuthority      ratified | implemented-unpromoted | vendored-source
  semanticRole          syntax | handler | state | observation | logic |
                        source-type | target-type | subcalculus | evidence
  disposition           reuse | restrict | bridge | embed |
                        separateCalculus | targetOnly | proposedNew
  meaningOwner          declaration or specification that owns denotation
  identityOwner         declaration/codec that owns canonical bytes, if any
  proposedUse           role in Effect Core v1
  preservedFacts        exact theorem/definition names relied on
  missingFacts          obligation IDs, never prose-only “later” markers
  prohibitedUse         duplication or inference the row forbids
  sourceDigest          generated later from the exact declaration bytes
```

`currentAuthority` and `disposition` are independent. An implemented type can
still be restricted, and a vendored source type can be target-only. A proposed
new type is never marked ratified by appearing in this ledger.

The machine-readable successor is a generated table keyed by
`annotationId`. This Markdown file is the bootstrap annotation and review
surface; after ratification, the generated table becomes authoritative and a
human projection replaces hand-maintained rows.

## 2. Existing Lean semantic spine

All rows in this section were observed in the current `library/cas` source.
The listed theorems are code coordinates to reuse, not new claims by this
packet.

| ID | Existing declaration | Source | Disposition | Effect Core v1 annotation |
| --- | --- | --- | --- | --- |
| `EC1-XT001` | `Cas.Lang.Sig` | `library/cas/Cas/Lang/Sig.lean` | reuse | The existing operation/answer family remains the minimal semantic signature. `Alphabet` is checked first-order metadata that elaborates to a `Sig`; it is not a competing handler language. |
| `EC1-XT002` | `Cas.Lang.Sig.sum` / `⊕ₛ` | same | reuse | Closed semantic families compose through the existing signature sum. Public-surface dispositions do not themselves become sum arms until an authored alphabet selects an operation. |
| `EC1-XT003` | `Cas.Lang.Prog S A` | `library/cas/Cas/Lang/Prog.lean` | restrict | Retain as inductive proof syntax and the free sequential program carrier. Its host-function continuations prohibit canonical serialization, so authored content is the first-order graph and may elaborate into `Prog` only at a semantic/proof boundary. |
| `EC1-XT004` | `Prog.bind`, `Prog.op`, `Prog.inl`, `Prog.inr` | `Prog.lean`; laws in `Representation.lean` and `Backend/SumAlgebra.lean` | reuse | Reuse the monad and signature-injection laws. Do not restate bind or signature-sum semantics inside the graph checker. |
| `EC1-XT005` | `Cas.Lang.Handler S M` | `library/cas/Cas/Lang/Handler.lean` | reuse | Remains the one-operation-to-target meaning carrier. A proposed direct-handler environment is a finite, checked selection/composition of existing handlers plus region ownership; it must elaborate to `Handler`, not compete with it. |
| `EC1-XT006` | `Cas.Lang.interpret` | same | reuse | Remains the structural fold from `Prog` into a target monad. `interpret_bind` is the inherited composition theorem. Graph semantics owes a translation/simulation into this boundary where applicable. |
| `EC1-XT007` | `Handler.sum` and its uniqueness/projection laws | `Handler.lean`; `Backend/SumAlgebra.lean` | reuse | Direct family composition uses the existing sum handler and its theorem family. A public census row never receives a handler merely because its type mentions Effect. |
| `EC1-XT008` | `IsMonadMorphism`, `IsMorphE` | `library/cas/Cas/Backend/Universal.lean` | reuse | Use as proof predicates for handler-induced interpretations and initiality. Do not create a second “handler homomorphism” record. |
| `EC1-XT009` | `RefM`, `referenceHandler`, `interpretRef` | `library/cas/Cas/Lang/Handler.lean` | embed | These own current CAS meaning. The general Effect Core reference machine embeds/preserves this handler on the CAS-only fragment; it does not redefine CAS admission. |
| `EC1-XT010` | `SemEq`, `ObsEq` | `library/cas/Cas/Lang/Representation.lean` | bridge | Reuse for existing handler- and CAS-observation equalities. General Effect Core equality is mask-indexed and must state how it specializes to these relations. |
| `EC1-XT011` | `CasE`, `CasSig` | `library/cas/Cas/Lang/Ops.lean` | embed | The CAS alphabet arm is existing law. `injectCas` selects it without changing operation identity. |
| `EC1-XT012` | `LlmE`, `LlmSig`, `AgentSig` | same | separateCalculus | Prior example of signature composition. It is not automatically part of Effect Core v1's selected alphabet; any admission is an explicit versioned decision. |
| `EC1-XT013` | `ByteE`, `ByteSig`, `Handler.through` | `library/cas/Cas/Lang/Tower.lean` | reuse | The existing translation-then-handler tower is the model for lowering one effect family through another. Reuse it for byte/transport targets rather than adding ambient host calls. |
| `EC1-XT014` | `RootE`, `RootSig`, `StoreSig`; `WordE`, `WordSig`, `WordedSig` | `library/cas/Cas/Lang/Roots.lean`; `Worded.lean` | reuse | Existing store/root/word extensions stay modular signature arms and direct handlers. Their state and observations remain owned by those modules. |
| `EC1-XT015` | `Refusal` | `library/cas/Cas/Lang/Interp.lean` | restrict | Existing CAS refusal remains exact for the CAS sublanguage. General typed failures, defects, and interruption use the new cause/exit layer and must translate CAS refusal without erasure. |
| `EC1-XT015A` | `Refusal.Clause`, `RefusalMap`, `CasErrorTag` | `library/cas/Cas/Lang/RefusalMap.lean` | reuse | This is the existing exhaustive CAS refusal-kind classification and host join. Effect Core references it directly; no duplicate CAS refusal enum or hand-maintained mapping is permitted. |
| `EC1-XT016` | `Status S A` | same | bridge | Existing fueled CAS execution status is retained. The general configuration machine may have richer suspension/finalization states; a specialization theorem must recover `Status` on injected CAS. |
| `EC1-XT017` | `step`, `run` | same | bridge | Existing fueled operational face remains a CAS oracle. It is not assumed to be a monad morphism; `Universal.run_has_no_composition_law` records that boundary. |
| `EC1-XT018` | `PIn`, `PLine`, `PProg` | `library/cas/Cas/Lang/Defun.lean` | embed | Canonical first-order sequential CAS content. It remains the canonical CAS spelling and injects into the larger graph. No second CAS serialization is permitted. |
| `EC1-XT019` | `PIn.WF`, `PLine.WF`, `embedFrom`, `embed`, `runP` | same | reuse | Reuse admission, semantic embedding, and exact finite execution of the sequential table. The new checker wraps these facts on the CAS-only fragment. |
| `EC1-XT020` | `Envelope`, `PProg.envelope`, dataflow/read/write projections | same | bridge | Existing conservative classification is retained and related to the larger product classifier. Known may/must gaps remain explicit; the new classifier cannot silently promote them. |
| `EC1-XT021` | `WPre`, `WPost`, `wp`, `wlp`, `Triple`, `PartialTriple` | `library/cas/Cas/Lang/Wp.lean` | reuse | This is the existing program-logic face. The EffHOL-inspired modality study must select and relate to these definitions rather than minting an unconnected modality. |
| `EC1-XT022` | `Tree.progK`, `treeProg`, `Tree.table` and correctness theorems | `Cas/Lang/TreeProg.lean`; `Cas/Backend/EmitProg.lean`; `ProgProse.lean`; `TreeProgCorrect.lean` | reuse | Prior pattern for three lowerings joined by explicit theorems and byte gates. Effect Core generation should copy this proof organization, not the tree-specific carriers. |
| `EC1-XT023` | `RunM`, `runAsMap`, `stepAsMap` | `library/cas/Cas/Backend/Universal.lean` | restrict | Useful boundary witnesses for fueled execution. They are not denotational semantics and must not be used to infer monad-morphism laws. |
| `EC1-XT024` | `Word` and CAS value/address/node carriers | `library/cas/Cas/IR/Word.lean` and imported core modules | reuse | The CAS world lens and canonical values remain existing owners. General `World` is a product/lens frame which embeds this word; it does not rename or copy its representation. |

## 3. Pinned Effect TypeScript carriers

These are canonical public source types at `effect@4.0.0-rc.112`. They are
subject/target declarations, never the Semantic Model interface.

| ID | Existing public type | Disposition | Effect Core v1 annotation |
| --- | --- | --- | --- |
| `EC1-XT100` | `effect/Effect::Effect<A,E,R>` | bridge | The generated target must expose the selected overload's normalized `A/E/R`. These indices are not a complete dynamic footprint: defaults such as scheduling, time, or randomness may remain absent from `R`. |
| `EC1-XT101` | `effect/Cause::Cause<E>` | bridge | rc.112 exposes an empty/reasons/combine algebra. The project-owned ordered cause provenance is richer; lowering to stock Effect uses a named lossy quotient and cannot preserve tree topology under a full observation. |
| `EC1-XT102` | `effect/Exit::Exit<A,E>` | bridge | Target terminal carrier. Preserve success and the rc.112 cause quotient; retain richer internal exits for project-owned execution and proof. |
| `EC1-XT103` | `effect/Context::Key` and service/reference types | bridge | Canonical TS service identities for generated code. The Semantic Model uses closed service IDs and checked requirement rows; a source key is related through the public-surface ledger. |
| `EC1-XT104` | `effect/Layer::Layer<ROut,E,RIn>` | separateCalculus | Layer remains a dependency/resource-building calculus with a typed embedding/lowering into scoped Core. It is not flattened into a single service operation. |
| `EC1-XT105` | `effect/Fiber::Fiber`, `Fiber.await`, `Fiber.join` | bridge | Model await and join separately: await returns an `Exit`; join returns/raises the child's `A/E`. Interrupt request and interrupt-and-await are also distinct operations. |
| `EC1-XT106` | `effect/Scope::Scope` and resource APIs | bridge | Relate to explicit regions, registrations, ownership, and finalization. Host scope objects never enter canonical program content. |
| `EC1-XT107` | `effect/Channel::Channel`, `Stream`, `Sink`, `Pull`, `Take` | separateCalculus | Separate typed transducer calculus with a total embedding or direct handler. Carrier mention alone does not make an Effect Core primitive. |
| `EC1-XT108` | `effect/Schedule` and recurrence types | separateCalculus | Pure schedule description stays outside the program; stepping/retry/time effects cross through named operations and handlers. |
| `EC1-XT109` | public transaction carriers (`Tx*`) | separateCalculus | Atomic read/write/retry/orElse/commit algebra with its own laws and commit boundary. |
| `EC1-XT110` | `Runtime`, `ManagedRuntime`, `run*` eliminators | targetOnly | Execution and host observation boundary, never authored Core syntax. |
| `EC1-XT111` | arbitrary callbacks, thunks, promises, custom `Effectable` values | restrict | Public surface is inventoried, but an instance is admitted only as a named first-order block or registered foreign implementation ID with serializable payload. Arbitrary closures remain refused or target-only. |
| `EC1-XT112` | pure/type-only support declarations | restrict | A non-Effect type shape does not prove purity. Rows split into modeled pure, type-only, host-only-never-callable-from-Core, or registered foreign behavior. |

The recursive source census, not this handwritten selection, must generate the
complete list of pinned public declarations. These rows name the load-bearing
carriers and known distinctions the census must preserve.

## 4. Proposed declarations and their existing bases

| Proposed declaration | Existing base | Why it is not a duplicate | Required bridge |
| --- | --- | --- | --- |
| `Alphabet` / `OpDesc` | `Sig` | Adds finite canonical IDs, request/error/requirement/cancellation/observation metadata needed for checking and serialization. | `Alphabet.toSig`; lookup and uniqueness theorems. |
| `RawProgram` / `CheckedProgram` | `PProg`; `Prog` | General first-order control graph with invalid raw states and checked rows; each block reuses `PProg` as its sequential body, `Prog` remains semantic syntax, and `PProg` remains canonical CAS content. | erase/check adequacy; `injectCas`; elaboration to semantic programs/machine. |
| `Flow` / `Term` / `Resume` | `Prog`; `PLine`; `PProg` | Adds first-order control, captures, regions, branches, calls, one-shot resumes, fibers, and scope forms around existing sequential bodies; it does not add a second line language. | graph composition laws and simulations. |
| `DirectHandler` / `HandlerEnv` | `Handler`; `Handler.sum`; `Handler.through` | Finite typed lookup, region scoping, ownership, and explicit delegation around existing semantic handlers. `Handler.sum` combines same-target families; `Handler.through` is available only when elaboration genuinely produces an upper `Handler S (Prog T)` and lower `Handler T M`. | elaboration to `Handler`; lookup uniqueness; restoration/frame laws; direct scoped-target adequacy. |
| `CauseTree E` / `Exit E A` | CAS `Refusal`; rc.112 `Cause`/`Exit` | Preserves ordered sequential/parallel provenance which stock rc.112 flattens. | CAS-refusal injection; lossy `toEffectReasons`; target observation quotient. |
| `Configuration` / `Step` / `FinApprox` / denotation judgment | CAS `step`/`run`; `interpretRef` | Adds arbitrary control flow, external choice, fibers, scopes, resources, and coherent finite observations without a public `Behavior` datatype. | CAS specialization; fixed-decision uniqueness; executable/relational/finite agreement. |
| `ClassProduct` | `Envelope` and current projections | Product of independent may/must domains with explicit precision and cross-domain reductions. | CAS-envelope refinement; per-transfer concretization theorems. |
| `PublicSurface` / `SurfaceRowKey` | vendored declarations and runtime bank | Mechanically closes the pinned source universe; it is source evidence, not the authored alphabet. | total census/disposition gate; selected-profile link to `OpDesc`/expansions. |
| `RawTsType` / normalized `TypeExpr` | TypeScript checker types | First-order exhaustive representation required for deterministic generated Lean rows and a total elaboration/refusal boundary. | checker extraction relation and total elaborator. |
| `TsCore` / `AcceptedTs` | generated TS and `Effect<A,E,R>` | Small project-owned target grammar plus structural acceptance, independent of TypeScript/LSP silence. | lowering simulation; render/decode; exact tooling evidence. |

## 5. Annotation gates

Before a slice can freeze:

1. every declaration it imports or proposes has one annotation ID;
2. each annotation points to an existing declaration digest or a proposed
   signature ID;
3. every `proposedNew` row names why reuse/restrict/bridge/embed was
   insufficient;
4. no two rows claim canonical byte ownership for the same language value;
5. every bridge row has obligation IDs and an observation;
6. every Effect public carrier link resolves through the generated surface
   ledger, including overload/profile identity;
7. deleting or renaming an existing declaration makes the annotation gate
   red; and
8. the generated human projection is byte-identical to the machine table.

The first generated annotation pass must fail on at least these controls:
an unannotated imported declaration, two meaning owners, two identity owners,
a `Prog` serialization claim, a second canonical `PProg` spelling, a missing
await/join distinction, and a public closure admitted without a registered
implementation ID.
