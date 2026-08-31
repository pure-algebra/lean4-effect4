# Effect Core v1 — specification plan

Status: **PRE-GRADE / PROPOSED**, 2026-08-31

License intent: CC BY 4.0

Owner: Effect Language Semantics context

Claim gate: none; this packet contains no implemented definition or proved claim

## Status vocabulary

- **SETTLED PREMISE** identifies an instruction supplied for this packet. It is
  not a new estate ruling.
- **RATIFIED** identifies an operator ruling that now constrains signatures and
  implementation. Its supporting evidence and remaining proof obligations are
  still recorded separately; ratification is not theorem discharge.
- **PROPOSED TERM `EC1-*`** names a carrier, judgment, operation, or
  organizational unit introduced here. Every such name remains unratified.
- **PROPOSED RULING `EC1-R*`** is a decision requested by this packet. It does
  not amend the decision record until a later grilling and ratification act.
- **PENDING THEOREM `EC1-T*`** is an obligation, not evidence.
- **PENDING FALSIFIER `EC1-F*`** is an executable counterexample battery to be
  written by an independently assigned breaker in an authorized implementation
  run. This packet does not create tests or scripts.
- **PENDING PROVENANCE `EC1-PV*`** is not evidence and must not support a claim.

## 1. Purpose and finishing criterion

This packet specifies a first-order, typed, fully reified **effectful** core:
program topology is finite data, control may be cyclic, and all effect
continuations, handler clauses, scopes, resources, fibers, cancellations, and
foreign calls are named rather than hidden in host functions. Its full meaning
is the relational `Runs`/`Denotes : Prop`; an executable runner and derived
finite approximations are required to be adequate to that relation.

The packet is complete when it supplies, without Lean implementation:

1. raw and checked carrier boundaries;
2. a restriction/bridge to the shipped `Cas.Schema.El` value universe and
   metadata over the shipped `Cas.Lang.Sig` operation family rather than
   replacement carriers;
3. a mechanically closed rc.112 public surface, a total seven-disposition
   mapping from that surface into a smaller authored operation alphabet, and a
   direct-handler interface for every admitted operation;
4. a first-order graph and its composition algebra;
5. typed failure, scope, resource, fiber, race, and interruption semantics;
6. a classification product whose dimensions remain independent;
7. a relational meaning with executable-path and finite-approximation
   adequacy theorems;
8. an overload-derived exact `A / E / R` projection for generated
   `Effect.Effect<A, E, R>`;
9. a semantics-preserving route through a small TypeScript target IR;
10. a theorem dependency graph, falsification equations, decreases clauses,
   frame conditions, and an ordered slice plan; and
11. an admission-checked embedding that preserves the existing CAS language as
    a sublanguage and does not mint a second canonical CAS spelling.

All eleven are specified across this staged packet and its routed organization,
existing-type, exhibit, closure, and counterexample documents. None is yet
implemented or proved.

## 2. Authority and reopening boundary

### Inherited authority

- `library/cas/EFFECTS-BACKEND.md` remains the ratified law for CAS: programs
  are content, hosts are code, meanings live in direct reference handlers, and
  pure work remains outside `Prog`.
- `library/cas/Cas/Lang/Fragments.lean` remains the current fragment account:
  L-A and L-P are landed; L-S is proposed and owed.
- `.staging/operational-structure/REIFICATION-SUBSTRATE.md` remains the
  ratified placement of the step/continuation forms and layer-generation lane.
- `.staging/operational-structure/EFFECT-AST-PLACEMENT.md` and Decision 9 in
  `docs/SPECS.md` remain the recorded v0 decision: do not build a general AST
  merely to cover irregular wild TypeScript.
- `docs/effect-typescript-semantics/CLAIM-GATES.md` remains the only claim
  ladder used here.
- `docs/lab-core/TOOLS.md` remains the tool authority. It records the
  repository's TS7 successor path: exact `typescript@7.0.2`, exact
  `@effect/tsgo@0.38.0`, and Effect diagnostics as hygiene evidence only.
- `EXISTING-TYPES.md` owns the bootstrap annotation and reuse/bridge decision
  for every relevant existing or proposed carrier.
- `ORGANIZATION.md` and the local `AGENTS.md` own generated-fact placement,
  gated routing, resume state, and role separation; they do not define
  semantics.
- `EXHIBITS-REVIEW.md` owns which kernel-checked scratch findings are adopted
  and which extrapolations are prohibited. `TYPE-CLOSURE.md` owns the per-type
  proof graph and cutover predicate.
- `.staging/agent-reports/2026-08-31-effect-core-local-anchors.md` records
  proved local counterexamples and reuse anchors. It is evidence for proposed
  proof shape, not a ratification act.

### Versioned reopening

**PROPOSED RULING `EC1-R01` — versioned reopening.** Effect Core v1 reopens
only Decision 9's *general-program* half, and only under two stronger premises:

1. the subject is a newly authored, closed, versioned Effect Core alphabet,
   not arbitrary Effect TypeScript source; and
2. the consumer is proof-bearing generation and analysis, not corpus coverage.

This does not silently amend Decision 9. The v0 L-A-plus-classification ceiling
continues to govern wild-source ingestion. Effect Core v1 is a separate
authored language whose admitted TypeScript is generated from checked content.
Persistence into the staged `README.md`/`COUNTEREXAMPLES.md` packet and O0
indexing in `docs/SPECS.md` are authorized organizational acts; they do not
ratify any definition or claim. Ratification and promotion out of `.staging/`
remain separate operator acts.

### Settled premises

- **SETTLED PREMISE:** the operation alphabet is closed and versioned.
- **SETTLED PREMISE:** handlers are direct; operation dispatch does not search
  an open stack of dynamically typed handlers.

The first premise has two distinct finite objects. `PublicSurface` is the
mechanically enumerated consumer-visible rc.112 universe. `Alphabet` is the
smaller project-authored operation table used by checked programs. A total
mapping classifies every public surface row before selecting primitives; the
authored alphabet never stands in for, or defines, public-source closure.

## 3. Scope

**PROPOSED TERM `EC1-CoreDomain`.** The admitted domain is every well-formed
finite graph over the selected alphabet version. Graphs may contain arbitrary
sequential paths, data-dependent branches, joins, loops, recursive calls,
typed failure handling, scopes, finalizers, handler provision, structured and
declared unstructured fibers, interruption masks, races, and declared foreign
atoms.

The following are in scope:

- closure-converted effect control: all captures are explicit typed values;
- graph blocks whose sequential body is the existing CAS `PProg`, surrounded
  by typed parameters, region ownership, and one general-control terminator;
- the complete pinned public module/export/member/overload ledger and its
  exactly-one seven-disposition classification;
- an existing-type annotation for every imported or proposed declaration,
  with separate meaning and canonical-byte owners;
- a partial equivalence from the overlapping `ValueTy` structural fragment to
  existing `Cas.Schema.El`, with every unsupported `El` arm and every genuinely
  new runtime-handle code named rather than duplicated or assumed inhabited;
- an `Alphabet` metadata layer indexed by an existing `Sig.Op`, elaborating
  through `Sig.sum` and retaining the shipped `RootSig` and `WordSig` extension
  packages and non-disturbance laws;
- cycles and recursion represented by first-order code-point references;
- higher-order effect shapes represented by named body and exit regions;
- one-shot resumptions in v1, with multiplicity classified explicitly;
- typed `CauseTree E` values for failure, defect, interruption, sequential cause,
  and parallel cause, retained as an ordered project-owned `CauseTree`;
- an explicit lossy quotient from `CauseTree` to rc.112's flat, de-duplicated
  `Cause.reasons` representation;
- deterministic replay from a fixed initial configuration and compatible
  decision tape, including ready-fiber selections;
- relational meaning over all admitted responses and scheduler-enabled
  choices;
- deterministic `Denotes`/coherence reuse only for stable non-frontier
  outcomes in the exhibited CAS/block subfragment; the full core has no global
  uniqueness theorem and pre-completion fuel labels are not stable outcomes;
- finite, inspectable prefix observations that converge by truncation;
- distinct live fuel-exhaustion, external-answer, and scheduler frontiers which
  are neither typed failure, `CauseTree`, nor CAS `Refusal`;
- exact static `A / E / R` types and conservative dynamic effect footprints;
- direct handler definitions, including handlers whose clauses are themselves
  checked core graphs;
- resource acquisition, LIFO finalization, and exactly-once registration;
- fibers, joins, supervision, interruption, masking, and race cleanup;
- foreign effect atoms with typed contracts, declared frames, and receipts;
- a typed TypeScript target IR and per-constructor semantic preservation; and
- required TypeScript plus Effect tsgo diagnostic, code-action-idempotence,
  coverage, and negative-mutation harnesses at the source boundary;
- the existing CAS operation family and `PProg` carrier as a protected
  sublanguage; and
- existing `Refusal.Clause` and `RefusalMap` for CAS refusal-kind
  classification, without a duplicate CAS refusal enum.

The following are out of scope:

- parsing or claiming coverage of arbitrary TypeScript or arbitrary
  `Effect.gen` bodies;
- reifying JavaScript closures, prototypes, reflection, `eval`, ambient module
  state, or unchecked host callbacks;
- treating pure calculation as an effect program;
- proving the upstream Effect implementation correct;
- treating TypeScript or Effect language-service diagnostics and code actions
  as denotational authority;
- claiming that stock rc.112 preserves ordered sequential/parallel cause
  topology after the `Cause.reasons` quotient;
- claiming generated bytes preserve meaning before the target model,
  renderer/parser gate, pinned compiler, and hosted-runtime evidence exist;
- changing the CAS grammar, tag registry, or canonical `PProg` encoding;
- replacing `Cas.Schema.El` on its inhabited structural fragment, modifying
  `Cas.Lang.Sig` merely to store classification metadata, or flattening the
  shipped `Sig.sum` extensions into a new signature carrier;
- Layer topology work already placed by the reification-substrate ruling; and
- a new higher-order handler carrier for scoped child blocks, a public
  `Behavior` carrier, a second sequential block-body language, or a duplicate
  EffHOL-style modality beside existing `wlp`/`wp`.

## 4. Proposed construction decisions

| ID | Status | Decision requested | Consequence |
| --- | --- | --- | --- |
| `EC1-R02` | PROPOSED | Use a finite typed block graph, not a host-continuation tree, as the reified carrier. | Loops, recursion, sharing, and resumptions remain first-order data. |
| `EC1-R03` | PROPOSED | Put pure expressions and pure foreign functions in a separate pure-code table; effect blocks reference them through typed argument maps and guards, and the evaluator owes adequacy to a relational pure meaning. | Effect-free work remains outside `Prog`; closure conversion is inspectable; mere function totality is not mistaken for a theorem. |
| `EC1-R04` | PROPOSED | Make every effect/control suspension a block terminator with explicit successor code points. | No `Ans op -> Prog` host function is needed in stored content. |
| `EC1-R05` | PROPOSED | Permit graph cycles; define divergence only through unbounded execution, witnessed by all finite approximations remaining live. | A finite document can denote recursive or nonterminating behavior without a divergence constructor. |
| `EC1-R06` | PROPOSED | Give handler provision, error handling, scopes, masks, and races named body/exit regions rather than opaque callbacks. | Scoped and higher-order effects stay first-order. |
| `EC1-R07` | PROPOSED | Fix resumptions to one-shot in v1; reject duplicate resume statically or dynamically at the checked boundary. | Resource and cancellation accounting remain linear; multiplicity is visible rather than assumed. |
| `EC1-R08` | PROPOSED | Define direct handlers as a total typed table over the closed alphabet, with explicit delegation only to a named parent table. | Missing and ambiguous handlers are checker errors, not runtime search behavior. |
| `EC1-R09` | PROPOSED | Separate typed failure `E` from defects and interruption while retaining all three in `CauseTree E`. | The generated `E` parameter stays faithful to Effect's typed-error channel. |
| `EC1-R10` | PROPOSED | Treat a resource as a scoped acquisition plus an immediately registered release region; run releases LIFO and uninterruptibly by default. | Exactly-once cleanup becomes a state invariant and theorem target. |
| `EC1-R11` | PROPOSED | Put scheduler policy/state in `Configuration`; let it determine enabled choices, and let the typed `DecisionTape` select the ready fiber or race winner. Fairness is a predicate on compatible infinite decision streams and is never assumed by safety theorems. | Replay has one choice owner, while liveness hypotheses remain explicit. |
| `EC1-R12` | PROPOSED | Define full meaning only by relational `Runs`/`Denotes : Prop`; derive `FinApprox` data from that relation and prove truncation coherence and runner adequacy. | Lean proofs can reason by fuel without minting a public behavior/projective-family carrier or calling a finite probe universal. |
| `EC1-R13` | RATIFIED | Use a product of abstract domains, each with its own sequential, choice, parallel, and loop operators; require sound concretization and mask-selected overlap, but no full-product invariance under `SemEq`. | `EC1-CE032` proves observationally equal programs may retain different structural dataflow summaries. Renderer injectivity remains a separate open target obligation. |
| `EC1-R14` | PROPOSED | Model generated TypeScript through a small typed target IR before rendering source text; require canonical bytes, round trip, and injectivity on normalized admitted targets. | Semantic preservation is proved over data; source bytes are validated separately; tautological function determinism is not counted as evidence. |
| `EC1-R15` | RATIFIED | Preserve CAS identity by admitting raw `PProg` through a checked `CasAdmissible` boundary and recognizing only the canonical injected graph form. | Empty/dangling tables cannot inhabit `CheckedProgram`; raw ingress is partial, total `injectCas` begins only at `CheckedPProg`; `toPProg` is a sound normal-form recognizer, not a semantic projection of every equivalent CAS-only graph; admitted CAS gets no second identity. |
| `EC1-R16` | PROPOSED | Admit foreign effects only through a finite registry entry containing types, declared capabilities, frame, replay key, and observation policy. | Host escape is explicit, typed, classified, and cannot smuggle a continuation. |
| `EC1-R19` | PROPOSED | Require the TS7 `@effect/tsgo` successor as a generated-source oracle, while keeping all diagnostic and code-action output outside the Semantic Model. | Emitted programs must pass the exact tooling gate, but only structural decoding and proved bridges relate source to checked graphs. |
| `EC1-R20` | PROPOSED | Treat the recursively resolved rc.112 `PublicSurface` ledger and its seven dispositions as a frozen input to the authored `Alphabet`. | Full source closure is proved independently of how many rows become Core primitives. |
| `EC1-R21` | PROPOSED | Retain ordered project-owned `CauseTree`, but lower stock rc.112 observations through an explicit `CauseReasons` quotient. | Full-topology model theorems remain possible; stock-runtime G4 claims are limited to the quotient unless a project-owned topology-preserving adapter is used. |
| `EC1-R22` | PROPOSED | Distinguish fiber `await` from `join`, and interruption request from interruption-and-await. | Static types and cleanup timing match the selected public rc.112 overload instead of sharing one ambiguous node. |
| `EC1-R23` | PROPOSED | Derive every source-facing `A / E / R` transform from a canonical public overload row. | Catch result unions, residual error rows, empty builtin requirements, and service discharge are checked rather than hand-assumed. |
| `EC1-R24` | PROPOSED | Require machine-readable Effect diagnostics with exact generated-file coverage and an independent export-census join. | A clean partial or wrong-version language-service run fails closed. |
| `EC1-R25` | RATIFIED | Limit deterministic `Denotes`/coherence reuse to stable non-frontier outcomes in the exhibited CAS/block subfragment; keep the full core relational over decisions, answers, scheduler-enabled choices, and finite frontiers. | `EC1-CE042` refutes every choice-free denotation function. A fixed initial configuration and compatible complete decision tape determine one executable path, but changing pre-completion fuel can change frontier labels and never implies globally unique meaning. |
| `EC1-R26` | PROPOSED | Keep fuel exhaustion and external/scheduler frontiers outside `Refusal`, typed `E`, and `CauseTree`. | Insufficient fuel or a pending choice cannot masquerade as a program failure. |
| `EC1-R27` | RATIFIED | Reuse `Refusal.Clause` and `RefusalMap` for CAS refusal-kind classification, keep write-address facts explicitly dependent on `H`, and retain the existing refusal-word observation quotient. | Exact Effect `E` still comes from `OpDesc` and the checker; the CAS envelope does not synthesize it or contain exact write addresses. Any observation retaining the refusal-side word is a newly named finer mask. |
| `EC1-R28` | PROPOSED | Gate cutover per existing/proposed type annotation and all proof edges named in `EXISTING-TYPES.md` and `ORGANIZATION.md`. | No full cutover occurs while any required constructor, checker, semantics, classifier, lowering, or red-control edge remains open. |
| `EC1-R29` | PROPOSED | Reuse `PProg` as each block's sequential body and add only parameters, region, and terminator around it. | Arbitrary control gains one graph carrier without minting a second straight-line CAS carrier or canonical spelling. |
| `EC1-R30` | RATIFIED | Interpret named scoped children directly with the existing `Handler` into an adequate state/error/machine target that observes child outcomes and retains post-body state on failure. Use `Handler.sum` only to combine signature families with one target. Use `Handler.through` only for its actual tower shape: an upper `Handler S (Prog T)` followed by a lower `Handler T M`. | No `HHandler` is introduced, and `Handler.through` is not a generic way to retarget an already-direct scoped handler. `ReaderT Env (Prog CasSig)` cannot recover failures; `ReaderT Env (StateT Word (Except Refusal))` repairs catch but is still finalizer-blind; the minimum CAS witness has state outside error, `ReaderT Env (ExceptT Refusal (StateT Word Id))`. Scratch handlers remain witnesses, and ordinary `Prog.bind` cannot implement ensuring after refusal. |
| `EC1-R31` | RATIFIED | Specialize EffHOL's modality to existing `wlp`, with existing `wp ↔ wlp ∧ total`; state Mod-E only with a nonempty prefix and the prefix-produced answer history threaded into the suffix. | No duplicate public modality or table-only suffix rule is admitted. The required `wlp_append` is a new `EC1-T130` obligation derived from shipped `wpAux_append`, not an inherited theorem. |
| `EC1-R32` | PROPOSED | Make `ValueTy` a versioned restriction/extension bridge over `Cas.Schema.El` on the overlapping structural fragment. | Existing `El` remains the value meaning owner where inhabited; its parked/refused arms and new fiber/resource/cause handles remain explicit insufficiencies with separate proof rows. |
| `EC1-R33` | PROPOSED | Store serialization, `A/E/R`, handler-route, observation, and reification metadata in `Alphabet`/`OpDesc` indexed by an existing `Sig.Op`; compose semantic families only with `Sig.sum`. | `Sig` is not replaced or modified for classification, and existing CAS/root/word extension laws remain reusable. |
| `EC1-R34` | RATIFIED | Route CAS refusal and authenticated-computation bridges through the complete existing `RefusalMap` and `Auth.lean` theorem families. | Host-only rows, disjointness, wire uniqueness, Level-0 collision witnesses, security, and correctness are retained instead of weakened restatements. |
| `EC1-R35` | RATIFIED | Make the checked-program checker fail first, with first-error soundness and existential rejection completeness; require duplicate-free checked rows for permutation/canonicalization laws. | An accumulating census is a separate tool, not the checker contract. Raw duplicate keys remain expressible and are rejected; checked rows supply `NodupKeys`. |
| `EC1-R36` | RATIFIED | Make Effect TS cutover one profile of a larger versioned, language-neutral effect protocol. Lean owns admission, relational meaning, and proof; the neutral manifest owns cross-language identities and bytes; TypeScript and later hosts are adapters. | No consumer imports Lean as its runtime interface, no TypeScript surface owns protocol identity, and one profile may cut over without claiming the whole effectful interface closed. Proof status and runtime evidence remain sidecars and never change protocol bytes. |

### Evidence-backed §17 rulings

The operator ruled the eight evidence-backed conditions on 2026-08-31 after
reviewing the dedicated Opus report. Conditions 10, 11, 15, 16, 18, 19, and 20
are closed as representation decisions by `EC1-R25`, `R27`/`R34`, `R15`,
`R35`, `R30`, `R15`, and `R31`. Condition 17 is closed only for
mask-selected classifier overlap by `EC1-R13`; renderer injectivity on
normalized admitted targets remains open. The evidence proves the ruling
boundary, not the proposed Effect Core theorem rows.

Condition 14 remains open deliberately. The neutral protocol must name stable
portable operations, including host-obligation operations, before Lean admits
a selected profile into existing `Sig.Op`. Inside the Lean model, semantic
families still compose through existing `Sig.sum`; the unresolved decision is
the exact admission bridge from neutral operation identity to that family, not
permission to replace `Sig`.

## 5. Provenance basis

Only already pinned local evidence is used as prior-art support here.

| Status | Local source | Permitted use in this packet |
| --- | --- | --- |
| PINNED | `.reference/catalog/PAPERS.md#semantics-carriers`: *Interaction Trees: Representing Recursive and Impure Programs in Coq*, arXiv:1906.00046v2, digest `943dc278978b9d85…` | Finite observations, visible events, recursion/nontermination proof shapes. |
| PINNED | `.reference/catalog/PAPERS.md#semantics-carriers`: POPL version, DOI 10.1145/3371119, digest `4cc833d5d09f520e…` | Same limited role as the preprint; not a carrier decision. |
| PINNED | `.reference/catalog/PAPERS.md#semantics-carriers`: *Choice Trees*, arXiv:2211.06863v1, digest `87cae08d3a3c0156…` | Keeping scheduler/environment choice visible in relational semantics. |
| PINNED | `.reference/catalog/PAPERS.md#semantics-carriers`: *HITrees*, arXiv:2510.14558v1, digest `86389e257dc4b0bd…` | Named first-order bodies for scoped/higher-order operation shapes. |
| PINNED | `.reference/catalog/PAPERS.md#semantics-carriers`: *Modular Denotational Semantics for Effects with Guarded Interaction Trees*, arXiv:2307.08514v2, digest `40d999b3e15d69b8…` | Coherent guarded/finite semantic layers and modular handler reasoning. |
| PINNED | `.reference/catalog/PAPERS.md#semantics-carriers`: *Modular, compositional, and executable formal semantics for LLVM IR*, DOI 10.1145/3473572, digest `592aa955d443d6ac…` | Separate syntax, executable interpreter, relational semantics, and refinement obligations. |
| PINNED | `.reference/catalog/PAPERS.md#translation-validation`: *Translation Validation for an Optimizing Compiler*, digest `335d4a06577b2231…` | Per-run validation as an alternative to trusting a generator. |
| PINNED | `.reference/catalog/PAPERS.md#translation-validation`: *MimIR*, arXiv:2411.07443v2, digest `89abaa4b949554e6…` | Typed intermediate-representation organization only. |
| PINNED | `.reference/catalog/PAPERS.md#type-effect-lineage`: *Do Be Do Be Do*, arXiv:1611.09259v2, digest `9cc06103fd865a49…` | Separating value computation from effect capability requirements. |
| `EC1-PV01` PENDING | EffHOL, arXiv:2506.09458, supplied by the operator | No estate claim uses it until a source lock and receipt are added. Its computation/program/specification separation is advisory only. |
| LOCAL TOOL AUTHORITY | `docs/lab-core/TOOLS.md` and `library/effects/{package.json,tsconfig.json,scripts/patch-toolchain.ts}` | Required TS7 + Effect diagnostic harness shape; diagnostics have no semantic trust contribution. |
| `EC1-PV02` PENDING | `https://github.com/Effect-TS/tsgo`, the published source named by installed `@effect/tsgo@0.38.0` | Resolve the exact successor source/toolchain pin before source-tooling evidence supports a claim. `@effect/language-service` is the configured plugin identity; the standalone language-service repository/package is prior art, not the TS7 execution route. |

The catalog explicitly says these sources do not select an estate carrier or
establish implementation conformance. This packet makes its own proposed
carrier decision and owes its own theorems.

## 6. Ordered proof-bearing slices

Each slice ends in a declaration freeze and its named falsifier battery. No
later slice may weaken an earlier signature to make a proof pass.

**ORGANIZATIONAL PREREQUISITE `O0`.** The packet routing in the local
`AGENTS.md`, the bootstrap rows in `EXISTING-TYPES.md`, the ownership plan in
`ORGANIZATION.md`, the README/spec/domain pointers, and their proposed
generated-facts gates must be reviewed before `EC1-S0` can close. O0 records
organization only. It does not imply that O1–O6 manifests, generators, or gates
already exist, and it contributes no semantic evidence.

O0 also establishes the per-type proof-closure register. Every required type
row must link its constructor, checker, semantics, classifier, lowering, and
red-control edges. Slice completion may cut over one fully closed type row;
the lane cannot claim a full cutover while any required row has an open edge.

| Slice | Proposed deliverable | Entry requirement | Exit obligation |
| --- | --- | --- | --- |
| `EC1-S0` | Grilled contract packet and vocabulary ownership | This pre-grade packet | Ratified scope or explicit rejection; no code |
| `EC1-S1` | Recursive pinned `PublicSurface` census, seven-disposition ledger, `El` value bridge, existing-`Sig.Op`-indexed alphabet metadata, raw identifiers, values, pure-code references, existing-`PProg` block bodies, and closed operation descriptors | `S0` | Module/export/member/overload closure; disposition totality; source-to-alphabet mapping; `El` overlap/insufficiency ledger; `Sig.sum` extension reuse; duplicate-free row premises; no duplicate sequential body; decidable equality/serialization; malformed witnesses banked |
| `EC1-S2` | Raw graph, well-formedness judgment, canonical fail-first diagnostic, checked carrier, erasure | `S1` | Checker soundness, relative completeness, first-error locality; no promise to enumerate every condemning clause |
| `EC1-S3` | `CasAdmissible`/raw-admission plus CAS injection/normal-form-recognition seam before new execution power | `S2`, existing CAS laws, existing-type annotations | Empty/dangling rejection; injected-form recognition and soundness; no semantic projection claim for equivalent non-normal graphs; canonical-identity preservation; reference-handler agreement; complete `RefusalMap` and `Auth.lean` theorem reuse; explicit refusal-word mask |
| `EC1-S4` | Sequential effect blocks around existing `PProg` bodies, calls, returns, typed failure, and direct handler table elaborating to existing `Handler` | `S2` | Preservation/progress; executable/relational one-step agreement; `Handler.sum`/`through` reuse |
| `EC1-S5` | Branch, join, cyclic jump, recursive call | `S4` | CAS/block coherence/uniqueness reuse only for stable non-frontier outcomes; relational/derived-approximation adequacy and truncation coherence; loop unfolding; divergence definition |
| `EC1-S6` | Canonical-overload-derived `A / E / R` projection and the non-concurrent classifier dimensions | `S5`, frozen surface rows | Projection exactness, including result unions, residual errors, and possibly-empty requirements; classifier soundness against observations |
| `EC1-S7` | Named handler provision and higher-order/scoped bodies | `S4` | Direct lookup uniqueness; handler law; scope nesting/frame laws |
| `EC1-S8` | Cause algebra, catch/ensuring exits, resource registration/finalization | `S7` | LIFO and exactly-once release; cause-combination laws |
| `EC1-S9` | Fibers, yield, join, supervision, scheduler policy/state, and ready-fiber decisions | `S8` | Fiber ownership and join laws; deterministic replay from fixed initial scheduler state/policy plus one compatible decision tape |
| `EC1-S10` | Interruption, masks, race, loser cleanup, fairness-labeled liveness | `S9` | Delayed interruption under masks; race cleanup; no safety theorem assumes fairness |
| `EC1-S11` | Foreign effect and pure atoms, receipts, replay | `S6`, `S8` | Registry totality; declared-frame preservation; receipt replay conditional on contract |
| `EC1-S12` | Complete semantic triangle and multidimensional product classifier | `S10`, `S11` | Runner/relation/approximation agreement; per-domain soundness and reduction; no unsupported full-product invariance under observational equality |
| `EC1-S13` | Typed TypeScript target IR and lowering | `S12` | Target typing, `A/E/R` preservation, per-constructor semantic simulation, canonical renderer round trip/injectivity on normalized admitted targets, and explicit `CauseTree -> CauseReasons` quotient for stock rc.112 |
| `EC1-S14` | Renderer/parser validation; exact TypeScript + Effect tsgo JSON diagnostics with file-set equality; code-action fixed points and negative mutations; pinned compiler and host lanes | `S13`, independent pins, frozen public census | Structural source relation plus complete coverage harnesses; gates G3–G6 only to their actual evidence; no stock-runtime full-topology cause claim |

## 7. Claim route

**PROPOSED TERM `EC1-ClaimRoute`.** The work may advance only by the existing
claim ladder:

- G0 pins exact Effect, TypeScript, compiler, engine, and host bytes.
- G1 proves properties of the Lean Semantic Model only.
- G2 traces the model to this grilled contract, including counterexamples.
- G3 admits a named source or generated target subset, selects canonical public
  symbol and overload rows, and proves its bridge.
- G4 compares a pinned Effect build with normalized model observations.
- G5 proves or separately validates compilation from emitted TypeScript to
  JavaScript under a pinned compiler configuration.
- G6 names the engine, host, platform assumptions, and preserved observations.

No theorem name in this packet satisfies any gate. Every theorem is PENDING.

## 8. Packet map

- `README.md` is the staged packet index and current evidence-status summary.
- `AGENTS.md` is the staged lane router and read-order/role boundary.
- `EXISTING-TYPES.md` owns reuse, restriction, bridge, embedding, and
  identity/meaning-owner annotations for existing declarations.
- `CONTRACT-PACKET.md` is the breaker's executable contract: quantifiers,
  falsification equations, frames, decreases, examples, and adversarial cases.
- `ALGEBRA.md` defines the proposed public-surface-to-alphabet boundary,
  carriers, graph operations, direct handlers, operational state, cause
  quotient, relational meaning, and executable/finite adequacy views.
- `CLASSIFICATION.md` defines the independent abstract domains, combination
  rules, concretizations, and soundness obligations.
- `PROOF-DAG.md` freezes the proposed theorem signatures and their dependency
  order for later ratification.
- `REIFICATION-CHECKLIST.md` owns the pinned public-source census and total
  seven-disposition closure contract.
- `ORGANIZATION.md` owns generated manifests, AGENTS/spec gates, continuity,
  and promotion shape without owning semantic declarations.
- `EXHIBITS-REVIEW.md` owns adoption limits for the scratch Lean exhibits;
  `TYPE-CLOSURE.md` owns per-type proof closure and full-cutover eligibility.
- `COUNTEREXAMPLES.md` is the stable negative-witness register;
  `WORKSHOP-RESULTS.md` records exact local probe commands and observations,
  neither replacing a theorem or contract clause.
