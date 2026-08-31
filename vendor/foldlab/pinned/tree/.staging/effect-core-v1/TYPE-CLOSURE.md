# Effect Core v1 — per-type proof-closure and cutover ledger

Status: **PRE-GRADE / PROPOSED**, 2026-08-31

Claim gate: none

Operator condition: full cutover is not eligible until the proof graph for
every required existing, proposed, source, and target type is mechanically
closed. A package-wide source census and a compiling group of favorite
theorems are insufficient.

## 1. What “closed for a type” means

Each `TypeClosureRow` has these edges:

```text
TypeClosureRow = {
  typeId,
  annotationId,
  declarationId,
  authority: existing | proposed | vendored | generated,
  requiredForCutover,

  identity: {
    canonicalName, sourceDigest, versionOwner, duplicateCheck
  },
  formation: {
    constructorsOrGrammar, indices, positivityOrFiniteness, enumeration?
  },
  equalityAndBytes: {
    decidableEquality?, normalization?, codec?, roundTrip?, identityOwner?
  },
  admission: {
    rawCarrier?, wfJudgment?, checker?, sound?, complete?, diagnostics?
  },
  elimination: {
    recursorOrTotalConsumers[], exhaustivenessGate
  },
  semantics: {
    operationalRules[], executableRules[], denotation[], observations[]
  },
  classification: {
    abstractTransfers[], concretization[], soundness[], precision[]
  },
  composition: {
    operations[], laws[], sideConditions[]
  },
  embeddingAndLowering: {
    sources[], targets[], simulations[], reflectionOrQuotient[]
  },
  generation: {
    sourceRows[], emittedRows[], deterministicBytes?, driftGate?
  },
  falsification: {
    counterexampleIds[], positiveFixtures[], negativeFixtures[], mutationIds[]
  },
  assurance: {
    theoremIds[], buildReceipt?, axiomReport?, highestClaimGate?
  },
  dependencies[],
  openEdges[],
  closure: open | conditionallyClosed | closed
}
```

An edge can be explicitly inapplicable, but it cannot be omitted. For example,
a type-only TypeScript helper may have no runtime semantics; its row says
`semantics = inapplicable(typeOnly)` and proves it emits no Core node.

## 2. Closure rules

1. A type is `closed` only when every applicable edge is discharged by a
   named theorem, executable gate, or recorded ruling.
2. `conditionallyClosed` names all external assumptions and the observation
   under which closure holds.
3. A theorem depending on another open type row cannot close its consumer.
4. Mutually recursive types form one declared strongly connected component;
   their formation, induction, and checker closure is proved as a group.
5. A generated type table is closed only when generator totality,
   deterministic bytes, source identity, and drift controls are closed.
6. A vendored type is source-closed at its pin but never thereby semantically
   closed in the project model.
7. Existing types are not re-proved indiscriminately: their row points to the
   exact existing theorem and records only new bridge obligations.
8. A duplicate declaration or identity owner makes both affected rows open.
9. Every active counterexample attacking an edge is named by stable ID from
   `COUNTEREXAMPLES.md`; an amended statement records the premise, restriction,
   quotient, or carrier split that the witness forced.
10. A finite probe closes only its stated bounded edge.
11. Full cutover requires every `requiredForCutover = true` row to be
    `closed`, every dependency target to resolve, and every red control to
    have killed its intended mutant.

## 3. Foundational existing-type rows

| Type group | Existing owner | Inherited closed edges | Open Effect Core edges before cutover |
| --- | --- | --- | --- |
| `Sig`, `Sig.sum` | `Cas.Lang.Sig` | formation and operation-answer indexing | `Alphabet.toSig`; metadata erasure; selected-alphabet/version totality |
| `Prog S A` | `Cas.Lang.Prog` | formation, recursor, monad operations; existing laws named in `Representation`, `SumAlgebra`, `Universal` | graph elaboration/simulation; explicit prohibition on canonical serialization |
| `Handler S M`, `interpret` | `Cas.Lang.Handler` | handler fold, sum, bind preservation | direct-environment elaboration, region restoration, frame and one-shot laws |
| `PIn`, `PLine`, `PProg` | `Cas.Lang.Defun` | existing WF, embedding, runner, envelope, exact CAS bytes/identity owners | graph injection/projection, CAS specialization, no-second-spelling gate |
| `Refusal`, `Refusal.Clause` | `Interp`, `RefusalMap` | six-kind enumeration, payload-forgetting map, host join/completeness | policy for injection into `CauseTree`/target errors; partial-word observation quotient |
| `Status`, CAS `step`/`run` | `Cas.Lang.Interp` | existing operational semantics and CAS receipts | specialization from general machine; frontier correspondence; no-composition boundary retained |
| `WPre`, `WPost`, `wp`, `wlp` | `Cas.Lang.Wp` | CAS logic and existing transformer laws | selected full-core logic or explicit restriction; EffHOL modality relation |
| `Envelope` and projections | `Cas.Lang.Defun` | current executable projections and theorem names | per-domain bridge preserving known gaps, reindexing, H-dependent write limitation |
| `Word`, address/node/value carriers | CAS core/IR modules | existing identity, admission, and word owners | one world-lens embedding and full/quotiented observation relations |

These rows prohibit parallel replacement types named “new Sig,” “serializable
Prog,” “CAS refusal kind,” “CAS status,” or “CAS word.” New data is admitted
only at the general graph, cross-boundary, or classification layer with the
bridge explicit.

## 4. Proposed Semantic Model rows

| Type group | Required closure edges | Key blockers/red controls |
| --- | --- | --- |
| `ValueTy` / indexed `Value` | closed constructors; decidable codes; raw/checked values; total interpretation; codec/normalization where addressable | invalid tag/payload, out-of-range scalar, resource/fiber region forgery |
| `ErrorRow`, `RequirementRow`, `AER` | canonical normalization; equality; union/difference; unique synthesis; exact checked projection | duplicate tags/keys, too-small declared `E/R`, builtin operation wrongly adding `R` |
| `Alphabet`, `OpDesc` | finite enumeration; unique IDs; explicit possibly-empty requirement row; answer/error/cancel/resumption/observation fields; `toSig` | unknown op, duplicate op, many-shot admission, missing direct primitive/foreign handler |
| `PureExpr`, `PureAtom`, `ArgMap` | total evaluation; termination; world independence; substitution/renaming; empty effect footprint | hidden mutation/random/throw/promise, partial evaluator, pure value smuggling resource token |
| `RawProgram`, raw blocks/regions | complete invalid-state carrier; first-order field walk; canonical IDs; dependency graph | function field, dangling ID, alias capture, delegation cycle, second CAS spelling |
| `ProgramWF`, `Diagnostic`, `CheckedProgram` | decidable checker; soundness; completeness; error locality; erase/check round trip; AER synthesis | every breaker F01–F10 plus one mutant per new clause |
| `Block`, `Term`, `Resume`, `Flow` | typed formation with existing `PProg` as each sequential body; explicit captures; alpha/offset normalization; builders; composition laws; one-shot resume | second straight-line body language, duplicated resume, reindexed-dependence defect, implicit handler search, opaque callback |
| `CauseTree E`, rc.112 cause quotient | ordered internal fail/die/interrupt/then/both laws; typed catch; canonical internal order; total lossy reasons quotient | flattening used under full observation, defect inserted into `E`, sequential/parallel topology erased silently |
| `Exit E A` | value/error typing; terminal machine relation; target quotient relation | await/join conflation, CAS refusal silently treated as typed user error |
| `ScopeFrame`, resources, ownership | region WF; atomic registration; LIFO; exactly-once-after-registration; non-escape; diverging-finalizer behavior | catch ignored, ensuring success-only, resource/daemon escape, fabricated cleanup completion |
| `FiberState`, scheduler, interruption | ownership; await/join split; request/await interrupt split; mask pending flag; schedule-enabled rules | join returns Exit, interrupt request waits accidentally, fairness assumed by safety |
| `Configuration`, `Step`, decision tokens | config WF; progress/preservation; one rule per term; explicit choice labels; frame facts | implicit host nondeterminism, stuck checked state, unrelated world mutation |
| `RunPrefix`, `Frontier`, `FinApprox`, denotation judgment | fuel runner; frontier not refusal; finite-support theorem; truncation; executable/relational agreement; coherent-prefix relation; no public `Behavior` carrier | `Finite (FinApprox ...)`, global `denotes_unique`, answer enumeration, fuel reported as error |
| each D0–D14 domain / `ClassProduct` | carrier/order/concretization; constructor transfers; SCC solver; per-domain soundness; precision marker; reduction preservation | may=must, dataflow raw union, frame union treated as semantics, operation/world/order conflation |
| `ForeignEffect` / registry rows | serializable request/answer/error/service schemas; direct model/handler; frame; receipt; replay; host pin | arbitrary closure accepted, unknown frame marked empty, receipt replayed against wrong world |
| `CasEmbedding` | admission from `CheckedPProg` or successful `Option`/`Except`; projection left inverse on that image; run/denotation/classifier agreement; canonical identity | total injection from arbitrary raw `PProg`, alternative CAS bytes, envelope strengthened past known gaps, refusal word hidden unintentionally |

Every row expands into constructor-level obligations. “Scope closed” cannot
stand for acquire, register, release, ensure, nested scope, mask, child, and
race cleanup unless each rule has an entry or explicit inapplicability.

## 5. Public source and target type rows

| Type group | Required closure edges | Cutover condition |
| --- | --- | --- |
| `SurfaceRowKey` / public exposure graph | recursive exports-map closure; symbol/member/overload identity; dependency closure; total row key universe | no unclassified, duplicate, missing, unresolved, or internal-public row |
| `RawTsType` | exhaustive closed grammar for every selected public signature shape plus explicit external/unsupported boundary | no opaque signature strings consumed by Lean generation |
| normalized `TypeExpr` and AER elaborator | total normalize/elaborate/refuse; quantifier scope; union, never, Exclude, conditional/infer, callbacks, carriers | per-overload index transform reproduced or profile refused |
| dispositions and admission profiles | one conservative row disposition; profile-specific mapping/family roles/transfers/observations/obligations | census closure and semantic proof completion reported separately |
| `TsCore` | typed closed target grammar; deterministic lowering/rendering; target semantics; constructor simulation | every emitted form structurally decodes and has a source theorem edge |
| `AcceptedTs` | bytes -> closed target grammar -> structural decode -> raw graph -> checker -> checked graph; independent TS/LSP evidence | clean diagnostics alone never close the row |
| rc.112 `Effect`, `Cause`, `Exit`, `Fiber`, `Layer`, Channel family, Tx family | canonical public symbol/profile IDs and exact bridge or separate-calculus row | richer project semantics name every lossy quotient or project-owned replacement |
| TypeScript/`@effect/tsgo` tool records | exact pins/config/catalog, expected/reported file-set equality, per-file v4 detection, red controls and action idempotence | no 42/43-file or plugin-disabled clean run can pass |

## 6. Nondeterminism closure subgraph

Nondeterminism is not closed by a single scheduler theorem. The following
edges must all close:

```text
DecisionSource enumeration
  -> typed Decision token for executable runner
  -> labeled relational Step branch
  -> symbolic Frontier for unanswered/infinite choices
  -> relational Runs/Denotes judgment
  -> derived FinApprox branch/truncation
  -> approximation soundness/completeness/coherence theorems
  -> may/must ClassProduct transfers
  -> deterministicGiven classification
  -> fixed-DecisionTape replay theorem (scheduler selections included)
  -> fairness-parameterized liveness theorem
  -> target policy and G4 observation relation
```

Required counterexamples include branch-only effects, unfair scheduler,
race-tie public-order difference, infinite answer space, interrupted masked
finalizer, and two schedules with equal result but different lifecycle trace.
The deterministic CAS exhibit closes only the specialization edge after the
general subgraph exists.

## 7. Refusal closure subgraph

```text
RawProgram diagnostic ----------> no CheckedProgram
public profile refusal ---------> census row retained, profile not admitted
Cas.Lang.Refusal ---------------> existing Refusal.Clause / RefusalMap
typed failure ------------------> CauseTree.fail E
defect/interruption ------------> CauseTree.die / interrupt
fuel/external/schedule frontier -> live FinApprox frontier
TS/LSP/decoder rejection -------> EvidencePlane / no AcceptedTs
```

Proof obligations prevent arrows between the wrong rows. In particular:

- frontier never maps to `Refusal.failed`;
- CAS clauses are not copied into a new refusal-kind sum;
- TypeScript diagnostics never become semantic causes;
- typed catches cannot catch CAS/tooling admission unless a selected bridge
  deliberately exposes a typed error; and
- stock rc.112 cause flattening is a quotient, not internal equality.

## 8. Mechanical cutover predicate

The proposed generated check is:

```text
FullCutoverEligible manifest rows :=
  manifest.packetFrozen
  && rows.all fun row =>
       (!row.requiredForCutover) || row.closure == closed
  && noDuplicateMeaningOwners rows
  && noDuplicateIdentityOwners rows
  && dependencyGraphClosed rows
  && declarationSnapshotMatches rows
  && everyRedControlObserved rows
  && counterexampleRegisterClosed rows
  && publicSurfaceZeroCounters
  && effectLspCoverageExact
  && axiomPolicySatisfied rows
```

The predicate returns a structured refusal listing every open edge. It is not
a Boolean-only CI message. There is no manual override named “substantially
complete.” An operator may version the cutover scope, but that changes the
manifest and reopens review rather than suppressing rows.

## 9. Current closure state

At this staged packet:

- existing declaration identities and many inherited CAS theorems are
  observed;
- two scratch exhibits compile and expose useful bridge facts/counterexamples;
- the central counterexample register distinguishes verified, reported, red,
  and owed evidence, but its generated zero-counter projection does not exist;
- the packet's types and theorem graph remain proposed;
- no generated type-closure table or cutover predicate exists;
- the public Effect universe has not yet been recursively emitted into rows;
- no general nondeterministic Semantic Model has been kernel checked; and
- no full cutover is eligible.

This state is intentional and explicit. The next accepted implementation
slice begins by generating row skeletons and making the open edges executable,
not by declaring the graph closed.
