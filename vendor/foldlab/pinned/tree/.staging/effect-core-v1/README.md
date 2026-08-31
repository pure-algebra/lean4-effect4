# Effect Core v1 — staged packet

Status: **PRE-GRADE / PROPOSED**, 2026-08-31

This directory is the working packet for a closed-alphabet, fully reified
Effect Core whose meaning is modeled in Lean and whose selected TypeScript
target is generated and checked independently. It organizes the work; it does
not claim that the core, its denotation, or the generated target has already
been completed or promoted.

## Start here

Read the nearest [`AGENTS.md`](AGENTS.md), then use only the document that owns
the current question:

| Need | Owner |
| --- | --- |
| scope, frozen premises, slices, literature roles | [`PLAN.md`](PLAN.md) |
| existing Lean and Effect declarations; reuse/bridge decisions | [`EXISTING-TYPES.md`](EXISTING-TYPES.md) |
| proposed syntax, handler algebra, machine, denotation, target relation | [`ALGEBRA.md`](ALGEBRA.md) |
| exact contract clauses and adversarial batteries | [`CONTRACT-PACKET.md`](CONTRACT-PACKET.md) |
| denotational classification dimensions and transfer laws | [`CLASSIFICATION.md`](CLASSIFICATION.md) |
| declaration and theorem dependency graph | [`PROOF-DAG.md`](PROOF-DAG.md) |
| mechanically exhaustive vendored Effect public-surface plan | [`REIFICATION-CHECKLIST.md`](REIFICATION-CHECKLIST.md) |
| applicability of the staged Lean exhibits | [`EXHIBITS-REVIEW.md`](EXHIBITS-REVIEW.md) |
| every active counterexample and negative-control boundary | [`COUNTEREXAMPLES.md`](COUNTEREXAMPLES.md) |
| per-type proof closure and cutover refusal | [`TYPE-CLOSURE.md`](TYPE-CLOSURE.md) |
| AGENTS layout, generated facts, drift gates, resume protocol | [`ORGANIZATION.md`](ORGANIZATION.md) |
| exact local commands and observations | [`WORKSHOP-RESULTS.md`](WORKSHOP-RESULTS.md) |

The independent reports are evidence inputs, not packet authority:

- [`effect-core coordination and incoming-lane record`](../agent-reports/2026-08-31-effect-core-coordination.md)
- [`effect-core-local-anchors`](../agent-reports/2026-08-31-effect-core-local-anchors.md)
- [`effect-core-classification-anchors`](../agent-reports/2026-08-31-effect-core-classification-anchors.md)
- [`effect-core-provenance`](../agent-reports/2026-08-31-effect-core-provenance.md)
- [`effect-core nondeterminism witness`](../agent-reports/2026-08-31-effect-core-nondeterminism.md)
- [`effect-core ensuring repair`](../agent-reports/2026-08-31-effect-core-ensuring.md)
- [`effect-core §17 evidence rulings`](../agent-reports/2026-08-31-effect-core-s17-rulings.md)

## Operator-set representation decisions

The packet is being reconciled to these constraints:

1. A graph block's sequential body is the existing `PProg`; no second
   straight-line program carrier is introduced.
2. Scoped child bodies are `BlockId` data. Existing `Handler` remains the
   carrier, `Handler.sum` combines same-target signature families, and
   `Handler.through`/`interpret_through` apply only to a genuine intermediate
   `Prog T` tower. Scoped interpretation targets its adequate machine directly;
   there is no `HHandler` type.
3. Full-core meaning is relational over typed decisions, including scheduler
   selections and external answers. Scheduler policy/state lives in the initial
   configuration; fixing that configuration and one complete compatible
   decision tape yields deterministic replay. The deterministic CAS graph
   exhibit does not imply global uniqueness.
4. There is no public `Behavior` program carrier. Finite approximations are
   observations of runs, and coherence is a theorem.
5. The compositional coherence face is `interpretRef`/big step. Existing
   `run_has_no_composition_law` forbids a fixed-fuel bind law.
6. EffHOL's modality specializes to existing `wlp`; existing `wp` adds
   totality.
7. Fuel exhaustion and unanswered external/scheduler choices are live
   frontiers, not `Refusal`, typed error, or cause.
8. Existing `Refusal`, `Refusal.Clause`, `RefusalMap`, `Sig`, `Prog`, `Handler`,
   `PProg`, `wp`, `wlp`, and CAS word/observation declarations remain the
   canonical owners of their current meanings.
9. Every required type must have a mechanically closed proof graph before full
   cutover. There is no “substantially complete” override.
10. The protocol and profile language covers the larger effectful interface; it
    is not exclusive to operations whose semantics are implemented in Lean.
    Before the alphabet freezes, every operation profile distinguishes a
    Lean-modeled operation from a first-order host obligation. Registry
    population and replay machinery may arrive later, but the language-neutral
    profile arm is a foundation concern. This is an operator-set representation
    decision, not evidence that any foreign implementation is sound.

## Evidence-backed §17 freeze rulings

The §17 evidence pass rules only the following eight conditions. Conditions
1–9 and 12–14 remain open design questions; condition 17 is only partly closed.

| Condition | Ruled boundary |
| --- | --- |
| 10 — denotation | Full-core meaning is relational; no choice-free denotation function or global uniqueness theorem is admissible. Uniqueness is relational under one fixed compatible tape, in an ask-free subfragment proved free of every other decision source, or for the stable non-frontier CAS/block specialization. |
| 11 — refusal and observations | Reuse `Refusal.Clause`/`RefusalMap`; envelope facts do not determine exact errors or handler-dependent write addresses; refusal-side word erasure is an explicit `ObsEq` quotient. |
| 15 — CAS ingress | Raw `PProg` ingress is partial and meaning preservation is stated only on `CasAdmissible`; an arbitrary input-ignoring function is outside the counterexample's force. |
| 16 — checking and normalization | Checking is first-error sound plus existentially rejection-complete. A per-clause diagnostic set is a separate census. Row normalization requires `NodupKeys` or a validity door that supplies it. |
| 17 — classification | Whole-product invariance under `SemEq` is rejected in favor of concretization soundness or mask-selected overlap. Renderer injectivity remains open. |
| 18 — scoped target | Existing `Handler` and `BlockId` children remain. `ReaderT Env (Prog CasSig)` is prohibited for catch/finalization; `StateT Word (Except Refusal)` repairs catch but not ensuring. The common information contract is that post-body state survives failure; `ExceptT Refusal (StateT Word Id)` is the minimum exhibited CAS witness. |
| 19 — `toPProg` | `toPProg` is a sound recognizer for one literal `CasImage` normal form, not a semantic projection. A broader projection still owes a canonical domain or semantic quotient. |
| 20 — EffHOL sequencing | The modality is existing `wlp`; (Mod-E) requires a nonempty prefix and threaded answer history. `wlp_append` is a new obligation (`EC1-T130`), not an inherited estate theorem; stable uniqueness excludes frontier labels. |

## Current executable evidence

The following checks have been rerun locally in this working tree:

| Check | Result | Claim boundary |
| --- | --- | --- |
| `lake env lean ../../.staging/effect-core-v1/workshop/EffectCoreProbe.lean` from `library/cas` | exit 0; five theorem receipts; `propext`/`Quot.sound` ceiling where reported | workshop definitions only, local G1 ceiling |
| `lake env lean ../../.staging/effect-core-v1/workshop/exhibits.lean` | exit 0; 17 theorem receipts; no `sorryAx` or `Classical.choice` | deterministic CAS/block specialization, not full-core semantics |
| `lake env lean ../../.staging/effect-core-v1/breaker-exhibits.lean` | exit 0; 40 theorem receipts; `propext`/`Quot.sound` ceiling | adversarial results against the scratch exhibits, including the inadequate catch target and conditional `wlp` composition |
| `lake env lean ../../.staging/effect-core-v1/workshop/counterexamples/LocalAnchors.lean` | exit 0; seven theorem receipts; explicit `Classical.choice` only in the row-normalization pair | four packet/DAG contradictions and their narrowed forms |
| `lake env lean ../../.staging/effect-core-v1/workshop/counterexamples/FixedFuel.lean` | exit 0; exact inherited boundary receipts: `[propext, Quot.sound]` and `[propext]` | supports `EC1-CE002`; introduces no declaration |
| `lake env lean ../../.staging/effect-core-v1/workshop/counterexamples/Nondeterminism.lean` | exit 0; 29 receipts; `[propext]` ceiling, 12 axiom-free, no `Quot.sound` or `Classical.choice` | discharges `EC1-CE042` for direct-handler answers; does not model scheduler fairness, external frontiers, interruption, or replay selection |
| `lake env lean ../../.staging/effect-core-v1/workshop/counterexamples/EnsuringRepair.lean` | exit 0; 44 receipts; `propext`/`Quot.sound` ceiling | proves the state-outside-error repair for the exhibited one-level scoped carrier; not nested or multi-block scoped control |
| `lake env lean ../../.staging/agent-reports/2026-08-31-effect-core-classification-anchors.lean` | exit 0; 11 receipts | concrete counterexamples and existing-classifier anchors only |
| `bun .staging/effect-core-v1/workshop/effect-surface-probe.ts --summary` | exit 0; 392 exports-resolved code entries, 4,613 canonical stable coordinates, zero reported duplicate/missing-pair/type errors | pinned package census instrument, not semantic closure |
| `bun .staging/effect-core-v1/workshop/tsgo/run-probes.ts` | exit 0; exact pins and direct declaration resolution verified; ignored bridge absent; exact one-file coverage; positive clean; three mutants rejected by their exact diagnostics | Effect TS7 source-hygiene evidence only |
| `effect-tsgo diagnostics` over `library/effects/tsconfig.json` | exit 0; 43/43 files detected and supported as Effect v4; zero errors, warnings, or messages | current library-wide language-service baseline, not generated-code denotational evidence |

The breaker and local-anchor sources are accepted only as pre-grade, local
kernel evidence. Their exact counterexamples and the restrictions they force
are indexed in [`COUNTEREXAMPLES.md`](COUNTEREXAMPLES.md); they do not promote
the replacement model or close a proof-DAG row.

## Findings already forced into the design

- The old runtime-bank walk is not a complete public-package census; recursive
  exports-map enumeration found public MultipartParser entries absent from it.
- Dataflow sequence must reindex the right operand; neither union nor append is
  correct, and closure is not componentwise homomorphic.
- Operation occurrence, world change, and temporal order are separate
  dimensions.
- `PProg.envelope` does not synthesize exact errors or write addresses.
- CAS observational equality deliberately excludes the partial word on a
  refusing branch.
- A full reification grade is decided from finite authored alphabet/profile
  metadata and discharged by theorems; it is not inferred from an
  undecidable semantic predicate over all runs.
- Four proof-DAG statements require amendment: duplicate-free row
  normalization, fail-fast diagnostic completeness, classifier invariance,
  and total injection from arbitrary raw `PProg`.
- `EC1-CE042` now kernel-refutes a choice-free denotation function for the
  direct-handler-answer fragment. This strengthens the relational-semantics
  boundary without supplying scheduler fairness or external-frontier proofs.
- `EC1-CE045` forces state outside error for finalization: the catch-adequate
  `StateT Word (Except Refusal)` target loses the refusal-side word and cannot
  observe a finalizer there; `ExceptT Refusal (StateT Word Id)` retains it.

The exact witnesses and evidence states are centralized in
[`COUNTEREXAMPLES.md`](COUNTEREXAMPLES.md); replacement statements belong in
[`PROOF-DAG.md`](PROOF-DAG.md), not in this status page.

## Current limits

- No Effect Core declaration is promoted into `formal/` or `library/`.
- The proposed general machine, relational denotation, classifier product, and
  generated TypeScript simulation remain unproved.
- The full recursive public surface has not been emitted into canonical
  profile rows; the workshop census is a measured starting point.
- The generated packet, annotation, obligation, counterexample, and type-closure
  manifests described by [`ORGANIZATION.md`](ORGANIZATION.md) do not exist yet.
- EffHOL and Effect TS7 source-repository pins remain pending in the estate's
  provenance machinery; the local package versions and PDF digest do not
  silently promote those rows.
- No type is approved for full cutover by this packet.

## Current implementation boundary and next slice

B0 (clean packet baseline) and B1 (file stubs only) are present. The next
bounded slice is B2, the broad ownership sweep:

1. reconcile every required existing/proposed/source/target type with one
   meaning owner, byte owner, disposition, and proof-closure row;
2. sweep every operation family and neutral profile row, leaving condition 14's
   portable-identity-to-`Sig.Op` admission bridge explicitly open;
3. join every active counterexample to the theorem/type edge it constrains;
4. record missing generator, checker, adapter, and red-control rows without
   creating placeholder output or semantic declarations; and
5. freeze the resulting signature/obligation snapshot before B3 begins.

B2 does not generate public-surface rows, implement the raw checker, or close a
type. Those are later B3/B4 acts after the breadth sweep is complete. This
remains a pre-grade packet and scaffold, not a cutover branch.
