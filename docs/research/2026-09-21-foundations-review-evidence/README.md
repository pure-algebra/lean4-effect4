# Checked controls for the foundations review

The five probe files compile with warnings treated as errors. Every named research theorem
has an axiom report within `[propext, Quot.sound]`; the runner checks both report coverage
and the ceiling. The production dependencies passed the focused build (275 jobs). These
results support the [review findings](../2026-09-21-foundations-monotonicity-and-refinement-review.md)
and the [amended implementation brief](../2026-09-21-codex-brief-foundations-slices-3-6.md).

Source base: `641a0feabe8ff7c3899396cd2144380d6d8cf53c`. Date: 2026-09-21.
Production and generated files were unchanged. This work does not implement slices 3–6,
close their production obligations, establish reachable-state preservation, or certify an
OCaml/C/TypeScript backend. No whole-tree `make check` or native differential was run for
this review. Earlier implementation receipts remain historical evidence.

## Reproduce

From the repository root:

```sh
python3 docs/research/2026-09-21-foundations-review-evidence/run-probes.py
```

The runner builds the three direct dependency roots and executes the five probes and statement packet sequentially.
`--skip-build` uses a narrow build already completed on this same checkout. `results.json`
records each command and exit code, declaration kind, axiom-audit result and source hash. `build.log`
retains the separate completed build used for this run. Nothing writes to generated outputs,
`Test/All.lean` or the production obligation ledger.

## What each file establishes

| File | Checked statements and limits |
| --- | --- |
| `WorldReplayProbe.lean` | `leHost` does not imply global WF preservation; active Θ coverage does not imply allocator freshness; token bound does; same-length spelling rename fails while existing universal lookup transport applies; actual reference answer preparation preserves stores; finite command-fuel-30 replays show matching raw answers can mistype a yield, with normal/stale/missing controls |
| `ProtocolAdmissionProbe.lean` | Certificates can be higher-order at universe zero; Ty has open variables; impossible posts allow vacuous protocol typing; successful checker calls do not prove path or runtime-environment agreement; coarse leaves admit forged handles and `badShapeExit`; Boolean allocation/read is valid machine behavior outside legacy HeapNat |
| `StackProbe.lean` | Landed resume contract rejects an error-removing catch; evaluator's normal and interrupt-skip branches; existing interrupt provenance does not exclude the arbitrary bad combination; generic protocol typing does not type a discarded marker continuation's payload |
| `MonotonicityBridgeProbe.lean` | Universal local endpoint transport, selected-invariant transfer through `Projects`, indexed lookup transfer through `LawfulArena`; fresh axiom inspection of existing arena, kernel and completion-data connectors |
| `AnswerShapeProbe.lean` | Actual dependent answer types; raw scoped-exit dispatch gives `badShapeExit`; environment-derived constructor inventory (31 SyncOp, 40 FiberOp), not an answer-adequacy gate |

Arbitrary-world and saved-frame witnesses are not claims of source reachability. A successful
finite replay is not a universal preservation proof. Conditional representation theorems
still require actual implementation instances. The report names those distinctions wherever
the controls are used.

## Architecture statements: four open, zero proved

`ArchitectureStatements.lean` is the owner's requested declaration-first design packet.
It compiles using existing theorem-shaped `ProofGraph.Obligation` declarations and
`#proof_wanted` markers. Its actual gate reports:

```text
FoundationsArchitectureStatements: 4 open, 0 proved, 4 total; ceiling 4
```

| Open declaration | Proposed production owner | Meaning |
| --- | --- | --- |
| `completion_transport` | `Laws/Program/Typed/Validity.lean` | Shape/column completion transport from Ρ persistence and spelling `Extends` |
| `indexed_ref_step_preserves` | `Laws/Machine/RefKernel.lean` | Actual kernel row preserves a per-index heap predicate, answer, length and untouched lookups |
| `projects_compose` | `Laws/Machine/Refinement.lean` | Compose exact operation projections while retaining both validity predicates |
| `projects_induces_refines` | `Laws/Machine/Refinement.lean` | Relational step/frontier interface obtained from an exact valid-state projection |

The namespace is `FoundationsArchitectureStatements`. The log prints the full propositions.
An axiom report on an obligation wrapper does **not** prove its enclosed proposition. The
runner labels these four separately from the 71 proved research statements in the five
probe files. Promotion into production still needs its exact scoped landing and proof fills;
no marker was removed and no runtime representation was changed.

## Retained failed attempts

`*.initial-error.log`, `*.second-error.log` and `*.draft-error.log` record draft elaboration
errors (namespace qualification, missing build artifact, record fields and decidability
unfolding). They are **not counterexamples or axiom evidence**. Lean recovery may print
`sorryAx` for such failed declarations; only the final zero-exit logs are admitted evidence.
The checked negative propositions in the final sources are the mathematical findings.

## Persistence and scope

Changed tracked documents: the slices 3–6 brief and `docs/STATE.md`. Added local research
artifacts: the findings note and this evidence directory. These are saved in the repository;
`docs/research/` is ignored by Git, so a later landing must force-add the explicit note and
evidence paths. This review makes no commit and no push, and does not alter the coordinator's
decision register. The input theoretical review remains unchanged.

Landing note: input reports and two historical error logs have trailing whitespace normalized. Their failed elaborations remain non-evidence; the checked Lean source files and recorded source hashes are unchanged.
