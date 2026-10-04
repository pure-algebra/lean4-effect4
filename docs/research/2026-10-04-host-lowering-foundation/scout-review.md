# Foundation packet scout review

Status: independently scouted and refined plan; feature implementation has not started.
Base: `faad3e9e`.

## Question

Does the packet define usable implementation slices without assuming the host or target connection it promises?
Does the proof tooling expose their obligations before implementation starts?

## What was read or run

Three independent scouts review the actual packet against the base.
Their scopes cover proof tooling and requirements, host typing and session commands, and the OCaml target boundary.
The root reviewer checks their findings against source and refines the packet.
Each scout rereads the revised sections.

Source inspection covers checking, registration, session commands, reference agreement, semantics reporting, the proof ledger, target roots, and artifact receipts.
The earlier DI-57 probes remain historical evidence on their recorded base.
The current review runs isolated Python and Make fixtures, with a fake Lake driver.
It starts no Lean build, production generator, OCaml build, or runtime execution.

## Findings and dispositions

| Finding | Source | Disposition |
| --- | --- | --- |
| The semantics report checks individual statements, not authored prerequisite edges | `Claim`, `tools/Tools/SemanticsRegistry.lean`; `readGoal`, `tools/ProofGraph/Ledger.lean`; `claimStatus`, `tools/Tools/Semantics.lean` | P0a extends the existing claim record and report; graph validity stays separate from proof status. |
| Independent test-root changes and missing report files escape the semantics marker inputs | Semantics rules, `Makefile` | Isolated fixtures reproduce both defects; P0a repairs and tests them before feature dispatch. |
| Public claims must retire temporary goals after exact proof comparison | `AGENTS.md`; `#obligation_proved`, `src/Effect4/Laws/Auto/Obligations.lean` | P0a checks the lifecycle; receipts retain the comparison evidence. |
| Global environment typing would depend on the reply typing it helps prove | `PointTyped`, `src/Effect4/Laws/Program/Typed/Admission.lean` | F3 proves local transport; F8 establishes the strengthened invariant by prefix induction. |
| Existing typed replay uses the empty table and constrains tails only after sufficient receipts | `DecisionKeeps`, `AdmittedTape`, `src/Effect4/Laws/Program/Typed/Assembly.lean`; `AdmittedReplay`, `src/Effect4/Laws/Machine/Lift.lean` | F8a adds table-aware one-decision typing with an actual world, both budgets, and both receipt outcomes. |
| Prepared-result membership does not alone type the recorded completion | `preflight_success_prepared_fits`, `src/Effect4/Laws/Api/HostSession.lean`; `AnswerOk`, `Assembly.lean` | F5 proves the payload/state bridge and `CompletionStrong`; F8 derives the answer premise at each actual prefix. |
| Equal final observations do not recover guards or saved stacks | `stepAgrees`, `src/Effect4/Laws/Program/Simulation/Drive.lean` | F6 retains the stronger machine relation and sufficiency receipts. |
| Parallel reference work needs landed registration definitions | `CodeMeans.asyncForeign`, `src/Effect4/Laws/Program/DenoteR.lean` | P2a lands the shared definitions and direct consumers before P2b and P3 branch. |
| Target roots, trust coverage, and executable proof equations need separate checks | `registry`, `tools/Tools/SemanticsRegistry.lean`; `ofExpr`, `tools/Conform/Effect4/LcnfMl.lean` | P0a checks extraction coverage; P6a freezes a feasible actual target relation. |
| The current target roots omit keyed session entry points | `ocaml/gen/roots.json` | P6a inventories the actual closure; a refusal leaves artifact implementation open. |
| Target receipts omit relevant interface, extern, build, and closure files | `manifest`, `scripts/lib/conform_report.py` | Isolated fixtures reproduce the omissions; P6a declares exact required input and output sets. |
| A passing Conform report may retain open obligations | `Conform.Obligation`, `tools/Conform/Core/Obligation.lean` | Certificate consumers require closed obligations and an independently derived subject set. |
| One production rule cannot establish target replay | `builtin?`, `src/OCaml5/Lcnf/Translate.lean`; the selected artifact contract | P6b proves one bounded rule; P7 leaves the remaining F9/F11 connections explicit. |

## Review outcome

The final scout passes identify no remaining sequencing blocker in the plan after their stated refinements.
Their last safeguards are incorporated: explicit answer membership, full graph validation, target-root ownership, artifact refresh, and fixed completion criteria.
This outcome releases P0a implementation and review, not the later feature proofs.
P0a's actual changes and command results still require independent review before feature dispatch.

## Verification

The retained [fixture](check-tooling-fixtures.py) reads the actual semantics Make rule and production Conform manifest function.
It exercises representative files in temporary directories and deletes only those temporary fixtures.
The [literal output](tooling-fixtures.txt) records its results and the Make rule hash.
These are bounded tooling checks, not a successful production build or a semantic proof.

The packet passes strict controlled-English checking and local reference checks.
The handoff receipt records the exact verification commands.

## Limits

A15–A17 remain source-derived fuel candidates until P0b checks them in Lean.
No proposed theorem in this packet has a new proof.
No production source, authority document, or generated output changes in this planning task.
The overnight monitor remains unconfigured until the implementation session starts.
