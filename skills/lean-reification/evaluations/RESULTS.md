# Behavioral evaluation results

Evaluation date: 2026-09-02 UTC. All 32 recorded criteria were met across six
documentation exercises. This result concerns the decisions and work products
below. It is not a reliability estimate, a Lean proof, or evidence that any
program generated using these skills is correct.

## Method and preserved inputs

Three independent agents received raw scenarios and the relevant skills in
fresh contexts, without this task's conversation. They were asked to complete
the work, not critique or repeat the skill instructions. Each agent handled
two cases; cases within the same agent did share its evaluation context.
The [scoring record](SCORING.md) was written before dispatch and explicitly
withheld from the evaluating agents. Their work products list the files they
consulted and report no blocking workflow ambiguity.

The author compared the actual responses against each criterion. This was
human-readable assessment by the authoring agent, not a second independent
grader or a blinded comparison against an unskilled baseline. No production
code, Lean commands, host programs, or external proof artifacts were executed
by these trials. The cases explicitly authorize documentation only.

[The input manifest](inputs.json) preserves SHA-256 values for the original
40 source-pack files, including all seven skills, references, cases, and
scoring criteria. Its paths are relative to the source `skills/` directory.
Every listed file still matches those bytes except `references/sources.md`,
which had one trailing blank line removed during commit preparation. The
manifest retains its original evaluation hash and records the packaged hash
separately; all other bytes are unchanged. No instructional correction was
needed after the trials. The report, manifest copy, and response copies were
added after evaluation. The six responses below are preserved without editing.

| Agent | Assigned cases | Original work products |
| --- | --- | --- |
| `reification_eval_models` | [01: durable workflow](cases/01-durable-workflow.md), [02: sequencing and cleanup](cases/02-sequencing-and-cleanup.md) | [Workflow handoff](outputs/01-durable-workflow.md), [model review](outputs/02-sequencing-and-cleanup.md) |
| `reification_eval_audit` | [03: release claim](cases/03-release-claim.md), [04: proof and witness](cases/04-proof-and-witness.md) | [Release review](outputs/03-release-claim.md), [proof handoff](outputs/04-proof-and-witness.md) |
| `reification_eval_target` | [05: generated predicate](cases/05-generated-predicate.md), [06: small scope](cases/06-small-scope-control.md) | [Generation plan](outputs/05-generated-predicate.md), [completion verdicts](outputs/06-small-scope-control.md) |

Absolute workspace paths in the preserved responses identify the files used
during these trials. The skills themselves use sibling-relative links and
live project discovery. The responses' proposed obligations are exercise
outputs, not new requirements imposed on the real Effect4 repository.

## Case 01: useful formation without inventing a proof

Evidence: [workflow handoff](outputs/01-durable-workflow.md), especially
“Contract and ownership,” “The smallest admitted model,” and “Connections
still required.”

| Recorded criterion | Result | Observed decision |
| --- | --- | --- |
| Produce a useful handoff without asking permission to start | Met | Delivers a concrete restricted-profile design and open choices; no implementation or further authorization is required to deliver it. |
| Separate durable data from the existing proof carrier | Met | Uses finite code blocks and capture data, retains `Program`, and identifies named foreign calls as a separate boundary. |
| Do not infer finite size from induction | Met | Gives infinite natural-answer branching and unbounded branch-depth examples, and distinguishes cyclic finite documents from a well-founded carrier. |
| Keep callback meaning explicit and preserve failure state | Met | Separates snapshot and live-cell captures; cleanup receives the state left by a failing body. |
| Name the required connections without claiming proofs | Met | Records D1–D7 as open, including admission, source interpretation, recursion, codec, runner, and host behavior. |

## Case 02: find both sequencing defects and both cleanup defects

Evidence: [model review](outputs/02-sequencing-and-cleanup.md), especially
the C02-SEQ and C02-STATE witness tables and “What can be kept and what needs
a local proof.”

| Recorded criterion | Result | Observed decision |
| --- | --- | --- |
| Reject the unconditional fresh-history equation | Met | Shows the proposed nesting true while actual composition violates the postcondition; even the desired implication fails. |
| Expose empty-prefix vacuity | Met | C02-SEQ-01 uses an empty prefix, `emit 9`, and a postcondition requiring 4. This is the same distinguishing case as the criterion with 4 and 9 exchanged. |
| Expose reset history despite a nonempty prefix | Met | C02-SEQ-02 uses `emit 9` followed by `use 0`; restarting refuses, while concatenation returns the forbidden 9. |
| Reuse the existing logic and retain the theorem premises | Met | Keeps the nonempty history-or-prefix premise, full produced history, and existing predicates; the missing specialization remains a local obligation. |
| Distinguish skipped cleanup from discarded failure state | Met | Shows both collapsed errors needing different states 6 and 9, and short-circuiting bind skipping cleanup even after state retention is fixed. |
| Require adequate retained state and an exit-aware finalizer | Met | Proposes state on both exits and cleanup from that state; catch support alone does not establish either requirement. |

## Case 03: reject unsupported release claims for the right reasons

Evidence: [release review](outputs/03-release-claim.md), “Supported release
wording,” the connection table, and numbered findings 1–7.

| Recorded criterion | Result | Observed decision |
| --- | --- | --- |
| Keep only the supplied one-way theorem and finite host observations | Met | Supported wording names source-to-target inclusion and 60 selected runs; rejects trace equivalence and universal completion. |
| Exhibit the extra target behavior and missing direction | Met | Finding 1 identifies `read, fail` as target-permitted and source-forbidden, and requires the reverse trace inclusion. |
| Separate scheduling assumptions from one-scheduler observations | Met | Finding 2 identifies allowed starvation and separately names fairness, environment, and computation-progress obligations. |
| Identify circular coverage, skipped scanner input, and wrong-detector rejection | Met | Findings 3, 5, and 6 distinguish unexamined input, prerequisite build failure, and shared recursive-walk omissions. |
| Keep the choice exception exact and legitimate reasoning permitted | Met | Finding 4 rejects a module-wide expansion of a named renderer exception, leaves the uninspected theorem's actual dependencies unverified, and retains permitted `propext` and `Quot.sound`. |
| Do not invent fresh checks or repairs | Met | The verification record explicitly limits its result to supplied facts and paper reasoning. |

## Case 04: preserve a frozen contract and separate existence from execution

Evidence: [proof handoff](outputs/04-proof-and-witness.md), “Decisive evidence
against the frozen theorem,” “What fits inside the fence,” and upstream
handoffs A and B.

| Recorded criterion | Result | Observed decision |
| --- | --- | --- |
| Refute determinism with compatible complete tapes | Met | The admitted program returns 2 on `[false]` and 3 on `[true]` from the same initial state. |
| Preserve the statement and checker; reject an unproved axiom | Met | Explains why proof-body repair cannot solve the false obligation and proposes an explicit fixed-tape contract amendment. |
| Require a computational witness rather than arbitrary existential elimination | Met | Requests an actual program value with a certificate, or a computational derivation translation; distinguishes Lean's existential proof from executable data. |
| Reuse canonical syntax and separate construction, saving, and execution | Met | Keeps the supplied first-order representation and lists separate obligations for a witness, its saved form, and its host execution. |
| Avoid a universal prohibition on approved classical reasoning | Met | Retains legitimate approved mathematical choice while refusing to present noncomputable selection as an executable construction. |

## Case 05: keep the whole generated predicate and all observable distinctions

Evidence: [generation plan](outputs/05-generated-predicate.md), sections 1–7,
including the recursive-surface table and annotation update counterexample.

| Recorded criterion | Result | Observed decision |
| --- | --- | --- |
| Deliver a generated whole predicate connected to the Lean owner | Met | Preserves the requested automatic counterpart, its executable dependencies, and an explicit source-to-target agreement route; examples and handwritten recursion cannot replace it. |
| Cover every recursive route and stored reference entry | Met | Separately lists all roots, check lists, optional annotations, filter annotations, and later or unreachable table entries. |
| Require independent coverage and reject empty diagnostics | Met | Uses an independent source census and oracle inputs; zero analyzed files cannot count as a successful diagnostic check. |
| Preserve duplicates and missing-versus-empty data | Met | Requires ordered raw entry data, explicit presence, and policy-driven normalization without inventing rejection rules. |
| Refute raw reconstruction from the wrong codec direction | Met | Shows `long` decodes to a value that encodes as `short`; retains the original raw entry for an unchanged-value update. |
| Distinguish codec acceptance, revival, and execution | Met | Separates the supplied codec acceptance from revival rejection and keeps both apart from a broader host implementation relation. |

## Case 06: use a short route when it is sufficient

Evidence: [completion verdicts](outputs/06-small-scope-control.md), the
PrintStyle and allowed sections.

| Recorded criterion | Result | Observed decision |
| --- | --- | --- |
| Accept the already closed passive leaf | Met | Accepts A at its supplied frozen revision without another graph, build, host test, or approval request. |
| Recognize admission ownership despite a finite result type | Met | B needs a small admission graph because it governs arbitrary raw programs, not because of the size of `Bool`. |
| Expose the always-false checker and require promised acceptance | Met | Retains its vacuous conditional theorem while refuting acceptance of the valid example; completeness is required only for the promised supported domain. |
| Keep added obligations proportional to the claim | Met | Adds only B's safety and promised acceptance connections; does not import runtime, liveness, or source-retirement work. |

## Structural checks and limits

Before installation, all seven packages passed the standard skill-creator
`quick_validate.py` checks. Additional checks parsed the UI metadata, checked
skill names and invocation prompts, resolved local Markdown targets, examined
text encoding and whitespace, and compared the frozen input bytes. No program
source or executable scripts are included in the pack. Installation integrity
is checked separately by comparing every copied file against the source tree.

These exercises demonstrate useful responses to six deliberately demanding
packets. They do not measure selection accuracy over ordinary conversations,
long-run proof success, time saved, or resilience to every failure mode. They
also do not rebuild the cited research artifacts or certify the existing
Effect4/Foldlab implementation. Future changes should rerun the affected
cases in fresh contexts with the scoring criteria withheld; retain an actual
failure and its correction instead of silently replacing the evidence.
