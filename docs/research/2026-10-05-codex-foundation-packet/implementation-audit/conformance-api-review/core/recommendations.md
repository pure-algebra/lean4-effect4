# Conformance APIs: bounded upgrades

Status: read-only source review at `182312f3`, with twenty actual Python API controls.
No Lean process, build, generator, installation, or active repository edit runs in this review.

The existing core is worth reusing. It separates check outcomes, evidence methods, exact result identities, strict configuration readers, and open obligations.
The compiler lane correctly reports finite comparisons as `tested`.
No current Conform producer was found falsely publishing a `proved` result.

## 1. Reuse evidence methods without promoting table metadata

The proposed builtin fields `inspected`, `control`, and `proved` serve different purposes.
Keep source notes, control identifiers, and proof-claim references as separate metadata fields.
A control identifier denotes a fixture until a retained run supports it.
A fidelity, domain, or cost description remains an authored claim until its named check establishes the property.
Do not introduce a second evidence ranking or derive `proved` from the table's field.

Use `Core.Evidence` when producing a report row.
Retain returned-value, exception, refusal, fuel, and cost observations separately where the profile needs them.
Continue using compiled Lean wrapper results for partial-application fixtures outside the source primitive evaluator's current admitted fragment.

## 2. Connect checked theorem references to proof-bearing rows

`Conform.Core.Proof` already aliases `ProofGraph.ProofRef`.
The validator checks theorem kind, the frozen proposition, universe parameters, and transitive axioms.
`Conform.Spec.Reflect.declareReflect` shows how a consumer reconstructs an expected proposition before validation.
Reuse that pattern for the first builtin law report.

Add a small report-row constructor that takes the independently reconstructed row-specific expected proposition and a theorem reference.
Validate the reference, then render the full proposition, universes, and actual axiom result into its detail.
Do not create the expected proposition by reading whichever theorem the caller names.
That would validate the theorem against itself without establishing the requested builtin law.

The Python validator checks only the shape of proof metadata.
It accepts `theorem = "NoSuchTheorem"`, `proposition = "False"`, and an empty axiom list.
It correctly rejects missing proof metadata and `sorryAx` in the supplied list.
These are schema observations, not kernel unsoundness.
A checked producer and its bound run receipt remain necessary.

The README currently says Core.Proof is used by model and normalization reports.
The current production normalization rows are tested rows, and those model reports were retired.
Correct that usage statement while documenting the new real consumer.

## 3. Bind the requested fixture domain at the consumer

`Report.complete` correctly checks a bijection between required identities and reported results.
The Python validator also supports independent `expected_ids`, `expected_pins`, and `expected_inputs`.
Current production callers do not supply those optional arguments.

Sixteen direct validator controls confirm the distinction.
Deleting a result alone fails. Deleting its planned identity and updating both counts passes without an independent request.
Supplying `expected_ids` detects that shrink. The pin and input expectations similarly detect their respective changes.
This is a limit of self-described reports, not a claim that the current fixture generator drops a case.

For the builtin slice, bind each requested case to its Lean declaration, raw arguments, observation, source profile, and target profile.
Retain the table and support-body hashes in the exact run inputs.
Construct expectations from those requested fixtures, independently of the lowering implementation and its results.
Pass available expectations into `validate`; do not copy the report's own values back as its expectations.
Keep dynamic closure discovery explicit where an independent fixed identity list is unavailable.

The existing runner checks exact output filenames and input stability.
Its `fresh_run` discovers reports by their self-declared format tag.
Four actual runner controls show that removing one report's tag makes that file an unchecked artifact when another valid report remains.
A missing output or an unsupported `conform-report` tag is correctly rejected.
For profiles with several reports, name their expected formats and tool identities beside their output filenames.
This is a bounded runner improvement. The current compiler step also validates its reports internally, which limits the immediate exposure.

## 4. Use obligations as open-work data

`Obligation.validate` checks registered kinds. `Report.withObligations` leaves the check outcomes unchanged intentionally.
The Python report reader validates obligation shapes, but has no caller registry parameter.
It accepts unregistered kinds and duplicate obligation entries.
It also accepts arbitrary `dependsOn` strings; those strings currently describe subjects, not a checked closed dependency graph.
Do not relabel them as measured proof dependencies.

`require_closed` means no obligations are present in this report.
Removing the obligations key makes that check pass; it does not prove the missing connection.
Keep this behavior available for ordinary inspection reports, with precise documentation.
When a real certificate consumer needs closure, supply its registered kinds and independent obligation plan, or derive closure from checked proof dependencies.
Do not add a global graph schema before that consumer exists.

`TypingAssessment` provides the right precedent: its successful typing value carries a proof, while separate remaining gaps cannot fabricate that proof.
`Model.Container.resolve` currently has no production caller found in the reviewed tree.
Its rendered law names and intersected law lists are metadata. It is not a shortcut to a checked builtin certificate.
No framework rewrite or revival of retired profiles is needed.

## Placement and order

These are proposed tooling obligations serving translation simulation and R8.
They do not prove the compiler correct or discharge R8's open numeric and host boundaries.

| Order | Consumer | Required property and immediate prerequisite | Exclusions |
| --- | --- | --- | --- |
| Now | Builtin fixture reports | Reuse Evidence and structural identities; pin the requested domains and exact emitted inputs | Metadata is not a theorem or universal agreement |
| Next bounded tool slice | Compiler report validator and runner | Compare supplied request expectations; require named report formats before accepting several outputs | Does not certify the producer's semantics |
| With first scalar proof | Proof-bearing builtin report | Reconstruct the expected proposition, validate ProofRef, retain universes and actual axioms | JSON proof strings alone remain untrusted metadata |
| Only when closure matters | A specific certificate consumer | Register obligation kinds and bind its own obligation plan or checked proof dependencies | Ordinary open-work reports may still pass their selected checks |

Proof goals belong first in a `Test` fixture importing the existing tool seam, with coordinator-owned root and registry placement.
Laws and Conform remain sibling libraries; no backwards Laws import is required.

## Retained checks

- `validator_probe.py`: sixteen calls to the actual `scripts/lib/conform_report.py.validate`.
- `fresh_run_probe.py`: four calls to the actual runner, using only tiny Python producers in this scratch directory.
- Both output JSON records retain the exact cases, accepted outcomes, and refusal diagnostics.
- The current row coverage and invalid-evidence positive controls remain green.

Commands:
`python3 /private/tmp/codex-effect4-overnight-monitor/2026-10-05-conformance-api-review/core/validator_probe.py`
`python3 /private/tmp/codex-effect4-overnight-monitor/2026-10-05-conformance-api-review/core/fresh_run_probe.py`
