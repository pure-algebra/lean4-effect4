# Conformance runner: two fixes before the new support mutant

Prioritize failed-run retention and an exact negative-check contract. Both directly serve the planned support-body mutant and target-only fixtures.

Evidence status: source inspection and 19 isolated Python assertions.
Scope: main `182312f30194f0beefa7a6273eb1144aa834c0f0`.
No Lean, OCaml compiler, generated executable, build, generator, or installation ran.
The compiler-step controls mock process outcomes. They exercise the actual Python decision code, not native execution.

## 1. Preserve an unsuccessful attempt before rejecting it

`check-conform.step_compiler` compares runtime stdout with `expected.txt` before writing `actual.txt`.
A mismatch therefore loses the actual observation file. `run` also truncates failed subprocess diagnostics before raising.
A compiler or runtime failure can leave missing reports and extra compiler outputs.
`conform_report.fresh_run` rejects that output set inside `TemporaryDirectory`; it then deletes the directory without retaining the failed artifacts.
The previous receipt remains, which is useful history but is not evidence about the latest failed attempt.

The isolated controls distinguish two cases:

- A complete report containing a refusal returns exit1 and is retained correctly.
- An incomplete unsuccessful producer is rejected, and its output directory is gone afterwards.

Smallest change: capture full subprocess results and write actual stdout before comparing it.
On every producer exit, retain an attempt record and its raw artifacts before validation or publication.
Keep validation status separate from the producer's exit. An invalid attempt must remain invalid.
Do not publish its incomplete reports as a successful conformance result.
Record the exception diagnostic without deleting the source, compiler outputs, stdout, stderr, and command that explain it.

Consumer: the new support-body mutant, target-only fixtures, and the next failed compiler checkpoint.
Property: failed acceptance preserves enough evidence to reproduce the failure without changing the successful-run contract.
This is runner infrastructure. It is not a new semantic theorem or a whole-lowering certificate.

## 2. Require the intended negative observation

The positive compiler step compares stdout byte-for-byte and rejects a normal mismatch.
The current UTF-8 negative control accepts exit1 plus any stderr containing a tab followed by FAIL.
It ignores the failing fixture identity and the mutant's stdout.
The actual Python step accepted `NOT-IN-THE-PLAN\tFAIL` in an isolated mocked-process control.
It correctly rejected exit2 and a failure without that marker. These are bounded runner observations.

The retained historical run reports `12\tFAIL`, but this is not a current source-bound expectation.
Its report hashes match the retained files. Its recorded hashes for `check-conform.py` and `Normalization.lean` differ from current source.
Do not reuse that historical fixture number as the new permanent mutation contract.

For the planned support-body mutant, declare the selected fixture identity and expected counterexample before running it.
Require the negative run to compile. Require its failed observation to name an allowed fixture from the selection.
Check the unchanged successful prefix when the executable stops at its first failed assertion.
Reject unrelated exceptions, missing observations, unexpected identifiers, and an unresolved evaluator result.
Retain mutant stdout and stderr separately, the exact emitted mutant bytes, and the original artifact's hash.
A source or target evaluator mutant must produce a counterexample, not merely a reader refusal or fuel exhaustion.

Consumer: the actual support-function body consumed by the target evaluator and OCaml compiler.
Proposed placement: `translation-simulation`, R8's open typed-lowering part, as bounded wrong-rule controls.
Observation: the named fixture changes its value or permitted target outcome under the declared mutation.
Hypotheses: same input selection, admitted fixture, original positive control, actual mutated artifact, successful target compilation.
Exclusions: general compiler correctness, exhaustive rule coverage, and upstream runtime claims.
Prerequisite: the coordinator's shared support assembly and explicit mutation identity.

## 3. Make the fixture selection an API input

`Normalization.Fixture` currently stores source arguments, target arguments, two expected values, and an OCaml check string.
`step_compiler` derives host identities from `expected.txt`; host rows use numeric or short textual identifiers.
Source and target interpreter rows include an index, declaration name, and label.
A named selection shared across lanes can relate these observations without matching display strings.

Keep target-only fixtures explicit. Their absent source lane is a declared scope, not a silently missing result.
A small fixture record can name the lane, stable identity, argument encoder, expected outcome, and observation.
Use the existing `CheckId`, `Report`, and validation machinery. No new report system is needed.
The core-report scout owns external expected identity, pin, input, and report-role validation; its findings are not a duplicate dispatch here.

For the first slice, keep the existing native equality assertions and exact stdout protocol.
Add named expected failure outcomes only where the support mutant or next primitive needs them.
Later, a typed host outcome can record a returned value or exception without turning every failure into an anonymous exit.
Do not require that wider protocol before the two concrete runner fixes.

## 4. Preserve diagnostic distinctions

Source and target interpreters already keep fuel exhaustion separate from values.
The target also distinguishes an actual exception. Neither is a success by default.
Both `stuck` constructors combine an unsupported rule with a malformed value shape.
Their differentials label all such cases refused, whereas the shared report documentation calls unsupported checks unresolved.

This is a diagnostic precision opportunity, not evidence that an existing green result is false.
When target-only cases need it, split structured reasons: unsupported form, missing primitive, wrong arguments, target exception, and fuel exhaustion.
Map these reasons consistently to report outcomes. Preserve existing fuel-frontier behavior.
Retain the input, evaluated outcome, and expected outcome as structured detail for the failing fixture.
Avoid changing the semantic meaning of all refusals merely to make report counts agree.

## 5. Bind host evidence to the executed artifact

The runner records the outer producer command. The selected compiler path and each compiler/runtime invocation live only inside `step_compiler`.
`ocaml.json` records a compiler version but has an empty input list; the outer receipt binds the generated artifacts by hash.
Preserve that useful outer binding, and add exact subprocess argv and full results to the attempt record.
This directly identifies `OCAMLOPT` overrides, compiler flags, and the generated file a host result consumed.
The `native` profile checks Lean native layout. Actual OCaml primitive execution belongs to the `compiler` profile; keep those labels distinct.

## Recommended landing sequence

1. Retain every failed attempt and full process result, with positive and incomplete-failure controls.
2. Give the new support-body mutant a named expected failure and enforce its diagnostic, using the original artifact as the positive control.
3. Add a shared named fixture selection with explicit source, target, and host lanes as target-only fixtures arrive.
4. Add structured stuck reasons only for the new cases that need the distinction.

File ownership: the coordinator assigns `scripts/check-conform.py`, `scripts/lib/conform_report.py`, and the relevant Conform fixture producer together.
The support-assembly seat keeps its existing ownership. This advice does not edit or dispatch either slice.

The retained probe also demonstrates report-role demotion and self-declared empty-domain acceptance.
Those belong to the core-report scout's work, and are not additional runner recommendations here.

## Exact report-role control

The actual `fresh_run` accepts two expected JSON files when one is valid and the second has no format tag.
Its receipt validates only the first file. A two-valid-report control also passes.
Use explicit expected file roles: report with schema/tool identity, or raw artifact with its own validator.
Do not infer a required report role from the producer's format field. This is a confirmed bounded API acceptance gap.
The existing outer receipt still hashes every expected output and snapshots source and compiled Lean inputs before and after execution.
Those strengths remain; they do not establish that each expected report underwent validation.
