# Record field refusals

Status: implementation authorized, after the record term source and typing stages.
Base at preparation: `cdd1261b`, including the checked typing signature repair `fdb0598d`.
The coordinator requested field-specific record refusals under the approved `record-contract.md`.

## Contract

`argTy`, `argsTy` and `Record.check` keep ownership of term acceptance.
Their definitions and successful results do not change in this slice.
`Checker.term?` first matches the existing `termTy` result.
On success it returns that type immediately. On failure it computes an error description.
This avoids a second term traversal for accepted inputs.

A diagnostic fold uses the generated `TermAlgebra` and reconstructs each raw term beside its diagnostic computation.
Its inputs are the existing argument-typing functions and the atom's literal flag.
It follows the typing rule's child order and flags.
It follows only the first failed child, even when that child has only the old generic reason.
It therefore cannot skip an earlier failure to blame a later field.

The coordinator also approved cause-contained record failures.
A generated cause fold follows the same first-failure rule, while `causeTy` remains its acceptance owner.
`Checker.cause?` diagnoses only a failed `causeTy` result.
Its stored `RecordCauseRefusal` carries a cause path and a separate `RecordTermRefusal`.
A cause path uses zero for the left child of `both` and one for its right child.
The term path starts at the selected cause leaf's term.
Append `TypeReason.recordCause` after the new record-term reason.
A cause-specific failure, such as a non-natural interruptor whose term typed successfully, retains the existing generic cause reason.

Append one `TypeReason.recordTerm` constructor after all existing constructors.
It carries a nested term address and a passive record-reason value.
Existing program paths keep their current `Node.child` meaning.
Within a term, the separate address numbers immediate term children in source order.
Atom and record arguments use their index. A field target uses zero. An update target uses zero and its replacement uses one.
No address is silently appended to the program path.

Construction reasons cover repeated declaration or supplied names, missing required fields, unknown supplied fields, and wrong supplied field types.
They also cover unequal name and value counts.
Read reasons distinguish a missing field from a required read of an optional field.
A type mismatch retains the actual and declared types and the field name.
A length mismatch retains both counts.
A nested malformed declaration retains the existing formation refusal where that diagnosis applies.
A non-record target and existing non-record term failures may retain the generic `TypeReason.term` fallback.
The public raw formation pass still runs before program typing, so it may report duplicate declarations first.

The diagnostic function is not a program admission function and never supplies a successful type.
The existing checker projection and judgment agreement remain the acceptance specification.
This slice does not assign TypeScript error codes or change emission policy.

## Edit fence

- `Program/Typing/TermRefusal.lean`: passive reason data and the diagnostic fold, importing the current rules and generated fold.
- `Program/Typing/Blame.lean`: append the reason constructor and its name projection.
- `Program/Checker.lean`: failed-term and failed-cause payloads, with their success projection laws.
- `Program/Typing.lean`: reuse the cause success projection in the existing weakening proof.
- `Laws/Program/Typing/CheckInversion.lean`: a successful-term inversion lemma in the existing checker bank.
- `Laws/Program/Signature.lean`: retain the existing `term?_ext` statement and its new cause-check analogue, using equal diagnostic inputs.
- Direct statement-preserving checker proof repairs if the new inversion lemma requires them.
- `Test/Program/RecordRefusals.lean`: focused field, order, path and acceptance controls.
- This brief and its receipt.

The coordinator owns root imports, canonical carrier entries, generated refusals and target diagnostic cases.
No old constructor is reordered and no generated file is edited here.

## Proof placement

| Obligation | Concept and existing question | Reach and hypotheses | Consumer and requirement | Exclusions |
| --- | --- | --- | --- | --- |
| The located term check has the same success projection | Residual Program Typing; existing checker agreement | Every typing signature, type environment, program path and term | `toOption_term?`, program weakening and `check_sound`/`check_complete`; M5 and R3 | Error text alone adds no typing rule |
| Successful term checks invert to the existing term rule | Residual Program Typing; existing checker agreement | Every successful `term?` result | Existing checker rule bank and its inversion theorems; M5 | No new acceptance algorithm |
| A typing signature extension keeps the located term check | Residual Program Typing; existing signature-extension compatibility | Existing `SigExtends` premises, including equal atom typing and literal flags | `term?_ext`, then the checker's algebra agreement; R3 | No weakening of row or service premises |
| Field reasons and term addresses follow the failing input | Residual Program Typing; located refusal required property | Failed term typing, with the existing constructor order and literal flags | Concrete record authoring errors and public program checks; R3 and R8 | Finite controls establish their tested cases, not a separate universal reason-completeness theorem |

The first three obligations repair existing laws without changing their statements.
The same placement covers the cause success projection and its inversion helper.
Their consumers are `check_weaken`, the existing checker bank and the typing signature algebra agreement.
`termRefusal_ext` serves the term and cause check extension helpers.
The new inversion helper has a named consumer in the existing checker bank.
The fourth row is executable diagnostic coverage; the checker still decides acceptance through the first row.
No new proof graph or type judgment is introduced.

## Verification and done criteria

Build the changed core and the direct checker, typing signature and typing-law consumers.
Run a focused fixture with each named refusal and successful neighbors.
Test nested record failures under an atom, field target and replacement, plus an earlier generic child failure.
Test nested causes with separate cause and term addresses, including an earlier generic cause failure.
Check that direct literal children retain literal types while general string variables still fail literal declarations.
Keep raw formation precedence and successful program types unchanged.
Inspect axiom output for the changed projection, inversion and typing signature laws.
Run the strict language check on this brief and receipt, then `git diff --check`.
Commit explicit source and receipt paths after the narrow checks.
No full battery, target execution check or generator run is included.
