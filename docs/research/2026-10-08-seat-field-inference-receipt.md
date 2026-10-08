# Field reference inference: receipt

## The merge fact

A known schema now supplies an inferred field type to `field_ref%`.
The expression `.len (.get cell (field_ref% "xs"))` compiles without an element-type annotation.
Unresolved schemas still postpone lookup, and opaque schemas still refuse.

## Scope

- Base: `88a660b3`.
- Branch: `codex/module-field-inference`.
- Head: the commit that carries this receipt.
- Worktree: `/Users/pooks/.codex/worktrees/module-field-inference/lean4-effect4`.
- Changed: `src/Effect4/Schema/FieldRef/Elab.lean`, `Test/Program/StepLanguage.lean`, and `Test/Schema/Modeled.lean`.
- Added: this receipt.

The change keeps `FieldRef.here` and `FieldRef.there` as the stored data.
The elaborator resolves the schema before unifying the requested field type.
It postpones failed schema reduction only when the schema contains unresolved metavariables.
The existing refusals remain in the battery.

The new controls cover nested list inference, direct reference inference, and a schema supplied by a later argument.
The collision control replaces its forbidden axiom-print command with `#check`, and updates the expected diagnostic.

This is a meta helper for the existing `record-field-laws` consumer.
It states no new theorem, changes no judgment, and creates no proof obligation.

## Commands and results

All Lean commands run in this worktree, with `LEAN_NUM_THREADS=3`.

| Command | Result |
| --- | --- |
| `lake build Effect4.Schema.FieldRef.Elab` | passes, 37 jobs |
| `lake build Effect4.Modules.Step Effect4.Schema.Modeled.Derive` | passes, 70 jobs |
| `lake env lean -DwarningAsError=true /private/tmp/ow03-macro-inference.lean`, before repair | refuses `FieldRef fields (Ty.list ?m.4)` because the expected type contains metavariables |
| `lake build Effect4.Schema.FieldRef.Elab Test.Program.StepLanguage Test.Schema.Modeled` | final run passes, 837 jobs |
| `lake build Test.Program.StepLanguage`, after adding delayed-schema control | passes, 835 jobs |
| `lake env lean -DwarningAsError=true /private/tmp/ow03-macro-inference.lean`, after repair | passes |
| `lake env lean -DwarningAsError=true /private/tmp/ow03-macro-positive.lean` | passes: opaque field instance, renamed field, namespace, anonymous-instance name collision |
| `lake env lean -DwarningAsError=true /private/tmp/ow03-macro-preflight.lean` | passes: last-helper collision refuses and leaves no earlier helpers |
| `lake env lean -DwarningAsError=true /private/tmp/ow03-macro-opaque-schema.lean` | exits 1 with the expected located refusal: schema does not reduce to literal fields |
| `lake env lean -DwarningAsError=true /private/tmp/ow03-macro-trust.lean` | passes the scoped axiom checks below |
| `git diff --check` | passes |

The first combined battery run found two control errors, which were repaired before the final run.
The replacement `#check` reports the fully qualified unknown name.
An evaluation control could not infer its carrier; the retained control checks the emitted term instead.
The first trust-audit run found an unused variable in its logging code; the corrected audit passes.

## Trust

`Lean.collectAxioms` reports no axioms for the six added declarations under `Test.Program.StepLanguage.FieldInference`:
`fields`, `input`, `length`, `xs`, `choose`, and `delayed`.

The changed meta elaborator reaches `[propext, Classical.choice, Quot.sound]`.
Its module already appears in `auditImplementationModules`; this slice changes no exemption.
The scoped audit is not the whole-tree axiom gate.

## Limits

The schema's list, names, and flags must reduce to literals, within the existing 4096-cell fuel bound.
Missing, duplicate, optional, and wrong-type fields still refuse.
An unknown expected schema needs information from another expression before lookup can succeed.
Genuinely opaque schemas remain outside this elaborator's profile.

The checks are compiler and finite evaluations, not host execution evidence.
No sweep, merge, push, registry edit, root edit, or new ruling occurs in this slice.
