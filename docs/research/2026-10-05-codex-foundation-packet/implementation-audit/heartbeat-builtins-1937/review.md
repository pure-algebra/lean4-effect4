# Builtin table: bounded audit at 8b236fa7

One remaining name boundary needs a small correction.
The committed engine has no collision at that boundary.
A second finding concerns the independent check of repeated parameters.

Evidence status: source inspection and thirteen finite Python controls.
Scope: `182312f3..8b236fa7` and its committed OCaml artifacts.
This monitor runs no Lean, OCaml compiler, generator, installation or repository write.
The later staged T3b integration remains outside this review.

## 1. Keep extern helper identity through top-level emission

`ExternFn.headNames` records an unqualified helper such as `sh_machine_finished`.
`Translate.noteFree` places it in the caller's `freeRefs`.
The second naming pass protects that name from local binders.

`Translate.emissionGroups` rejects duplicate generated names and builtin reservations.
It does not reject a generated name that equals an extern helper's name.
`Translate.hygieneProblems` calls `Ml.shadowDiags` on parameters and bodies.
It does not check the top-level binding name.
`Ml.checkModule` permits ordinary sequential value shadowing and cannot inspect the raw hand prelude.

The existing row is `fn Effect4.Machine.RunMachine.finished 1 sh_machine_finished` in `ocaml/engine/externs.txt`.
`globalName Effect4.sh_machine_finished` also gives `sh_machine_finished`.
The existing hand helper lives in `ocaml/engine/tools/api_engine_prelude.ml`.
`LcnfGen.main` places that hand prelude before generated declarations.

A constructed translated declaration named `sh_machine_finished` can therefore hide the hand helper from later declarations.
A caller that also calls that generated declaration has a dependency forcing it before the caller.
Its extern call then reaches the generated declaration too.
The emitted functions can have the same type; a compiler type check need not catch the change.

The retained mirror uses an empty fiber table.
The hand helper answers true there.
A generated function of the same name answers false.
The intended pair is `[false, true]`; sequential target name resolution gives `[false, false]`.
The current emission-name and local-shadow checks both accept that constructed shape.
Renaming the generated function restores the intended pair.

This is a pre-existing boundary left open by the robustness refactor, not a new regression.
It is a source-constructed check witness, not a persisted-LCNF or compiled-OCaml reproducer.
The committed engine closure manifest contains no extern-head collision.

Smallest correction: retain extern helper heads as distinct target dependencies and compare them with emitted global names.
A collision should produce a located refusal, or generated calls should use qualified hand helpers.
Do not forbid every `freeRefs` entry globally: ordinary calls legitimately name generated declarations.
Keep extern literals that name generated dependencies distinct from the intentional caller-local `root` literal.

Placement: `translation-simulation`, R8's typed-lowering open part; the proposed `builtin-application-hygiene` and support-closure work.
Consumer: `Translate.emit`, `LcnfGen.main` and the compiler checkpoint with an extern table.
Property: every emitted extern call resolves to the helper named by its row.
Hypotheses: valid extern table, closed translated declarations, explicit hand-prelude exports and declared emission order.
Observation: identity of the function reached, then its returned value on the admitted domain.
Exclusions: the helper's own correctness, all-source translation, host effects, compiler correctness and whole-runtime agreement.
Immediate prerequisite: distinguish ordinary generated references from extern helper references.

## 2. Check duplicate names inside one parameter batch

`Ml.Env.shadows` compares each new name with the prior scope and protected names.
It does not compare names within the new batch.
Consequently, `shadowDiags []` accepts a binding with parameters `[x, x]` and body `x`.
The same gap affects `Expr.fn [x, x]`.
A nested function binding `x` under an existing `x` is correctly refused.

The mandatory `Ml.checkModule` path does not close this gap.
Its `duplicate-binding` check concerns names in a binding group, not parameter names.
`checkParams` checks patterns and defaults without checking repeated names across parameters.
The normal translator's `fresh` currently prevents this shape.
Thus this finding concerns the promised independent check, not a demonstrated wrong generated program.

Smallest correction: make the opt-in shadow check process each binder batch sequentially.
Keep `_` and `()` exempt because they bind no name.
Retain a repeated-parameter mutant beside the existing nested-shadow and distinct-parameter positives.
Do not return only `duplicate-binding` if `shadowDiags` continues filtering that code out.

Placement: the same R8 hygiene obligation.
Consumer: `hygieneProblems` as an independent check of translated declarations.
Property: no parameter hides a preceding parameter or protected reference.
Hypotheses: the opt-in no-shadow profile and the admitted expression fragment.
Observation: a diagnostic for the colliding binder, with the distinct-name positive accepted.
Exclusions: arbitrary OCaml rejection; ordinary OCaml permits sequential parameter shadowing.
Immediate prerequisite: define within-batch binding order for the existing check.

## Verified improvements and limits

The table holds the rows, normalized keys, support bodies and row contracts together.
The new reservation covers builtin eta names and extern eta names.
The second naming pass protects ordinary generated calls and extern heads from local capture.
The original argument layouts and numeric bodies remain unchanged by source comparison.
Non-atomic arguments are bound before non-strict and under-applied builtin forms.
The documented total/pure carrier premise remains necessary where conversions stay in applications.
The wildcard LCNF Makefile input includes the new Builtins module.

The retained seat outputs report generation checks on four artifacts and a passing compiler profile.
Those are the seat's observations; this monitor does not rerun them.
No new runtime defect is established in those artifacts.
The thirteen Python checks retain the source hashes, inputs, diagnostics and positive controls.
