# HO-3a follow-up: callback columns need the shared type inventory

Collect callback type columns before landing the widened TypeScript printer.
The current draft grants program admission to an unformed callback type and emits an undeclared callback payload class.
Both failures come from the same omitted inventory entries.

## Reviewed state

The implementation base is `41151468ffd97d0df25ed7d13080eee783ab199e` on `claude/ho3`.
The review parent is `648fe735cc3a143aa7e3817a3f7cb420552c5727`.
[The checkpoint](checkpoint.json) records the working changes and their hashes.
[The draft snapshot](owner-draft.json) retains the reviewed diff.
This is a review of working HO-3a changes, not a claim that HO-3a has landed.

The bounded Claude session tail verifies the repository working directory.
Claude is waiting for the law build before committing HO-3a and is reading the HO-3b invocation route.
The review leaves Claude's worktree and session unchanged.
[The placement](PLAN.md) precedes the probes and identifies the existing claims.

## HO3-ANN-01: callback columns escape the shared inventory

`Formation.declAnnotations` in `src/Effect4/Program/Formation.lean` collects a definition's request, answer, and error.
It omits every column of `DefDecl.params`.
The new `paramType` in `src/Effect4/Codegen/Print.lean` prints all three callback columns.

[Generated.lean](Generated.lean) checks a helper whose unused callback takes a payload class named `OnlyParam`.
The source checker accepts the program, and `Api.printModule` returns a module.
The emitted callback header names `OnlyParam`, but the module declares no such class.
Pinned tsgo reports `TS2304: Cannot find name 'OnlyParam'.`
The positive control also mentions that type in the helper's ordinary request column.
Its module declares the class and passes tsgo.
The generated declarations remain unchanged in these checks.

[AnnotationFormation.lean](AnnotationFormation.lean) checks a second consequence with a repeated record field.
The callback's request contains two fields named `item`.
`Formation.checkInput` and `admitProgram` accept it when it appears only in the unused callback.
Both refuse the same raw type in the helper's ordinary request column.
The source typing query accepts both cases; raw formation is a separate judgment.

| Request type location | Raw formation | Program admission |
| --- | --- | --- |
| Valid callback request | accepts | accepts |
| Repeated field in callback request | accepts: defect | accepts: defect |
| Valid ordinary request | accepts | accepts |
| Repeated field in ordinary request | refuses | refuses |

The raw omission already exists in the definition metadata collector.
HO-3a additionally exposes it through callback type printing.
These finite controls establish neither a runtime type violation nor a counterexample to output closedness.
The missing-class cases lie outside `ParamDecl.readable`, so they do not refute G6.

## Smallest repair

Extend `Formation.declAnnotations` with each parameter's raw request, answer, and error.
Retain the definition index, parameter index, and column in each position.
For example, append `params`, the parameter index, and `request` beneath the existing declaration position.
`Formation.sites` then retains the raw occurrence position within that type.

Do not normalize before collecting these columns.
Do not use row-template formation for stored callback declarations.
Those templates permit open types that these callback declarations do not.

Reuse the collector in its existing consumers:

- `ClassTable.moduleClasses` in `src/Effect4/Codegen/ClassTable.lean` collects required payload classes.
- `annotationRefusal` in `src/Effect4/Codegen/Print.lean` checks TypeScript type spelling.
- `Formation.programSites` in `src/Effect4/Program/Formation.lean` supplies the raw input check.

A class-only patch leaves the malformed callback type accepted.
A separate callback validation traversal duplicates the shared source of type metadata.
The author should declare each callback type once and receive a located refusal when that declaration is unformed.
No new stored program representation or author option is needed.

[The proof outline](PROOF-DAG.md) identifies the helper statements that must grow with the inventory.
It also separates this repair from target binding and service forwarding.

## Earlier findings now have generated-output controls

The earlier packet records `HO3-NAME-01` and `HO3-SVC-01`.
This follow-up upgrades their evidence from handwritten target projections to actual `Api.printModule` output.
None of these cases needs invocation printing.

| Generated case | tsgo observation | Positive control |
| --- | --- | --- |
| Callback named `Payload` captures a generated constructor | `TS7009` and `TS2345` | Rename callback to `use` |
| Callback named `Widget` captures the root of `Widget.run` | `TS2339` | Rename callback to `use` |
| Callback named `Token` captures a row's trailing identifier | `TS2345` | Rename callback to `use` |
| Service method takes a callback, but its wrapper omits it | `TS2554`, one argument missing | Ordinary service |
| Service initializer takes a callback, but its wrapper omits it | `TS2554`, two arguments expected | Ordinary service |

The qualified-root, trailing-name, and service cases still read back to the source program.
Their target rejection therefore does not contradict the structural reconstruction theorem.
Keep the existing repair recommendations: shared lexical-use inventory and a refusal for deferred service callback forms.
`HO3-REQ-01` remains unchanged; this follow-up does not repeat its requirement-row experiment.

## Reconstruction progress and evidence

The draft now pairs each definition with its body in `readDefs_printDefs` and `blockReadable`.
Each body uses its own parameter typing signature and spelling map.
`readDefBodies` extends that context separately and recurses at the block context.
The API route now consumes those facts through `ModuleEmission.readModule`.

The independent cycle-aware audit checks these compiled modules:

- `Effect4.Laws.Codegen.Definitions`;
- `Effect4.Laws.Codegen.Module`;
- `Effect4.Laws.Api.ModuleReadable`.

It reports 486 declarations within `[propext, Quot.sound]`, zero planned goals, and zero declarations resting on planned goals.
[The target and audit results](checked-results-targets-audit.json) retain the exact output.
This audit does not certify target acceptance or execution.

## Reproduction and limits

Run each command from the isolated review worktree, in this order:

```sh
LEAN_NUM_THREADS=3 lake env python3 docs/research/2026-10-10-ho3-print-review/followup-1945/run_probes.py generate
LEAN_NUM_THREADS=3 lake env python3 docs/research/2026-10-10-ho3-print-review/followup-1945/run_probes.py inventory
LEAN_NUM_THREADS=3 lake env python3 docs/research/2026-10-10-ho3-print-review/followup-1945/run_probes.py targets audit
LEAN_NUM_THREADS=3 lake env python3 docs/research/2026-10-10-ho3-print-review/followup-1945/run_probes.py runtime
```

[Generation](checked-results-generate.json) records twelve accepted source programs and their exact generated modules.
[Target checks](checked-results-targets-audit.json) record six positive modules and six intended target rejections.
[Raw formation](checked-results-inventory.json) records the four input cases and eight guards.
[Runtime checks](checked-results-runtime.json) record six positive observations: `[7, 7, 8, 7, 7, 1]`.
The compiler is tsgo `7.0.0-dev.20260629.1`; the runtime is Effect `4.0.0-rc.112` under Bun `1.4.2`.

The checks reuse Claude's compiled imports and record source and artifact hashes before and after each run.
Every completed run records unchanged inputs.
They do not rebuild those imports or run a full behaviour gate.
Target fixtures prepend explicit imports and external row implementations without changing generated declarations.
The external row implementations are finite fixtures, not independently proved host semantics.

The first fixture attempts contain local Lean syntax errors and an incorrect expectation about the separate source typing query.
Their result files remain as setup evidence.
An earlier generation run expects the wrong constructor diagnostic code.
The corrected generation and target runs pass.
No production repair, merge, push, or message to Claude occurs in this review.
