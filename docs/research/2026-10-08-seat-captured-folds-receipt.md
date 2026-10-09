# Captured folds: checked interface and laws

The coordinator must supply `ScopeFacts` in the Latch's two wake proofs.
Their statements retain their hypotheses.
The proof is `by cases setOpen <;> trivial`.
The constructor extension remains the coordinator's next slice.

## Commits and files

The base is `ca688ee0`.
The core checkpoint is `fe632c14`.
The checked laws and battery are `c5093ef87373834be6db92eb3d447c89bc80c65e`.
The branch is `codex/step-captured-folds`.

The owned files are:

- `src/Effect4/Modules/Step.lean`;
- `src/Effect4/Laws/Modules/Step.lean`;
- `Test/Program/StepFolds.lean`;
- this receipt.

## Contract and placement

`Step.fold` stores its list, initial accumulator and body.
The body inputs are the accumulator, the element and the outer inputs.
`StepAlgebra` indexes its carrier by the input context and the result type.
The stored syntax holds no function.
The translation still targets `Term`.

The translation resolves caller sources at their original scope.
Under a fold, `capturedSource` inserts two slots through `Term.weaken`.
Nested folds repeat that operation on term data.
The translation resolves only syntactically used sources.
It translates both branches of a selection.

| Declaration | Concept and claim | Reach and premises | Consumer |
| --- | --- | --- | --- |
| `Step.sound` | `translation-simulation`, `step-language-sound`, R10 | Every identity context, input readings, the reading check, and `ScopeFacts` | Module step agreement statements |
| `Step.typed` | `store-typing`, `step-language-typed`, R4 | Native atoms, input typing, typing facts, and `ScopeFacts` | Module step typing statements |
| `Step.frame` | `translation-simulation`, `step-frame`, R10 | An update spine and a field outside its overwrite footprint | Module frame statements |
| `Step.tree_exists` | Helper of `step-language-sound` | Successful source resolution, without a carrier inhabitant | The fold arm of `Step.sound` |
| `Step.fold_eval_image` | Helper of `step-language-sound` | Body evaluation at each actual accumulator and element | The fold arm of `Step.sound` |
| `Step.eval_fold` | Helper of `step-language-sound` | The fold's carrier denotation | Module value equations |

The helpers live in `src/Effect4/Laws/Modules/Step.lean`.
The plan places them in `docs/research/2026-10-08-seat-module-gaps-plan.md`.

The generic reading and typing statements gain an explicit premise.
`ScopeFacts` requires environment length to equal scope depth only when the step contains a fold.
It is trivial for a step without folds.
The final argument has a default proof for concrete steps without folds.
The module operation statements do not gain a premise.

A fold is no update spine in this slice.
The existing frame statements retain their types.
These results establish no allocation validity, wrapper scheduling, progress, liveness or target execution.

## Commands and results

The following commands run in the isolated worktree.
Each command uses `LEAN_NUM_THREADS=3`.

```sh
LEAN_NUM_THREADS=3 lake build Effect4.Modules.Step
LEAN_NUM_THREADS=3 lake build Effect4.Laws.Modules.Step
LEAN_NUM_THREADS=3 lake env lean Test/Program/StepFolds.lean
LEAN_NUM_THREADS=3 lake env lean /private/tmp/ow04-fold-axioms.lean
git diff --check
```

The core build passes.
The shared law build passes.
The focused battery passes.
The diff check passes.

The direct-consumer command is:

```sh
LEAN_NUM_THREADS=3 lake build Effect4.Laws.Modules.Step Effect4.Laws.Modules.Latch.Steps Effect4.Laws.Modules.Semaphore.Data Effect4.Laws.Modules.Pool.Data Effect4.Laws.Modules.Queue.Data
```

The three existing data modules build.
The Latch fails only at `wakeStep_agrees` and `wakeStep_types`.
Their default scope proofs cannot reduce the free `setOpen` variable.
The coordinator owns those caller edits.
No sweep runs.
No push runs.

## Trust evidence

The narrow axiom probe reports:

```text
'Effect4.Modules.Step.sound' depends on axioms: [propext, Quot.sound]
'Effect4.Modules.Step.typed' depends on axioms: [propext, Quot.sound]
'Effect4.Modules.Step.frame' depends on axioms: [propext, Quot.sound]
'Effect4.Modules.Step.frame_read' depends on axioms: [propext, Quot.sound]
'Effect4.Modules.Step.tree_exists' depends on axioms: [propext, Quot.sound]
'Effect4.Modules.Step.eval_fold' depends on axioms: [propext]
```

This probe checks named theorem dependencies.
It is not the whole-library axiom gate.

## Independent controls and remaining work

`Test/Program/StepFolds.lean` reads the shared laws at concrete inputs and an empty element carrier.
Its finite evaluations check nested captures and an original caller source that inspects its scope.
They also check a captured caller term that contains its own fold.
An unused source refuses, while the translated fold still answers.
A longer value environment produces the predicted unequal answer and fails `ScopeFacts`.

The coordinator adds the battery's root import.
The coordinator updates the existing registry descriptions for the new scope premise.
The constructor and identity extensions follow these checkpoints.
