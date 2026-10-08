# Independent module boundary audit

The checked capture, named-input, removal, identity, and tuple slices show no semantic defect in these controls.
The semantics registry descriptions and test-root imports need coordinator integration at the reviewed checkpoint.

Reviewed base: ce9a2ecbab229d8937ca9ce67272c126b667488e.
The reviewed production files remain unchanged.
The retained probe is 2026-10-08-seat-module-boundary-probe.lean.

`LEAN_NUM_THREADS=3 lake build Test.Program.StepFolds Test.Program.StepInputs Test.Program.StepLists Test.Schema.Identity Test.Schema.Modeled` passes, 866 jobs.
`LEAN_NUM_THREADS=3 lake env lean /private/tmp/module-boundary-final.lean` passes after correcting the probe's imports and typed literal syntax.
All checks run serially in the isolated worktree.
No whole sweep runs.

The independent finite probe checks:

- A used capture's refusal retains its original scope and source path inside a fold.
- A syntactically used capture refuses during translation even when the runtime loop list is empty.
- Transparent context and Step-type aliases retain named source ordering and lifted local inputs.
- A flat triple image retains all three values and rejects a short raw tuple.
- Model.refusal still refuses tuple types; the exact image supplies no Modeled admission.
- Equal-looking malformed opaque values supply no native deferred comparison reading.

The existing StepLists battery distinguishes first-match removal from all-match removal on duplicate inputs.
The existing StepFolds battery separates scope alignment from successful finite evaluation.
The existing Schema.Identity battery retains the external capability premise and rejects other handle roles.

Step.sound carries ScopeFacts and IdentityFacts in Laws.Modules.Step.
These premises remain conditional; the total candidate denotation grants no reading outside them.
Source translation can ignore syntactically unused inputs, while Step.sound asks for readings of every declared input.
This is a limitation of the theorem's admitted source table, not a compiler refusal claim.
The laws establish no allocation validity, run progress, cost, or external host agreement.

At this base, Test.All does not reach StepFolds, StepInputs, StepLists, PoolData, or Schema.Identity.
The coordinator owns the final root imports.
The step-language-sound semantics registry title omits the new scope and identity premises and still excludes folds.
The step-language-typed semantics registry title also still excludes folds.
The coordinator owns the final claim descriptions.
A static import traversal finds no Laws module reached from Effect4.
This source traversal is not a substitute for the library-root gate.

The generic tuple Step constructor and Queue operation connectors remain unfinished work at this base.
This receipt claims no completion for them.
No production, root, ruling, or generated file changes during this audit.
