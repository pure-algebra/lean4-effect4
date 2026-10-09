# Module overwatch: duplicate-proof cleanup

The review finds no new defect in `7334f119`.
The cleanup keeps the surviving theorem statements and their premises.
Focused compilations and the scoped dependency check pass.
No new module behavior or host compatibility claim follows from this cleanup.

## Checkpoint and ownership

Previous primary checkpoint: `7b73d59cb2ae5b290c87c7f0ba9a6aa77a71fa04`.
Reviewed primary checkpoint: `7334f1197cf5b535541ce1dfc7789a5082c07115`.
Previous review receipt: `86cec31e67d6af3ff4c3f3a1ee145ced7061a832`.
The primary worktree stays clean at the reviewed head.

The active Claude session is `9ebf38b2-8b2f-44e5-8fd9-2dc0cb5a1f50` in the primary repository.
A bounded recent tail records its cleanup, the repaired registration test reference, and its reported passing build.
The reader excludes internal thinking fields.
The review sends no message to Claude and changes no production source or ruling.

Two GPT-6.1 Sol agents inspect the remaining proof substitutions and their effect on the proof graph.
The parent compiles selected consumers independently in temporary directories.
No review Lake process, full sweep, merge, or push runs.

## Module consequences

| Consumer and source | Shared declaration | Retained boundary |
| --- | --- | --- |
| `leaseReply_at`, `borrower_typed`, and `giveBack_answers`, `src/Effect4/Laws/Library/Pool/Ops.lean` | `Model.leaseReplyTy_normal` and `Model.returnReplyTy_normal`, `src/Effect4/Laws/Library/Pool/Typing.lean` | The resource type's canonical-form premise remains |
| `without_image`, `withdraw_eval`, and `take_eval`, `src/Effect4/Laws/Library/Semaphore/Data.lean` | The existing identity-table laws remain the consumers' source | Removing the unused `request_equal` copy does not remove table injectivity from withdrawal or taking |
| The typed printer, `src/Effect4/Laws/Codegen/PrintTyped.lean` | The existing template congruence family in `src/Effect4/Laws/Codegen/Read.lean` | Binder depth and agreement at holes remain premises |
| `neverSkip`, `Test/Program/RegistrationYield.lean` | `Bounds.subN_never`, `src/Effect4/Laws/Program/Bounds.lean` | The constructed registration configurations retain their original scope |

The Pool, Semaphore, printer, and reader patches match the prior reviewed working-tree snapshot byte for byte.
The remaining source review compares 1,392 surviving theorem headers across 21 proof files.
Only whitespace differs in their normalized headers.
The broader graph review reports unchanged surviving headers across all changed Laws files.
The reviews also inspect the replacement statements and proof bodies.

The substitutions keep sequencing's equal-error premise, failure membership, interruption premises, store cell counts, and zero-fuel behavior.
Deleted helpers have no remaining required source, test, or automation reference.
Imports and automation attributes remain unchanged.

This is useful consolidation behind the existing author interface.
It adds no author option, program constructor, stored closure, or independent behavior model.

## Proof graph

`tools/ProofGraph/Registry.lean` is byte-identical across the reviewed range.
The generated claim text, statuses, and goal dependencies remain unchanged.
The diagram now exposes additional uses of the existing `seq_typed` and `Bounds.subN_never` laws.
That records shared proofs more accurately without claiming additional behavior.

No planned goal, semantics attribute, or search rule changes.
The frozen contracts and counterexample pins require none of the removed names.
The core implementations and the applicable rulings remain unchanged.

## Reproduced checks

All compilations use Lean `4.33.1`, `LEAN_NUM_THREADS=3`, and `warningAsError=true`.
The source bytes come from the reviewed commit.
The manifest records their hashes, exact commands, elapsed times, and exit results.

| Freshly compiled module | Result | Declarations checked for axiom dependencies |
| --- | --- | --- |
| `Effect4.Laws.Library.Semaphore.Data` | Exit 0 | 23 |
| `Effect4.Laws.Library.Pool.Ops` | Exit 0 | 119 |
| `Effect4.Laws.Codegen.PrintTyped` | Exit 0 | 1974 |
| `Test.Program.RegistrationYield` | Exit 0 | 96 |

All 2212 selected declarations, including generated declarations, stay within `propext` and `Quot.sound`.
`Effect4.Author` imports no Laws module.
The parent also replays the graph comparison and the retained audit driver.
The producer reports a passing full build and gates.
The review reproduces only the focused checks above.

The first audit-tool draft needs an explicit natural-number annotation for its counter.
The corrected tool passes.
The retained draft error is a review-tool error, not a production finding.

## Next action and limits

Keep the existing author interface and use shared laws directly at their module consumers.
Treat this cleanup as consolidation, not an expansion of module compatibility.
The next substantive module work still needs the declared execution observation and its independent model.
Shared acquisition, waiting, and cleanup must retain their scheduling and identity premises.

This review closes the pending review of the prior cleanup snapshot.
It leaves the earlier public module-printer and whole-module execution obligations open.
The sibling directory `2026-10-09-duplicate-overwatch/` retains commands, hashes, logs, source comparisons, and replay scripts.
The scripts use the named local repository and its existing compiled imports.

## Retained patch bytes

The three retained `.diff` files keep Git's context-line spaces and terminal context lines.
The whitespace check allows those bytes only in these files.
All other retained files use the ordinary whitespace check.
