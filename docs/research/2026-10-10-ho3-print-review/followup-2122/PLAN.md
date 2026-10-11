# HO-3b proof completion review

Review the working changes over `000bcd7ad68e7bbbe4f3478831982a7f9f2f1a42`.
Compare them with review commit `0a29433ac412fe875bae18a57330ac96f88b0876`.
Keep the implementation worktree and its session unchanged.

## Placement

This review adds no registry claim or planned goal.
Its isolated repair probes retain the existing helper statements.
It checks existing reconstruction claims under the `exact-codecs` concept in `docs/core/semantics.md`.
Their role is `compatibility`, and their requirement is R8 in `docs/core/system-map.md`.

| Claim | Pointer and path | Reach | Limit | Consumer |
| --- | --- | --- | --- | --- |
| `typed-print-connector` | `Program.printTyped_eq_print`, `src/Effect4/Laws/Codegen/PrintTyped.lean` | No joined row or approved site needs type arguments | No target compiler or runtime claim | Authoring output comparison, R8 |
| `typed-print-erasure` | `Codegen.eraseJoinArgs_printTyped`, same path | Readable program, lawful spelling, successful typed print | Does not establish successful printing | `readTyped_printTyped`, R8 |
| `typed-print-read` | `Codegen.readTyped_printTyped`, same path | The same premises, followed by the named erasure | No target compiler or runtime claim | Typed reader reconstruction, R8 |
| `module-defs-round-trip` | `Program.readModule_printModule_defs`, `src/Effect4/Laws/Codegen/Definitions.lean` | Existing readable declarations, paired bodies, spelling, layers, and service premises | No target compiler or runtime claim | `Api.printModule_roundTrip`, R8 |

Decisions rows 325, 328, 340, and 341 bound this review.
The invocation helpers serve the existing claims through `read_print`, `childEnv_template_depth`, and the two erasure inductions.
They establish no machine typing, substitution, host meaning, progress, or schedule independence.

## Finish criteria

1. Record the current source, compiled inputs, and owner session report.
2. Rebuild the two newly changed proof modules in the review worktree.
3. Audit the affected proof modules with the cycle-aware axiom checker.
4. Compare public theorem statements and inspect their consumers.
5. Record unchanged findings without repeating their probes.
6. Commit the review files locally after their checks pass.

Keep successful printing as an explicit premise.
The earlier empty-list refusal remains an independent printing defect until production changes repair it.
