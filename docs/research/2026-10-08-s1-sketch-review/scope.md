# S1 Sketch review scope

No confirmed implementation defect has been found at the reviewed head.

Reviewed base: `8785c6f9`. Reviewed head: `979be0ad`.
The S1 commits are `351fb3f9` and `991d57da`.
The review branch is `codex/s1-sketch-review`.

Finishing criteria: inspect the changed declarations and their consumers, reproduce narrow builds, retain boundary controls, and inspect transitive axioms.

## Placement of the controls

These controls read existing laws or evaluate finite programs.
They state no new general theorem or planned goal.

| Concept | Existing claim and role | Controls and consumer | Reach | Exclusions | Requirement |
| --- | --- | --- | --- | --- | --- |
| `initial-algebras-folds` | `typed-replacement`, substitution; `focus-function`, inversion | Read `Sketch.check_fill_focusAt` and `Sketch.check_omit_focusAt` in `src/Effect4/Laws/Program/Sketch.lean`; editing is their consumer | A checked root block, two monomorphic definitions, body and main addresses, one host row, an existing hole | Behaviour, termination, root block fillings, normalization-only type equality | R14 |
| `initial-algebras-folds` | `module-address-table`, compatibility | Read `Sketch.refusals_nil_iff` in `src/Effect4/Laws/Program/Sketch.lean`; the query table is its consumer | Finite accepted and refused blocks, declaration mismatch, body scope and nested blocks | Refusal order after the head, admission, host replies | R14 |
| `host-session-protocol` | `block-call-instance`, preservation | Evaluate part signatures and body environments from `src/Effect4/Program/Typing/Parts.lean` | Two distinguishable declaration rows and body environments | Query integration, session runs, reference expansion | R6 |

Rows 291 and 294 bound hole rows and exact typing.
Rows 328 and 333 bound root blocks and their readers.
The review changes no declaration or owner ruling.

## Evidence boundary

`Sketch.check` is the module check with the hole table appended.
It is not signature admission or program admission.
The structural checker still refuses a definition block.
The body and main parts use the block signature.
The root focus uses the module check, in the empty environment.
A body's spine holds no focus.

The host boundary remains in `docs/core/host-boundary.md`.
No control runs a host program or establishes an execution observation.
