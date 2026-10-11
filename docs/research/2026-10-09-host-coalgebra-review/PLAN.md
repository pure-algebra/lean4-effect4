# Host coalgebra review plan

## Claim and scope

Review the proposed connection between the generic coalgebra layer and Effect4's checked host session.
The generic comparison concerns finished runs against the same host and initial state.
The Effect4 note proposes stronger uses for stopped runs and typed replies.

## Placement of the controls

| Control | Existing claim or proposed consumer | Concept and role | Reach and limit |
| --- | --- | --- | --- |
| A system that always cuts | CO-4, `rows-denotation-session`, R6 | translation-simulation; counterexample control | finite run; no liveness claim |
| Distinct call instances at one request | CO-6 typed protocol, `reply-at-call-instance`, R6 | host-session-protocol; counterexample control | data replies; no handle allocation |
| A funded unanswered run | CO-3 system adapter, R6 and `funded-run-replay` | translation-simulation; premise control | finite journal; no future scheduling claim |
| Generic theorem reader | CO-5, `rows-denotation-reactor`, R6 | translation-simulation; theorem consumer | finished run and identical host state |
| Unbounded program depth | existing `E4-ALG-CE-008` | initial-algebras-folds; existing counterexample | source review; no new uniform-depth theorem |

The controls add no library theorem or planned goal.
They constrain the proposed CO-3 through CO-6 adapters on the M7 path.
The tested finite outputs do not prove those adapters.

## Finish criteria

- Pin the note and generic sources.
- Read the independent reviews.
- Reproduce the call-instance and always-cut controls.
- Build the generic modules narrowly in a copied review package.
- Check selected generic proof dependencies with the existing exact axiom walk.
- Record each new obligation and the strongest justified result.
- Keep both active implementation checkouts unchanged.

The package copy contains only the imported source closure and the selected test.
It uses the installed Lean toolchain and no third-party dependency.
The review runs one Lake process at a time.
