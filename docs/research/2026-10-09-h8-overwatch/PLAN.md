# H8 landed-step review

Review only the landed commits `97d69de4` and `1f4ee194`.
Claude owns the later changes to `Agreement/Machine.lean`.
Keep those changes and all production files unchanged.

## Finishing criteria

- Inspect the active session and distinguish its edits from landed code.
- Build the changed modules and selected direct consumers at the pinned commit.
- Check reply consumption, frontier observations, and state through finalization.
- Record the exact commands, results, trust dependencies, and remaining obligations.

## Placement before probes

| Item | Placement |
| --- | --- |
| Concept and property | `translation-simulation`: agreement between program meaning and machine observations |
| Question | Claim `rows-denotation-session`, role simulation. Its pointer is `denoteRows_eq_session` in `src/Effect4/Laws/Api/SessionMeaning.lean`. |
| Existing step | `localRunC_compile` in `src/Effect4/Laws/Program/Agreement/Calls.lean`; the command-loop connection consumes it. |
| Reach | `StraightRows`, sufficient compile depth, a fixed reply tape, arbitrary outer stack and mask. Decisions rows 310, 313 and 323 apply. |
| Exclusions | Reply admission, handle allocation, scheduler behavior, host conformance, and frontier-state equality remain separate claims. |
| Consumer | The H8 command-loop proof, then requirement R6. Probe declarations are research controls, not new registry claims. |

## Probe questions

Does `ReachesC` identify execution states, or only their final observations?
Does a reply consume one tape entry while retaining the stores?
Does a finalizer retain body state after a host failure?
Do the table-generalized laws retain their empty-table consumers?
Can a session finish with less compile fuel than the whole program syntax depth?
That control serves the budget connection into `denoteRows_eq_session`.

## Checks

Use one Lake process with `LEAN_NUM_THREADS=3`.
Run narrow builds and the isolated probe only.
Do not run a full sweep, merge, or push.
