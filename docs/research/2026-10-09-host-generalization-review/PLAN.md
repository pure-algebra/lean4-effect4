# Host generalization review plan

## Scope

Review the captured working changes above `0a108d2f`.
The review tests the general-host replacement of H8's reply-tape local run.
The snapshot records work in progress, not a claimed landing.

## Obligation placement

| Check | Concept and claim | Consumer and scope |
| --- | --- | --- |
| H8 statement remains unchanged | translation-simulation; `rows-denotation-session`, R6 | the registered session observation, including absent exits |
| Request-sensitive host control | translation-simulation; proposed `rows-denotation-reactor`, R6 | the generalized local run, under a fixed deterministic host |
| Waiting versus budget exhaustion | translation-simulation; `rows-denotation-session`, R6 | explicit finite budgets and host nonanswer |
| Typed reply control | host-session-protocol; `reply-at-call-instance`, R6 | the existing checked session, no new handle allocation |
| Exact axiom walk | proof trust for the named claims | selected changed laws and H8, not the whole-library gate |

The controls add no production theorem or claim.
Keep the registered H8 statement and its premises unchanged.
A helper's build establishes no host progress or session-to-host connection.

## Finish criteria

- Pin the changing files before testing.
- Read three independent reviews.
- Compile the changed modules and their narrow direct consumers in an isolated artifact overlay.
- Exercise a host that distinguishes requests, and a host that gives no answer.
- Compare H8's statement against the reviewed commit.
- Check the exact dependencies of the selected laws.
- Record new findings and resolved concerns without repeating unchanged findings.
- Leave active implementation files and Claude's session unchanged.

## CO-5 follow-up

CO-5 lands during this review at `37d566d8`.
Capture its two changed law modules separately.
Check H9 with a stateful host over a finished session.
Check the normal driver's state after a refused reply.
These controls serve `rows-denotation-reactor`, R6, and its proposed drive consumer.
They establish no arbitrary-host completion guarantee.
Keep CO-4 and CO-5 evidence separate.

## H9 checker follow-up

The checker lands at `8a613615` during verification.
Check its exact returned state against both driver controls.
Build its law and its new session battery.
Do not extend this review into the active typed-protocol implementation.
