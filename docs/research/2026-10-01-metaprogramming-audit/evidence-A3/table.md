# A3 static arm and site census

Base: `8c9be2588332d9f9094c5a6ecd7d9e3af8a0ac55`. No Lean compiler run.

| Family | Definition | Direct arms, in order | Proof sites | Nested callers |
| --- | --- | --- | --- | --- |
| hops_leaf | Approximation.lean:386 | exact spawn_grows<br>exact start_grows<br>exact interruptEach_grows<br>exact countdownPark_grows<br>exact linkScope_grows<br>exact forkFinalizers_grows | Approximation.lean:427 (fireObserver_grows)<br>Approximation.lean:503 (withFiber_extends)<br>Approximation.lean:516 (evaluatePrim_extends) | hops_observers:441 |
| hops_observers | Approximation.lean:440 | hops_leaf<br>exact fireObserver_fold_grows | none | hops_cmd:561 |
| hops_cmd | Approximation.lean:560 | hops_observers<br>exact drainOwed_grows<br>exact fireObserver_grows<br>exact launchEntrant_grows<br>exact exitFiber_grows<br>exact settle_grows | Approximation.lean:575 (driveStep_grows) | hops_loop:599 |
| hops_loop | Approximation.lean:598 | hops_cmd<br>exact drive_extends | Approximation.lean:732 (stepDecision_extends) | none |
| queue_hops | Scheduling.lean:116 | exact spawn_queue (interp := $i)<br>exact start_queue (_interp := $i)<br>exact interrupts_queue (interp := $i)<br>exact countdown_queue (interp := $i)<br>exact link_queue (interp := $i)<br>exact forkFinalizers_queue (interp := $i) | Scheduling.lean:145 (observer_queue)<br>Scheduling.lean:204 (withFiber_queue)<br>Scheduling.lean:225 (evaluate_queue)<br>Scheduling.lean:279 (driveStep_queue) | none |

Counts: {"families": 5, "directArms": 22, "definition": 5, "nested-arm": 3, "proof-site": 9}. These are source occurrences, not runtime selections.
