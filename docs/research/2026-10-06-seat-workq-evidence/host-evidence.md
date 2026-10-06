| Scenario | Entry | Evidence | Scripts | Limit |
| --- | --- | --- | --- | --- |
| routing | `outcome` | host | all 8 |  |
| routing | `repositoryCalls` | host | all 8 |  |
| routing | `refusals` | ledger | all 8 |  |
| workers | `assignment` | reader: cells | all 17 |  |
| workers | `receipts` | host | all 17 |  |
| workers | `applications` | host | all 17 |  |
| workers | `retired` | host | all 17 |  |
| workers | `cleanups` | reader: cells | all 17 |  |
| workers | `rootExit` | host | all 17 |  |
| workers | `workLeft.runnable` | reader: dispatchers | all 17 | zero by the run's own wait, in 12 of 17: applied-2, applied-1-2, applied-2-1, unreceived, applied-1, stale, cancelled-running, cancelled-between, cancelled-root, lowest, cancelled, twice |
| workers | `workLeft.queued` | reader: dispatchers | all 17 | zero by the run's own wait, in 12 of 17: applied-2, applied-1-2, applied-2-1, unreceived, applied-1, stale, cancelled-running, cancelled-between, cancelled-root, lowest, cancelled, twice |
| workers | `workLeft.awaiting` | host | all 17 |  |
| workers | `workLeft.pending` | host | all 17 |  |
| workers | `workLeft.timers` | reader: sleeps | all 17 |  |
| timeout | `calls` | host | all 14 |  |
| timeout | `receipts` | host | all 14 |  |
| timeout | `applications` | host | all 14 |  |
| timeout | `retired` | host | all 14 |  |
| timeout | `stored` | host | all 14 |  |
| timeout | `attempts` | reader: cells | all 14 |  |
| timeout | `cleanups` | reader: cells | all 14 |  |
| timeout | `root` | host | all 14 |  |
| timeout | `timers` | replay only | 5 of 14: parked, timed-out, late, received, eager |  |
| timeout | `timers` | reader: sleeps | 9 of 14: 503, four, 404, before, second, kept, timer-interrupt, host-interrupt, resetting |  |
| atomic | `decisions` | reader: fibers | all 8 |  |
| atomic | `window` | reader: cells | all 8 |  |
| atomic | `account` | reader: cells | all 8 |  |
| atomic | `completed` | reader: fibers | all 8 |  |
| atomic | `cleanups` | reader: cells | all 8 |  |
| queue-workers | `assignment` | reader: cells | all 25 |  |
| queue-workers | `queue` | reader: cells | all 25 |  |
| queue-workers | `fed` | host | all 25 |  |
| queue-workers | `receipts` | host | all 25 |  |
| queue-workers | `applications` | host | all 25 |  |
| queue-workers | `retired` | host | all 25 |  |
| queue-workers | `opened` | reader: cells | all 25 |  |
| queue-workers | `cleanups` | reader: cells | all 25 |  |
| queue-workers | `finished` | reader: cells | all 25 |  |
| queue-workers | `rootExit` | host | all 25 |  |
| queue-workers | `workLeft.runnable` | reader: dispatchers | all 25 | zero by the run's own wait, in 21 of 25: fed, applied-2, blocked, applied-1-2, applied-2-1, unreceived, cancelled-running, cancelled-running-closed, cancelled-waiting, cancelled-waiting-closed, cancelled-offer, cancelled-root, closed, rewaiting, rewaiting-fed, unwithdrawn, kept, masked, taken-back, stays, twice |
| queue-workers | `workLeft.queued` | reader: dispatchers | all 25 | zero by the run's own wait, in 21 of 25: fed, applied-2, blocked, applied-1-2, applied-2-1, unreceived, cancelled-running, cancelled-running-closed, cancelled-waiting, cancelled-waiting-closed, cancelled-offer, cancelled-root, closed, rewaiting, rewaiting-fed, unwithdrawn, kept, masked, taken-back, stays, twice |
| queue-workers | `workLeft.awaiting` | host | all 25 |  |
| queue-workers | `workLeft.pending` | host | all 25 |  |
| queue-workers | `workLeft.timers` | reader: sleeps | all 25 |  |
