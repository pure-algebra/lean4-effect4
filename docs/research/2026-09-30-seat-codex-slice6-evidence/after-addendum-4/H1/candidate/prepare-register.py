from pathlib import Path
import difflib

root = Path('/Users/pooks/Dev/lean4-effect4-slice6')
out = Path('/private/tmp/h1-candidate')
rel = 'Test/Counterexamples/REGISTER.md'
before = (root / rel).read_text()
rows = [line for line in before.splitlines() if line.startswith('| `E4-SCHED-CE-016` |')]
assert len(rows) == 1, 'CE016 row missing or repeated; re-read register'
assert '| SEEDED 2026-09-30 |' in rows[0], 'CE016 status changed; re-read register'
assert '`E4-SCHED-CE-017`' not in before, 'CE017 now exists; re-read register'
assert '`E4-SCHED-CE-018`' not in before, 'CE018 now exists; re-read register'
replacement = '''| `E4-SCHED-CE-016` | REPAIRED 2026-10-01 | M6's queue fact types every queued resume | Original `docs/research/2026-09-30-pass/lift/verify-decision.lean` and `lift/verify-steppreserves.lean`; retained in `Test/Counterexamples/Machine/Semantics/M6Capstone.lean`: `EarlyStep.old_steps_false`, `EarlyDecision.old_fire_false`, `H1.loaded_sleep80_typed`, `EarlyStep.early_queue_rejected`, `EarlyDecision.early_dispatcher_rejected` | Internal keys in TypedState and queued resume keys in QueueOk must be below nextToken; keys are also disjoint from active external requests. The exact early queue and dispatcher are refused. The loaded sleep control discharges the old falsifiers' initialization premise; the eighteen command proofs remain open. |
| `E4-SCHED-CE-017` | REPAIRED 2026-10-01 | M6's queue fact types every queued command | `docs/research/2026-09-30-side-audit/probes/TokenFinish.lean`; retained in `Test/Counterexamples/Machine/Semantics/M6Capstone.lean`: `H1.loaded_typed`, `H1.step_finish_false`, `H1.proposed_step_finish_false`, `H1.bad_finish_rejected` | QueueOk applies generated RCmdOk to every command and adds scheduler authority, unique owners and reserved keys. The unit-typed root's finish with success 42 fails the new queue fact. The exact reference code-site scan and all eighteen command proofs remain open. |
| `E4-SCHED-CE-018` | REPAIRED 2026-10-01; SEEDED 2026-09-30 | A token is typed by what its observer delivers | Seed: `docs/research/2026-09-30-seat-codex-slice6-evidence/H1/ObserveGap.candidate.lean`; retained in `Test/Counterexamples/Machine/Semantics/M6Capstone.lean`: `OldObserve.proposed_step_observe_false`, `H1.bad_observe_rejected`, `H1.join_delivery_typed`, `H1.await_delivery_typed` | Stored and queued observers connect the source exit to the declared delivered type: joinEffect delivers the source exit, awaitValue delivers its encoded Exit value. The actual interpreter hook has the matching local typing lemma. Countdown and race buffers have finite payload clauses; registration, hook certification and the eighteen command proofs remain open. |'''
after = before.replace(rows[0], replacement, 1)
(out / 'REGISTER.deferred.md').write_text(after)
(out / 'register.deferred.patch').write_text(''.join(difflib.unified_diff(
    before.splitlines(keepends=True), after.splitlines(keepends=True),
    fromfile='a/'+rel, tofile='b/'+rel)))
(out / 'register-current-rows.txt').write_text('Current CE016:\n'+rows[0]+'\n\nCE017: absent\nCE018: absent\n')
print('Deferred register patch written outside repository; apply only after the named H1 controls pass.')
