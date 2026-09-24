# Divergence integration and slice 5 retarget

The once-over of `439f27f3..7c3b62ea` found no blocker. The four divergence commits were
fast-forwarded onto `refactor/phase1-phase3` on 2026-09-23. The owner authorized continuing
through this integration and slice 5 in the current task; the earlier “yes proceed” also
explicitly approved the bounded CE-009 consumer amendment. Nothing was pushed.

The code review checked the optional cause's default, its update at an actually preempted
failure handler, and the three consumers (`resumeCause`, `finalizerOr`, `exitScoped`).
Projection lemmas retain the original structural observations. The receipt's changed
expectations cover the changed runtime and battery values. `run_eq_ref` and
`run_eq_ref_exit` retain their original source and premises.

The two finite witnesses changed only their proof bodies to `decide +kernel`. A fresh
`lake env lean /private/tmp/effect4-divergence-review.lean` printed `[propext, Quot.sound]`
for those two witnesses and both runtime agreement theorems (exit 0). An initial invocation
used the wrong Witnesses namespace and exited 1; correcting the names was the only probe
change. No source or statement changed during the review.

Fresh `python3 docs/research/2026-09-21-foundations-divergence-evidence/implementation/VerifyArtifacts.py`
passed (exit 0): all 36 earlier host rows and manifest observations, the runtime theorem
source and original batteries, the protected files and all 11 generated hashes agree.
`bun run harness/truth/run-truth.ts --self-test-divergence` passed all nine controls (exit 0).
The exception checks the exact fixture, scenario, exit pair, compared schedules, sync
agreement and settled host; `check-truth.py` also requires exactly one signed fixture.
Changing the old Lean failure back into agreement does not bypass this check.

A fresh SHA-256 verification of all 61 decompressed retained logs passed. The retained
`make check`, `check-ocaml`, `check-truth` and `check-census` logs end in their passing results.
These are the implementation's sweep evidence, not a newly repeated sweep. The integration
changes documentation only after the fast-forward and owes no redundant sweep under AGENTS.

The coordinator records now distinguish the landed runtime repair from the still-open
state-preservation proof. Slice 5's retarget removes three stale references to the superseded
walk premise, keeps the frozen no-run-premise statement, and reserves the next unused
counterexample ID if a new obstruction is checked. CE-009 remains the carrier obstruction.
The slice 5 branch must fast-forward to this coordinator commit before implementation.
The finish criteria remain the packet's two slices, exact proof ceilings and final checks.
