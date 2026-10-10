# Prepared run-view receipt

`frame` now takes its program and row table from the run's `Api.Built`.
Its former independent program argument is removed.
The existing driver calls `frames`, whose signature stays the same.
The renderer retains nine exact `Classical.choice` exclusions through existing text and layout functions.
This receipt changes no trust-gate policy.

## Landing

Base: `9389e543`.
The commit following this receipt records the head.
The managed worktree is `/Users/pooks/.codex/worktrees/prepared-run-view/lean4-effect4`.
The source change is `tools/Tools/View/Run.lean`.
The other changed files are this directory's finite controls and evidence.

`Prepared built` holds source paths, checked lines and printed code.
`prepare` uses `built.program` and `built.table` together.
`framePrepared` requires preparation indexed by the frame's own built input.
`framesBuilt` prepares once and transports that preparation across planned controls.
`frame` also supports a run with a nonempty row table.

## Proof placement

The only new theorem is `controlOnce_built` in `tools/Tools/View/Run.lean`.
Its five-point placement follows.

1. Concept: `initial-algebras-folds`, serving fold congruence through an unchanged built input.
2. Question: the tool check `prepared-run-view-agrees`, permitted by decisions rows 334 and 336.
   The theorem supplies the immutable input premise.
   Its consumer is `framesBuilt`.
3. Reach: each `Run.controlOnce` retains exactly `s.built`, including its program and row table.
4. Limits: the theorem proves no view equality, cost bound, host correspondence, progress or liveness.
5. Unlock: the run viewer retains the static readings between control frames.
   This serves the R13 journal face and the R14 checked source view.

`Compare.lean` checks view agreement on a finite corpus.
It states no generic agreement theorem.
The preparation reads source addresses.
It assumes no correspondence between source addresses and expanded call addresses.

## Verification

Run `python3 docs/research/2026-10-10-live-graph-support/run-view/verify.py` from the worktree.
`verification.json` records each command, exit code and source hash.
Every Lake command uses `LEAN_NUM_THREADS=3` and runs sequentially.

- `narrow-build.log`: `lake build Tools.View.Run Tools.View.Build` passes.
- `driver-imports-build.log`: the direct driver's other imports build.
- `driver-build.log`: `lake env lean tools/Drivers/View.lean` passes.
- `comparison.log`: full page output agrees with the retained base implementation for eight corpus programs, bounded at 32 controls.
- `Compare.lean`: the nonempty-table control checks the displayed `number` type and `Host.read` spelling.
- `Compare.lean`: the former empty-table frame refuses that host call.
- `Compare.lean`: the prepared code remains present across the live host frontier.
- `reuse.log`: compiled `framesBuilt` calls `prepare` once.
- `reuse.log`: compiled recursive and dynamic frame bodies contain no preparation call.
- `driver-run.log`: the driver writes three fork-run frames.
- `verification.json`: all three emitted SVG frames parse and contain text.
- `host-render.log`: the host control writes its second frame with one outstanding call.

`render/003.png` and `render/host.png` are raster readings of the retained SVG files.
The command is `rsvg-convert INPUT.svg -o OUTPUT.png`.
Both images were opened and visually inspected.
The completed fork frame retains its program, code and two completed fibers.
The host frame displays its checked type, host call and parked fiber.

## Axiom gate

`audit-raw.log` retains the refusal from `#axiom_audit Tools.View.Run`.
It reports nine of 54 declarations reaching `Classical.choice`.
The paths enter through existing string operations and graph layout.

`AuditRender.lean` uses the same cycle-aware walk and the gate's declaration facts.
It checks all 54 declarations.
It admits `Classical.choice` only at these exact names:

- `Tools.View.Run.prepare`
- `Tools.View.Run.framePrepared`
- `Tools.View.Run.frame`
- `Tools.View.Run.framesBuilt`
- `Tools.View.Run.frames`
- `Tools.View.Run.framesBuilt.go`
- `Tools.View.Run.framesBuilt.go._f`
- `Tools.View.Run.framesBuilt.go._sunfold`
- `Tools.View.Run.framesBuilt.go._unsafe_rec`

The last name is Lean's generated safe recursor twin.
The audit rejects authored unsafe declarations.
Every other declaration stays within `[propext, Quot.sound]`.
No declaration reaches a planned goal.
`audit-render.log` records the passing scan.

## Preparation evidence and limits

`benchmark.log` retains the short sample's noisy timings.
`benchmark-long.log` records three alternating-order samples over 30 corpus repetitions.
The longer sample timings vary widely.
This receipt makes no wall-time improvement claim.
Read the exact nanosecond timings in `benchmark-long.log`.
Each sample has the same output checksum, `195960`.
The command is `lake env sh -c 'LEAN_PATH="$1:$LEAN_PATH" lean --root="$1" --run "$1/Bench.lean" 30' run-view PATH`.
Here `PATH` is this receipt's directory.

These timings measure Lean's interpreter on a finite corpus under the current machine load.
They establish no general speed ratio or complexity bound.
The compiled inspection establishes one preparation call per frame sequence.
Dynamic fiber graph construction and layout still run per frame.
Preparation stores source readings; it supplies no running fiber's current source address.
It establishes no host or outside-runtime agreement.
The change touches no printer, interpreter, codec or outside-runtime relation, so it runs no behaviour gate.
No full sweep, push or primary merge runs.
