# R2 typed evaluation checkpoint

Integrate the repaired evaluation helper before the remaining park and command clauses.
The actual interruption uses the installed caller, including a caller that interrupts itself.

Base: `55a90853a` on `codex/symbolic-native-fold`.
Coordinator source baseline: `b4dcef4f1` plus its checked R2 working changes.
Changed modules:

- `Effect4.Laws.Program.Typed.Commands.Evaluate`
- `Effect4.Laws.Program.Typed.Commands.Clauses.Iter`
- `Effect4.Laws.Program.Typed.Commands.Clauses.Loop`

Placement: residual-program-typing, R4; dependency of typed-state-reachable preservation.
The exported endpoint statements remain unchanged.
Passive iteration literals gain their explicit empty addressed edit word.

## Actual interruption

The old self-interruption proof overwrites the interrupted record with the caller's local record.
R2 installs the caller first and applies the interruption afterward.
The repaired proof uses `configTyped_interruptRecord` on that installed caller.
Its other-target arm uses the same existing law on the retained target.
`rupdate_self` removes the final unchanged owner installation in both arms.
No message assumption, new carrier or additional planned goal enters either proof.

## Verification

The coordinator's active build makes direct dependency links transient.
The check copies its built artifacts with `cp -c -R` into `/private/tmp/typed-r2-artifacts/lib`.
All seven reserved output modules are removed from that copy before compilation.
The checks write only those private outputs.
The remaining dependency paths name the coordinator's existing package libraries.

Run each changed source with:

```sh
LEAN_PATH=<private artifacts and coordinator package libraries> LEAN_NUM_THREADS=3 /Users/pooks/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean -DwarningAsError=true --root=. -o <private module output> <source path>
```

All three modules pass.
The measured Iter check takes 6.6 seconds.
The measured Loop check takes 4.4 seconds.
The audit imports Iter and Loop, then runs:

```lean
#axiom_audit Effect4.Laws.Program.Typed.Commands.Evaluate
  Effect4.Laws.Program.Typed.Commands.Clauses.Iter
  Effect4.Laws.Program.Typed.Commands.Clauses.Loop
```

Result: 340 declarations within `[propext, Quot.sound]`.
The audit reports zero planned goals and zero declarations modulo planned goals.
`git diff --check` passes.

## Remaining work

Park still uses the eager observer machine before the caller's local installation.
Its new actual result carries that observer as an addressed edit instead.
The unchanged raw countdown helper does not yet bridge this different cut.
Async, Command and Close remain outside this checkpoint.
The coordinator owns the whole-law build and runtime gates after the R2 migration.
This checkpoint claims no outside-runtime comparison.

## Park checkpoint

Base: `36a31df7b`.
The changed module is `Effect4.Laws.Program.Typed.Commands.Clauses.Park`.
The actual observer message changes the installed target before the parked disposition.
`settle_observe_park` connects that result to an observer change after the existing disposition.
`configTyped_observe` consumes `configTyped_addObserver` at the actual target record.
Join and countdown consume these helpers with their existing fresh-token and saved-frame proofs.
A self-target retains its observer on the installed caller.
The exported `FiberClauseKeeps` and `CountdownParks` statements remain unchanged.
The countdown helper now names the plan before its observer message.
The glue helpers retain an arbitrary addressed edit word.

The direct Lean command above passes with warnings treated as errors.
The audit imports Park and runs `#axiom_audit Effect4.Laws.Program.Typed.Commands.Clauses.Park`.
Result: 157 declarations within `[propext, Quot.sound]`, zero goals and zero declarations modulo goals.
The private dependency snapshot still holds the earlier Observe artifact.
The coordinator's integrated build must rebuild Observe and its dependent modules.
The current repair fence adds Observe because its countdown callback changes the actual waiter after interruption.
Async, Command and Close remain to check.
No outside-runtime comparison is claimed.
