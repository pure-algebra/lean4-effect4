# Region stacks along an actual command prefix

The bracket reader now derives its entry-stack shape from the actual command prefix.
The boundary premise excludes an executed detached evaluation that finishes the region.
The finite control shows why a continuing whole fiber does not supply that premise.

Base: `b2aafba8a`.
Head: the commit containing this receipt.

## Placement and scope

Concept: scope-lifetime-finalization, R11, the saved-mask region bracket.
Question: `stack-local`, role invariant, serves `compiled_region_bracket` in `src/Effect4/Laws/Program/MaskBracket.lean`.
Reach: a compiled command-loop cut, every finite budget, and the watched live identity before the allocation counter.
The later cut is the actual result of `driveState` with its command residue.
Every executed loop or delivery tests the existing evaluator after detaching the entry suffix.
The premise supplies no resulting stack equation.

`compiled_region_bracket_of_prefix` derives the canonical region prefix and applies the existing bracket.
The original bracket statement remains available without changes.
The proof establishes no cleanup count, progress, or outside-runtime observation.
This landing covers one command prefix.
The outer scheduler and decision-history extension remains separate.

## Structure

`StackRegion` reuses `iteration_under`, `evaluateNative_under`, and the shared interference classification.
The same other-fiber edits retain the exact saved stack.
The existing allocation bound excludes a new fiber with the watched identity.
The assertion reads only the allocation counter and live stored fibers.

`StackRegionCommands` covers every actual command, including stale waiter write-back after nested interrupts.
A new frame appears above the entry suffix.
Exit publication removes the live obligation before stack clearing.
The compiled queue supplies the exit-clearing premise.

`Machine.Lift.PrefixAllows` reads a side condition at each command actually executed by the existing finite loop.
Stopped and exhausted cuts require no next-command premise.
`driveState_lift_allowed` transports the region together with the existing compiled cut.
It defines no replacement execution state or evaluator.

The control's full fiber enters its caller callback and continues.
Its detached region finishes, so the same delivery fails the boundary condition.
The actual loaded program also reads the new entry law.

## Verification

Commands, each with `LEAN_NUM_THREADS=3`:

- `lake build Effect4.Laws.Program.StackRegion`: passes, 353 jobs.
- `lake build Effect4.Laws.Program.StackRegionCommands Test.Dogfood.Scenario.Atomic.WriterPhase Test.Dogfood.Scenario.Workers Test.Dogfood.Scenario.Timeout`: passes, 1229 jobs.
- `lake build Test.Program.StackRegion`: passes, 879 jobs.
- `lake build Test.Dogfood.Scenario.Atomic.WriterOwnership Test.Machine.MaskBracket`: passes, 1131 jobs.
- `lake env lean docs/research/2026-10-10-goals-packet/codex/StackRegionAudit.lean`: passes.

Audit: 121 declarations within `[propext, Quot.sound]`, zero modulo planned goals, and zero planned goals.
The adjacent Atomic integration receipt retains the combined consumer build logs.
`StackRegionBuild.log` and `StackRegionAudit.out` retain this landing's final output.

New source lines, measured with `wc -l`:

| File | Before | After |
| --- | ---: | ---: |
| `src/Effect4/Laws/Machine/LiftPrefix.lean` | 0 | 59 |
| `src/Effect4/Laws/Program/StackRegion.lean` | 0 | 176 |
| `src/Effect4/Laws/Program/StackRegionCommands.lean` | 0 | 295 |
| `src/Effect4/Laws/Program/StackRegionRun.lean` | 0 | 100 |
| `Test/Program/StackRegion.lean` | 0 | 44 |

`src/Effect4/Laws.lean` imports the run reader.
`Test/All.lean` imports the boundary control.
This proof-only landing changes no runtime or generated output, so it owes no behavior gate.
The original scenario goals and the remaining base-law work continue.
