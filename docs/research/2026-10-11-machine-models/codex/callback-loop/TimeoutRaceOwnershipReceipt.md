# Actual Timeout race ownership

The original retry and cleanup goals remain open.
This slice assigns a child only when its actual accepted-none launch runs.
Race entry allocates bookkeeping and launches no child.
Early acceptance leaves every later head unlaunched.

## Placement

Concept: scope-lifetime-finalization R11 and translation-simulation R10.
Question: Timeout.cleanup_keeps and Timeout.retries_declared in Test/Dogfood/Scenario/Timeout.lean.
Consumer: the joint current-frame, saved-callback and generation assertion, then the existing command and decision transport.
Reach: actual source action, captured environment, race lookup, program head, acceptance verdict and fresh child lookup.
The local producers establish no reached assertion, cleanup completion, retry permission or public-cut budget room.

## Shared producers

NativeConfiguration.configuration_begin_race_programs replaces configuration_begin_race's old body.
Its result retains the actual owner, token, unlaunched programs and parameterized program permission.
The old theorem is its lexical projection.

NativeEvaluation.begin_race_programs couples that evidence to the actual returned evaluation.
The old begin_race_at theorem is its projection.
NativeActions.with_fiber_first_race_programs couples the actual first-exit action to that result.
The existing action analysis consumes these producers without a second action traversal.

Clauses.driveStep_launch_runs retains the actual accepted-none launch's whole machine and command pair.
It remains generic in the evaluator and existing frame carrier.
Clauses.driveStep_launch_accepted records the unchanged machine for an accepted race with an unlaunched head.
Both are direct shared clause equations.
They add no command classification.

TimeoutRaceOwnership.race_entry combines the exact child-source witness with the captured generation permission.
It retains the ordered source program list and unchanged fiber table and id counter.
TimeoutRaceOwnership.launch_entry reads the actual head, shared launch equation and Guard's fresh lookup.
It assigns that child its source permission before evaluation.
TimeoutRaceOwnership.launch_accepted consumes the shared accepted-head identity equation.
It grants no child role.

## Files and evidence

The patch is /private/tmp/timeout-race-ownership-shared.patch.
Its SHA256 is dfbb49960627ffcfedd168afa413845ed65663e72f0439d3975d095f326f497b.
The compared root checkpoint is ae30ab96c06f77a917eba727ae218e08aa3aa846.
The assigned worktree remains unchanged by this private slice.

The patch contains NativeConfiguration, NativeEvaluation, NativeActions and Clauses only.
Forty-seven existing theorem headers remain unchanged in the three source transport modules.
The Clauses patch inserts a scoped generic block and retains every existing source byte.
The header inventory and dependency hashes are retained in timeout-race-ownership-header-inventory.txt and timeout-race-ownership-hashes.txt.

NativeConfiguration changes from 265 to 282 lines.
NativeEvaluation changes from 380 to 397 lines.
NativeActions changes from 121 to 140 lines.
Clauses gains 32 lines.
The sole old race allocation membership proof moves into the stronger producer.
The old adapters discard additional evidence.

Each source module passes an isolated one-thread Lean check with warnings as errors.
The exact shared clause bodies pass as RaceLaunchClauseProbe.lean.
The full candidate Clauses bank awaits the coordinator's integration build against R1.
The concrete numeric ownership readers pass TimeoutRaceOwnershipProbe.lean.

The audit runner is /private/tmp/TimeoutRaceOwnershipAudit.lean.
The result is /private/tmp/timeout-race-ownership-audit.log.
It audits the three source modules, exact shared clause probe and numeric ownership probe.
Result: 253 declarations within [propext, Quot.sound], zero goals, zero declarations modulo goals.

The immutable numeric snapshot is /private/tmp/TimeoutRaceOwnershipAccepted.lean.
Its SHA256 is 297ae8586c71f43d04923919a9f1b25d51e5a24518c7fd09dbc6f4f951c103b9.
The immutable shared clause snapshot is /private/tmp/RaceLaunchClausesAccepted.lean.
Its SHA256 is 6e8989b04f59ef5c247ab55b746fe5494bc8b1943d35dd446b880bb33a62520a.
The numeric snapshot imports the checked clause probe.
The coordinator's production reader replaces that import with the shared Clauses bank after integration.
This one import migration must remain explicit in its acceptance receipt.

## Remaining obligations

The waiting root must retain the actual generation and partially assigned child roles through registration and cancellation.
An attempt winner needs its actual published cleanup exit.
A timer winner needs a completed loser join containing the assigned attempt.
A timer-only join grants no cleanup permission.
Persistent cleanup evidence comes from the actual source write.
Reference equality and structural answer labels grant no phase permission.

The exposed public cut must supply remaining budget for the count prefix.
An unfinished frontier remains live and can retain command residue.
The native charge facts alone establish no four-command room.
Use the existing StackRegion and LiftPrefix connection under the actual 2000-command and 4000-compilation budgets.
No executable code changes; no behaviour gate is reached by this proof-only slice.
