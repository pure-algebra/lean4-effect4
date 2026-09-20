# Phase B changed-statement inventory

Base: `15cb510e2ea747364e1c814e3a92f1e1ac0075eb`. Working-tree HEAD: `15cb510e2ea747364e1c814e3a92f1e1ac0075eb`. Read-only source inspection; no Lean or search.

## Counts

- paths: 84
- changed: 151
- new: 34
- deleted: 26
- parser refusals: 0
- exact live: 138
- reviewed live: 13
- missing manual live: 32
- generated without manual ledger: 2
- exact snapshot: 156
- reviewed snapshot: 7
- missing snapshot: 22

## Exact live-ledger gaps

32 manually authored theorem statements have no matching or reviewed live Obligation: 26 changed, 6 new.

- `src/Effect4/Laws/Api/Supervision.lean`: `forkedOf_append` (changed, no pending snapshot found), `spawn_forked` (changed, no pending snapshot found), `start_forked` (changed, no pending snapshot found), `fork_forked` (changed, no pending snapshot found), `forkIn_forked` (changed, no pending snapshot found), `forkScoped_forked` (changed, no pending snapshot found), `forkScoped_none_forked` (changed, no pending snapshot found), `launchEntrant_forked` (changed, no pending snapshot found), `forkFinalizers_forked` (changed, no pending snapshot found), `action_fork_forked` (changed, no pending snapshot found), `action_forkIn_forked` (changed, no pending snapshot found), `action_forkScoped_forked` (changed, no pending snapshot found), `supervision_static` (changed, no pending snapshot found).
- `src/Effect4/Laws/Machine/Book.lean`: `fiberMeans_origin` (new, snapshot retained).
- `src/Effect4/Laws/Machine/Clauses.lean`: `spawn_eq` (changed, snapshot retained), `spawnChild_fields` (changed, snapshot retained), `spawn_untracked` (changed, snapshot retained), `drive_launch_runs` (changed, snapshot retained), `withFiber_fork` (changed, snapshot retained), `withFiber_forkIn` (changed, snapshot retained), `withFiber_forkScoped_ambient` (changed, snapshot retained), `withFiber_forkScoped_none` (changed, snapshot retained), `launchEntrant_eq` (changed, snapshot retained), `withFiber_raceAll` (changed, snapshot retained).
- `src/Effect4/Laws/Machine/CompletionData.lean`: `store_lookup_lt` (new, no pending snapshot found), `poll_reads_cell` (new, no pending snapshot found).
- `src/Effect4/Laws/Program/Simulation/Fibers.lean`: `FMeans.origin` (new, snapshot retained), `FMeans.mk'` (changed, snapshot retained), `fmeans_make` (changed, snapshot retained), `raceMeans_nextSite` (new, snapshot retained), `raceMeans_mk'` (changed, snapshot retained), `make_pending_empty` (new, no pending snapshot found).

## Covered statements with pending-snapshot gaps

- `Effect4.Machine.syncOpStep_clockNow` — Live obligation exists; no matching pending snapshot found in the scoped retained evidence tree.
- `Effect4.Program.Agreement.DeferredStore.complete_quiet` — Live M1Quiet.complete_quiet and #proof_wanted exist; no separately retained pending snapshot located in the scoped evidence tree.
- `Effect4.Program.Guard.NativeStateLinks.Links.beginRace` — guard-origin-pending/NativeStateLinks.lean has a site binder but its saved obligation target omits site in beginRace, fixing the default none. The live statement/gate include site. The retained snapshot is narrower than the final statement.
- `Effect4.Program.Sched.exit_completion_means` — Live obligation exists; no matching pending snapshot found in the scoped retained evidence tree.

## Important mappings

- `M1Quiet.complete_quiet` is live at Agreement/Machine.lean; its retained snapshot gap is separate from live-ledger coverage.
- `syncOpStep_memoComplete_some` maps to the corrective `MemoIdentityUpdateWanted.lean`, not the earlier narrower StoresLaws snapshot. The correction omits a saved wanted-marker line.
- All nine clock source-name/binder correspondences and all four Pending section/default-binder correspondences are explicit reviewed records in JSON. They are not counted as missing live obligations.
- The 13 Api.Supervision trace theorems now say `TraceFacts.forkedOf`; their renamed proposition heads still count as changed written statements and currently have no live ledger entries.
- Two newly generated `lift_ClockMillis` declarations (Api/Derived and Api/RunnerDerived) are recorded separately; no handwritten proof was added for them.

## Limits

- Compared explicit written theorem/lemma binders and result expressions; no Lean elaboration/search was run.
- Whitespace, comments and leading underscores on unused binder names are normalized; 13 separate reviewed mappings account for qualified names, implicit binders and section variables.
- An unchanged explicit header can still depend on a changed definition/section context; such transitive semantic changes are outside this header inventory.
- Snapshot existence records retained source, not chronology or proof completion. A source-name correspondence is not an elaborated proposition equality claim.
- Two new ClockMillis lifting theorems are producer-generated declarations, listed separately from the manual proof ledger.
- No live source or evidence files were changed by the inventory.
