# Pool design and machine-control follow-through

Role: advisory review. Evidence: committed design, frozen active source and retained seat results.
Main at the opening snapshot is `601ed7c5830d22154fdd68e0b7e062c67407b9dc`, clean.
POOL begins at `685d60f433586c3079e63f224dd201c7821f46f9` with the scenario file and its import active.
The closing seat commit is `af7f6099be28021e67408245120652c056f33556`, clean.
The two reviewed active files match that closing commit byte for byte.
No monitor repository change, build, compiler, runtime, generator, installation or UI action occurs.

## Result

No new actionable semantic defect was found in this bounded review.
The committed design takes the accepted `borrowed` flag and latest lease stamp representation.
The saved seat notes explicitly restrict the stamp's meaning to a borrowed item.
The earlier optional-stamp suggestion is consumed; this review does not reopen that choice.
The design adopts the three shared Nat equality rules at their allocated files.
Its selection remains `take` and `drop`, with no new fold or table.

The source is `docs/research/2026-10-06-seat-POOL-design.md`.
The checked machine programs are test fixtures in `Test/Program/PoolScenarios.lean`.
The library model, generic proofs and public operations remain later work.
The fixtures initialize an already acquired resource list before any borrower begins.
They do not test failed eager acquisition or implement the public `make`.

## Scope of the retained controls

| Control | What the source and saved output establish on one schedule |
| --- | --- |
| PP1 | Two borrowers reuse one resource; its scope finalizer runs after both returns |
| PP2 | Returning A then B puts B's item first; the FIFO mutation changes the next two borrowers |
| PP3 | A return leaves an idle item beside enrolled waiters; each posted helper has count 1 |
| PP4 | Cancellation before helper execution removes A; selection reads the current cell and serves B |
| PP8 | A waiting borrower's interruption removes its registration; a later return owes no wake |
| PP5 public | Count 1 selects A; the intermediate snapshot is idle=1, borrowed=0, waiters=0; A subsequently leases |
| PP5 lower-level | A constructed open state has an idle item and two waiters; one count-2 helper selects both in order |
| C1 | The first close step refuses future leases and counts waiters; it does not prove completion of a waiting close |
| Stale lease | Lease 0 returns; lease 1 begins; another return of lease 0 refuses and leaves the entire snapshot unchanged |

The public count-1 case and the constructed count-2 case are separately named and documented.
No public open-pool operation posts count 2 in this profile.
The handover mutation changes the public intermediate snapshot before notification.
Its lower-level counterpart gives two borrowers one lease, which the retained control rejects.
Selection at posting time instead of execution time fails PP4.
A return that finalizes the resource fails PP1.

`useWith` uses one outer saved-state mask around acquiring the lease and installing its return hook.
It restores the body only inside `onExitWith`.
The fixtures reuse `waitAt`, `posted` and the current mask builder.
They do not use `waitRetry`; the already consumed note records why its mask boundary does not fit this protected body.
No new wrapper implementation is proposed here.

## Actual saved evidence

`evidence/public-command-results.json` retains only public tool commands and their results from the POOL transcript.
Probe1 prints the expected typing checks and the cell/lease answer types.
An initial Probe2 diagnostics printer fails to synthesize `Repr`; the seat repairs that printer before its successful finite observations.
This intermediate printer failure is resolved and is not a Pool acceptance failure.
Probe3 prints fourteen built programs and named positive and mutation observations.
Its stale-lease output explicitly contains the false return answer and equal before/after snapshots.

The final scenario-file command uses `lake env lean -M6144 -DwarningAsError=true Test/Program/PoolScenarios.lean` through the seat's slot script.
Its retained output contains no diagnostic, followed by its timing.
That command pipes through `cut` and `head`, so its shell pipeline alone does not certify Lean's exit status.
The subsequent saved build does give `exit=0` and `Build completed successfully (991 jobs)`.
It reports building `Test.Program.PoolScenarios` and `Test`.
The saved gate reports 741 modules and 87,857 declarations, with 24 planned goals and 11 declarations resting on goals.
These are the seat's results; the monitor does not rerun them.

The frozen fixture matches closing commit `af7f6099`.
`integration-byte-check.json` records that check for the fixture and `Test/All.lean`.
`check-retained.py` performs eight consistency checks of the saved Probe3 output.
Those checks parse retained observations; they do not execute Lean or Pool.
The record keeps the initial prefix and final version of the build log separately.

## Next proof detail worth retaining

The existing brief already assigns the profile closure, return and selection statements.
No new proof task is needed before those statements are worked.
Two details should remain explicit in their current statements.

**Resource values do not identify items.** Keep `res : Nat → Val` unrestricted by injectivity in the reading relation.
The design explicitly permits two items to hold equal resource values.
A lease is identified by item stamp and lease stamp; request-handle injectivity applies only to request equality.
The existing `Table.Injective` says nothing about the resource map.
Queue's `cellVal` already accepts an unrestricted value map in `src/Effect4/Laws/Modules/Queue/Relation.lean`.

The proposed return law's frame is exact: if no borrowed item matches both stamps, `giveBack` returns false and keeps the state.
Its consumer is the proposed `pool-lease-return`, concept `scope-lifetime-finalization`, R11, through the atomic return step.
The reading connector serves `pool-expansion-agrees`, `translation-simulation`, R10; membership remains R4.
Premises are the chosen cell relation and profile, including distinct item stamps and current lease stamps below `next`.
The observation includes the whole cell and reply, not only resource values or the available-list length.
The immediate prerequisite is the model's placed return statement.
No claim follows about cancellation, cleanup completion, the whole close, fairness, or liveness.

For a future compact control, use two distinct item stamps with the same resource value.
Both may be borrowed simultaneously, and returning one must leave the other's lease intact.
The current `oneBorrower` helper groups log rows by resource payload; it is suitable only for the current distinct-payload scenarios.
Do not promote that log helper to the general item-identity property.
This is an observation-domain reminder, not a defect in the current finite cases.

**Reuse the already chosen fold facts.** `heldBy` folds Boolean disjunction; `freed` maps item records while preserving the list.
The current design's `foldl_or_any` and `foldl_snoc_map` are the appropriate existing helpers in `src/Effect4/Data/Constructive.lean`.
The source-term reading and typing remain separate, with `Captured` and `CapturedTy` where caller terms enter fold bodies.
`step_updates` connects exact reading to one store operation; `step_keeps_cell` establishes reply and stored-value membership under its typing premises.
Neither connector establishes that the profile is closed or that a waiter eventually receives an item.

No new advisory is required while the seat follows these already assigned obligations.
