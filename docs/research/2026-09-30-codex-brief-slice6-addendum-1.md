# Addendum 1 to the slice 6 brief: items A–C after the design pass

Written 2026-09-30, after the design pass finished
([synthesis](2026-09-30-pass/synthesis.md) §§3.6, 4 K2–K4, 6 step 0). Read it with the
[brief](2026-09-30-codex-brief-slice6-and-fixes.md); where the two differ, this addendum wins.
Each change below was checked against the tree by the coordinator.

**The one thing first.** In item A, the fixture row `"cell"` and one guard change on purpose: do
not stop for them. The failure part of item A's step 2 is withdrawn, because a failure cannot
carry a handle.

## Item A

1. **The fixture row `"cell"` is expected to fall under the rule.**
   - `Test/Api/ExternalContract.lean:15` defines a row answering `NativeOp.refTy`, a cell. The
     table rule refuses it, and that is the rule working, not a stop.
   - Keep the row. Add a guard that `admitProgram` refuses this table at the row's located path.
   - Step 2 also changes the guard at `:55-57`: the dead cell answered at that row is now refused
     earlier, as `.answerType Api.root 0 NativeOp.refTy`, not `.deadHandle Api.root 0`. Update
     the guard and say so in the receipt. The synthesis checked this on a copy, with a failing
     control (Appendix A).
   - Keep `Refusal.deadHandle` as a constructor; the parked registry will need it.
   - Host-returned internal cells wait for that registry (row 7's authority question).
2. **The failure arms do not change.**
   - `Err` is a closed alphabet (`Machine/Alphabets.lean:34`: `boom`, `tag`, `tagged`, `text`).
   - Every decoded error image is handle-free (`valOfErr_keys`, `Laws/Program/Admit.lean:304`;
     `causeImage_handleFree`, `Machine/Alphabets.lean:183`).
   - So `admitAnswer` and `externalAdmits` keep their failure arms as they are. The guarantee
     theorem covers failures by citing those two lemmas: an accepted reply, success or failure,
     carries no internal handle.
   - Drop the `unknown`-error control; it cannot be built. Keep the `unknown`-answer control.
3. **The engine's closure.** The fiber-slice verifier found that the engine calls a
   specialization of `replayCheckedFrom` by name. Item A does not change `replayCheckedFrom`. If
   your change reaches it anyway, run the `lcnf` byte check and `dune build`.

## Item B

The pass refutes the answer-free capstone on programs with no host at all. So the restriction is
necessary, but it does not repair M6.
1. Register `E4-SCHED-CE-015` as REPAIRED **for host answers only**, and say so in its repair
   column.
2. **The capstone's docstring** says three things:
   - it counts tapes with no host answer;
   - it remains refuted on host-free programs, by the four ids below;
   - M6 does not yet claim that a run never dies with `badName`, `notImplemented` or
     `missingService` when nothing is required. The pass shows that the exit clause admits those
     defects at every type (`strongExit_of_dies`). Whether to add a clause that refuses them is
     an open owner decision.
3. **Add four SEEDED lines to `Test/Counterexamples/REGISTER.md`.** Their witnesses stay in the
   pass folder, which the coordinator has committed. Each moves into `Test/` with its repair.

| id | claim refuted | witness (under `docs/research/2026-09-30-pass/`) |
| --- | --- | --- |
| `E4-PROV-CE-005` | a layer's effect body runs in the environment it was checked in | `registry/LayerGap.lean`: `errLeak_checked`, `errLeak_native_exit`, `errLeak_reference_exit`; `registry/verify-Gaps.lean`: `discardLeak_native_exit`, `crash1`, `errLeak_admitted`. Checked at `(nat, string)`, `errLeak` fails with `9` on both machines. The body is checked at `[]` but built at `p.child 0`, which keeps the enclosing environment (`Program/Compile.lean:766-781`). |
| `E4-PROV-CE-006` | a layer's value fits its key's service type | `registry/LayerGap.lean`: `valueLeak_*`, `succeedLeak_*`; `crash2`. `LayerHasTy.succeed` says "the value's type plays no part" (`Laws/Program/Typing/HasTy.lean:414-418`); the pinned `tsgo` refuses the printed TypeScript. |
| `E4-TYPED-CE-004` | `typedState_load` (M5) holds for checked programs | `membership/Gaps.lean`: `typedState_load_false` at `Ref.make(5)`; `membership/verify-load.lean`: `typedState_load_refuted`, `restricted_capstone_refuted`; `membership/verify-step.lean`: `step_loop_refuted`. The value judgment reads liveness from store lengths, which `storePost` never provides. |
| `E4-SCHED-CE-016` | M6's queue fact types every queued resume | `lift/verify-decision.lean`, `lift/verify-steppreserves.lean`: `load_and_fire_inconsistent`, `load_and_five_inconsistent`. A queued resume for a token not yet allocated counts as typed. The refutation is conditional on M5 at `perform sleep 1`. |

Add no Test files for these four; their repairs are later slices.

## Item C

1. **Make a missing site a compile error.**
   - Remove the eight `site : List Nat := []` defaults in `Machine/Fibers.lean`: the three
     `FiberAction` constructors (`:304`, `:308`, `:310`), `spawn` (`:926`), `launchEntrant`
     (`:957`) and the three fork steps (`:1428`, `:1440`, `:1451`).
   - Pass `[]` explicitly where the empty site is meant: finalizer forks and races without a
     source site.
   - Laws whose binders mirror these defaults may keep them.
   - If more than about twenty call sites outside `Machine/` and `Program/Compile.lean` break,
     keep the defaults instead and list those callers in the receipt.
2. **Layer builds are a third internal fork kind.** A `merge`/`mergeAll` layer build forks through
   the `fork` arm with the layer's own path (`Program/Compile.lean:1453-1455`). Add a
   `merge`/`mergeAll` fixture to the comparison runner's list.
3. **Add no `kind` field.** The registry is parked, and it comes back with it.
4. **Support for the reader switch.** The pass proved that the reference machine records the same
   origin for every fiber, on every tape, at the empty table (`origin_eq_ref`,
   `registry/verify-Origins.lean`). The `FMeans` readers can lean on it when they move.

## Items D and E

They are not dispatched yet. The pass changed both:
- **D.** The generic lifts are proved, but they do not yet give M6. Its statement needs four more
  repairs first.
- **E.** The membership judgment must read liveness from the world's tables; without that, M5 is
  false.

Addendum 2 will follow the owner's rulings on those repairs.
