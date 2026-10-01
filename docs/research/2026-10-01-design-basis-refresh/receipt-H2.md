# Seat H2 receipt: DB-16 re-read and the basis re-pinned at `6b3f2c92` (decisions row 154)

## The one thing first

The basis is now exact at `6b3f2c92`. Every citation, register id, DI number, source mark and the
seventeen rows' shape check there with 0 failures (tested).

DB-16 states the design as recorded:
- the `J`/`I` split keyed on `running` (row 134);
- frames and hook protocols closed under later worlds (row 135);
- the posts at the machine's answers, with the handler rule proved (row 136);
- `Fits` in the checker's order (row 137);
- scope presence as the one predicate `ScopeLive` (row 156).

Each repair names its tree witnesses at `6b3f2c92` with an evidence word. The formal pass's ports
at `dceae006` are replaced by the in-tree batteries.

Before merging, know two things:
- **The glossary.** System map §9 still says "Sites are at `dceae006`", and 19 of its line sites
  are wrong at `6b3f2c92`: 17 moved with their text unchanged, `TypedState`'s definition changed,
  and `CodeInert` no longer exists. The proposed lines are below; nothing was edited.
- **The re-pin moved what it claims.** Seven declared obligations remain declared. Since
  `6b3f2c92` the branch moved to `44a8551c` (one brief, no file the basis cites), so nothing
  drifts at the tip (tested).

## Base and head

- Base: `6b3f2c92` (`refactor/phase1-phase3` at dispatch).
- Worktree: `/Users/pooks/Dev/lean4-effect4-seat-H2`, branch `seat/H2`.
- Commits on `seat/H2`:
  - `780516bd`: the basis re-read and re-pinned, and the checker moved to `6b3f2c92`;
  - the commit that adds this receipt, which is the head at hand-back. Its hash is in the
    hand-back message.
- Nothing was pushed. No `git merge`, `checkout`, `reset` or `push` was run, and no permission
  was refused.

## Changed paths (against `6b3f2c92`)

| Path | Change |
| --- | --- |
| `docs/DESIGN-BASIS.md` | DB-16 re-read and rewritten against rows 134–137, 139, 156. Every line citation re-pinned. Reading guide, header and the seventeen status fields moved to `6b3f2c92`. DB-06's source mark corrected. One literature line updated. |
| `docs/research/2026-10-01-design-basis-refresh/check_citations.py` | `BASE` and `TRACK` moved to `6b3f2c92`. The branch head is a variable. The red controls are pinned to their own commits. Absence claims are read at the `BASE` in force. |
| `docs/research/2026-10-01-design-basis-refresh/receipt-H2.md` | New: this receipt. |

## (1) DB-16 against rows 134, 135, 136, 137, 139 and 156 as recorded at `6b3f2c92`

The rows' texts were read at `6b3f2c92` (reading); the tree's declarations were read at the lines
cited (reading, and the checker's pairs, tested). DB-16 now says:

- **Row 134, ruled and landed: the `J`/`I` split.** The old text called it ruled; now it says what
  landed.
  - `J` = `MachineTyped`: `TypedState`, the source's service table, `LiveCode` and `MachineLive`.
  - `I` = `ConfigTyped`: `J`, `ReadCode` and `QueueOk`.
  - Proved: `guarded_stepKeeps_of_stepPreserves` (`StepPreserves` over `I` is the lift's step
    premise), `evaluate_entry`, `machineTyped_of_configTyped`. `DecisionLift` is unchanged.
  - Tested: `machineTyped_m6`, `machineTyped_m9` and `running_exempt_at_m6`, beside the cut's
    refutations kept as history.
  - `decision_preserves` and `typedState_reachable` over `J` are declared.
- **Row 135, landed: frames closed under later worlds.** The old text said "not settled, row 135
  proposes".
  - The Kripke closure is in the definitions of `FrameAccepts`, the hook protocols and `HookLaws`.
  - Proved: `stackAccepts_mono`, `savedOk_mono` and `typedProg_mono`. The last closes
    `M3bWorld.typedProg_mono`, which DB-16 cites as declared, its statement the theorem's.
  - Tested: `bad_not_kripke_initial`, `stackAccepts_now`, `step_loop_good`, `output_not_kripke`
    and `hookLawsX_refused`, beside `stackAccepts_not_mono` and `step_loop_refuted` kept as history.
  - The probe witnesses `typedProg_mono_ledger`, `stackAcceptsK_mono` and `stackAcceptsK_now` are
    gone.
- **Row 136, landed: the posts at the machine's answers.**
  - The handler rule is proved for the store rows and per fiber frame: `storeStep_typed`,
    `answerFrame_typed`, `seqFrame_typed`, with `StoreTyped` and `StoreImplements`.
  - Each row's fulfilment is an instance in `M3bAdequacy`, proved or declared there.
  - Tested: the corpus program loads into `J` (`loadsTyped`, `AwaitLoad.lean`).
  - The close rows are rows 151 and 152 (`lone_release_outside_post`, `closeSeq_protocol_refused`,
    tested).
- **Row 137, ruled and landed: `Fits` in the checker's order.**
  - Every handle arm and protocol entry compares in `subN`.
  - Proved: `fits_normalize`, `fits_subN`, `fits_join_left`, `fits_join_right`, and `evalTerm_fits`
    (TY-07). These replace the types verifier's copies, `fitsN_*`.
  - Tested: `prog3_loads_typed`, `loadsTyped` and `capstone_at_load`, beside `m5_false` and
    `capstone_false` kept as history.
- **Row 139, landed in part: halting-freedom.**
  - Landed: `MachineLive`, `QueueOk`'s live link scope, the observer clauses' scope drops,
    `RegistrationState`, and the halting fiber rows' premises.
  - `close_code_refused_absent` is tested.
  - `M7.exitHandles_valid` is declared.
- **Row 156, landed: scope presence.**
  - `ScopeLive` is the one predicate, read by `HandleFits`' scope arm, the five scope-handle posts,
    the scope arms of `storePre`/`fiberPre` and `TypedProg.scopeExit`.
  - Proved: `scopeLive_mono` and `ambientScope_live`.
  - Tested: `makeThenClose_typed`, `forkAfterMake_typed` and `forkAfterMake_denotes`.
  - Owed: one definition shared by the machine stores' three spellings of presence (row 156).
- **The Decision field** now names what is:
  - ruled: rows 134 and 137;
  - landed with its ruling the row's own: rows 135, 136 and 156, and row 139 in part;
  - open: rows 151 and 152;
  - owed: the one definition of presence (row 156).

  The judgment, world and membership paragraphs gain the `scopeExit` arm's presence, `ScopeLive`'s
  persistence, the `subN` comparison and the closure laws.
- **Declared, not proved** (each a `ProofGraph.Obligation` at `6b3f2c92`, tested by the checker):
  `M3bWorld.typedProg_mono` (its statement proved by `typedProg_mono`), `denoteR_typed`,
  `typedState_load`, `step_loop`, `decision_preserves`, `typedState_reachable`,
  `exitHandles_valid`.
- **Refusals.** At `6b3f2c92` the register holds `E4-TYPED-CE-003`–`018` (all but `015`, which is
  DB-15's) and `E4-SCHED-CE-010`–`014`, `016`–`020`. The checker confirms each is a row.
- **Decisions rows.**
  - Ruled: 44, 45, 48, 96, 106, 107, 134, 137, 138 and 150. Row 150's `FoldLift` is now the tree's
    (`Laws/Machine/Lift.lean:363`), no longer seat F's probe.
  - Landed with their rulings their own: 135, 136, 156, and 139 in part.
  - Open: 87, 117, 140, 148, 151, 152 and 153.

  Status is each row's.
- **Sources** add receipts B, C, I and I2 and Codex's second-eyes review, all tracked.
- **Literature** adds the handler rule's premise (de Vilhena Def. 2.2 as the papers review's
  *Implements*, A2: read).

## (2) The re-pin

- **Mechanical, by text identity** (a scratch script over the checker's resolver, kept in the
  seat's scratchpad):
  - 70 tree line citations moved between `dceae006` and `6b3f2c92`. Each was mapped to the line
    holding the same text.
  - 33 `git:a561d604:` citations (seat E's landings) became tree paths at `6b3f2c92`.
  - 159 cited lines were unchanged.
  - Result: `mapped 103, unchanged 159, manual 4` (tested).
- **By hand: four citations whose text changed.** All are in DB-16 and were rewritten with the
  row:
  - `IteratorProtocol` and `LoopProtocol`, now indexed by the world (`Residual.lean:362`, `:380`);
  - `TypedState`, redefined (`Assembly.lean:147`);
  - `CodeInert`, gone (`LiveCode` `:217`, `ReadCode` `:227`).
- **Commit mentions.**
  - The reading guide states lines and decisions at `6b3f2c92`, and tracking at `6b3f2c92`.
  - Sixteen witness headers and seventeen status fields say "re-read at `6b3f2c92`".
  - "Proved in the tree at `a561d604`" becomes "since `a561d604`" (seat E's landings).
- **Dated claims re-tested at `6b3f2c92`:**
  - no `wp`/`wlp` declaration under `src/Effect4` (DB-06; `git grep`);
  - the vendored `Schema.ts` still hashes to `9358710e…` (DB-09; `shasum -a 256`);
  - `Lit.toVal` and `Val.hasTy` are where DB-15 says;
  - `Ty` has no record constructor yet (DB-15's "witness missing at `6b3f2c92`");
  - `build_total` is absent (DB-17).

  All were tested.
- **DB-06's source**, `docs/research/2026-09-05-reification-effhol.md`, has been tracked since
  `f8692389` (the coordinator force-added it). Its three marks now say tracked.
- **Literature names.** "Kripke names … the amended stacks" now reads "the saved stacks (closed
  under later worlds since row 135)".

## The checker's commands and output

All were run from `/Users/pooks/Dev/lean4-effect4-seat-H2`. `C` is
`python3 docs/research/2026-10-01-design-basis-refresh/check_citations.py`.

| Command | Exit | Output |
| --- | --- | --- |
| `C --self-test` | 0 | Structure control 3 of 3; drift control as expected (`Provision.lean:69 -> 71` at `efcf1ae2`, 1 unchanged); red control 17 of 17, 1 obligation, 0 green failures (tested). The fixtures run at their own commits (`dceae006`, `efcf1ae2`, `621c2210`). Before this pass they read tracking at `HEAD`, and the coordinator's force-add of the reification note broke a green line; that is fixed. |
| `C` (stated commit `6b3f2c92`) | 0 | 542 file citations, 85 commits, 5 digests, 9 tags, 1026 identifiers, 343 witness pairs, 0 "witness missing" claims, 82 source marks, 59 register ids, 11 fallback ids, 30 DI numbers, 6 external pins: **0 failures**. 7 witnesses are declared obligations, each called declared in the text. History appendix: 1 STALE, `read_print_native`, kept as written. Structure: 17 rows, 0 failures. |
| `C --drift 6b3f2c92` (before the re-pin, `BASE` `dceae006`) | 0 | 74 line citations moved or changed, 35 unchanged; 4 with changed text. |
| `C --base dceae006 --drift 6b3f2c92 <system map §9>` | 0 | 12 moved or changed that the checker's short-path resolver reaches. The seat's §9 script, which resolves the map's `src/Effect4/`-relative paths and its bare `:n` continuations, finds 19 (below). |
| `C --drift 44a8551c` | 0 | 0 line citations moved: the one commit since the base changes no file the basis cites (tested). |
| `git merge-tree --trivial-merge 6b3f2c92 44a8551c 780516bd` | 0 | No path changed on both sides, 0 conflict markers (tested; this mode writes nothing). |

There is no axiom output. No Lean file was added or changed and nothing was built.

## (3) System map §9: sites that moved, as proposed lines (not edited)

§9 says "Sites are at `dceae006`". At `6b3f2c92`, with the text identical at the new line unless
noted (tested):

| Glossary row | Site at `dceae006` | At `6b3f2c92` |
| --- | --- | --- |
| `CTy` | the join laws `Laws/Program/TypeAlgebra.lean:1096-1121` | `:1271-1296` |
| `Fits` | `Laws/Program/Typed/Membership.lean:87` | `:98` |
| `World` | `Typed.mono` (`Laws/Effects/Protocol.lean:57`) | `:68` |
| `TypedProg` | `Typed/Residual.lean:186` | `:248` |
| `ExitOk`, `NoShapeDefect` | `Typed/Admission.lean:30`, `:23` | `:31`, `:24` |
| `FrameAccepts`, `StackAccepts`, `SavedOk` | `Typed/Contracts.lean:32`, `:51`, `:67` | `:43`, `:66`, `:82` |
| the same row | `popR_typed` (`Typed/Stack.lean:133`) | `:142` (the proved theorem; `:430` is the ledger goal `M4Stack.popR_typed`) |
| `TypedState` | `Typed/Assembly.lean:123` | `:147`, text changed: it reads no queue and no current code (row 134) |
| `CodeInert` | `Typed/Assembly.lean:84` | gone; row 134's code clauses are `LiveCode` (`:217`) and `ReadCode` (`:227`) |
| `denoteR` | `denoteR_straight` (`:1380`) | `:1385` |
| `iter`, `denoteB` | `Laws/Program/Iter.lean:30` | `:32` |
| the lifts | `replayEval_lift` (`Laws/Machine/Lift.lean:638`) | `:731` |
| provision and layers | `build` (`Program/Provision.lean:297`), `satisfies_iff_subset_keysRow` (`:168`) | `:322`, `:193` |
| `Session` | `advance_step` (`Laws/Run.lean:791`), `open_total` (`:230`) | `:792`, `:231` |

Proposed for the intro sentence: "Sites are at `6b3f2c92`", once the moves are applied.

Found in passing: §9 cells the landings made stale (reading; each site tested at `6b3f2c92`):
- **`subN`** is named now: `Ty.subN` (`Laws/Program/TypeAlgebra.lean:1067`), and `subN_equiv_iff`
  (`:1088`) is in the tree, not a probe.
- **`inhabited`** has landed (row 127): `Program/Admission.lean:79`; `inhabited_of_fits` and
  `inhabited_of_hasTy` are in the tree (`Laws/Program/Typed/Membership.lean:2188`, `:2224`), not
  probes.
- **Σ_app, `RowTable`.** "Owed: C1–C8 (rows 111–116)" is out of date: rows 111–116 have landed
  (`SigApp`, `Laws/Program/Signature.lean:264`; `SigExtends` `:78`; `check_ext` `:223`;
  `check_restrict` `:876`; `LawfulSig` `:1073`).
- **`TypedProg`.** `typedProg_mono` is proved (`Typed/Residual.lean:686`), not a probe.
- **`FrameAccepts`, `StackAccepts`, `SavedOk`.** "Typed at one world today; Kripke closure owed
  (F3)" is out of date: they are closed under later worlds since row 135 (`stackAccepts_mono`,
  `savedOk_mono`, `Typed/Contracts.lean:131`, `:139`). `stackAccepts_append` and
  `stackAccepts_split` are in the tree (`:154`, `:162`).
- **`TypedState`.** Name the split: `J` = `MachineTyped` (`Typed/Assembly.lean:257`), `I` =
  `ConfigTyped` (`:269`).
- **`CodeInert`.** Replace the row by the split's code clauses (above). `m9_root_inert` and
  `running_exempt_at_m6` are batteries now
  (`Test/Counterexamples/Machine/Semantics/StaleCode.lean:299`, `:387`).

## Lines proposed for the coordinator's files

1. **`docs/core/system-map.md` §9**: the table and the stale cells above.
2. **`docs/core/decisions.md` row 154.** Its status becomes "landed 2026-10-01 (seat H2, `780516bd`,
   receipt `docs/research/2026-10-01-design-basis-refresh/receipt-H2.md`): DB-16 re-read against
   rows 134–137, 139, 156; the basis exact at `6b3f2c92`".
3. **`docs/STATE.md`**: one line that the basis is exact at `6b3f2c92` (row 154 closed).
4. **A future re-pin**, after wave 2. Run `C --drift <rev>` and move the stated commit as here.
   The red controls no longer move with it.

## What remains

- **The history appendix**, kept as written: one STALE name, `read_print_native`.
- **The seven declared obligations above**, and rows 151–153 open.
- **One owed definition**: the machine stores' one spelling of presence (row 156).
- **System map §9's sites**, until the coordinator applies the lines above.

## Bounds

- **No build and no kernel check by this seat.** "Proved" means a theorem declared in the tree
  whose statement was re-read at `6b3f2c92`. The kernel check is the trust gate's, not rerun
  (assumed from the gate).
- **The re-pin matches by text identity.** A line found at a new position has the same text. The
  four whose text changed were re-read by hand.
- **The identifier check shows existence, and a witness pair shows the name on the cited line.**
- **The §9 report reads the map's paths** as `src/Effect4/`-relative. Bare `:n` continuations take
  the last path in the row. Sites without a line are checked only for existence.
- **No host evidence** was used.
