# Seat F brief: the instrument, the registers, the imports and the record

Written 2026-10-01 by the coordinator. Base: `dceae006` on `refactor/phase1-phase3`. Worktree
`/Users/pooks/Dev/lean4-effect4-seat-F`, branch `seat/F` (created; `.lake` current). Read
`docs/research/2026-10-01-landing/plan.md` (§1 choices O5 and O8, §2 the register ids, §4 rules)
first. The pass's organization seat is
`/Users/pooks/Dev/lean4-effect4/docs/research/2026-10-01-formal-pass/organization/` (`note.md`
§§1.6, 2.5, 3.5, 4.4, 4.6, 5.1 are its action lists; `verify.md` §2 is the verdict table, §3
"what the seat missed", M1–M8); read both before acting, and act on every item whose verdict is
confirmed or partly and whose file is in your scope below. Never edit or build in the main
checkout or another worktree.

**The one thing.** The tree's formal structure is where the map says; the record and the
instruments that measure it have drifted. You make the instrument honest, the registers exact,
the core root free of the `Effects` package, and the stale pointers true, each as a small commit
by explicit paths, with the measured before/after numbers in the receipt.

## In scope (files you edit)

1. **The traversal census instrument** (`src/Effect4/Laws/Auto/Traversals.lean`; the verifier's
   `verify-CensusWfBlindSpot`, `verify-CensusPrivate`, `verify-SparseShape`,
   `verify-CensusConsistency` under the organization folder say exactly what it misses): class a
   row `wf` when its value calls a `_unary`/`_mutual` helper whose value reaches `WellFounded.fix`
   or `WellFounded.Nat.fix`; count private definitions; recognise one-level matches compiled
   through a shared sparse `casesOn` helper. Red controls as `Test/` fixtures: `Ty.sub` (wf),
   `Codegen.Types.ofNormalized` (private), `Ty.isFactor` and `Ty.closed` (sparse one-level
   match). Then rerun `#traversal_census` and put the new counts, per family, in the receipt and
   in `docs/core/traversal-census.md` §1 (say whether a one-level match counts, and why), §7.4
   (the named exemptions: the five `Ty` template-calculus traversals, `Ty.sub`, the three private
   traversals), the "16 constructors" at `:72` and the §7.9 count. That document is yours for
   this item only.
2. **`src/Effect4/Machine/Context.lean`** (organization §3.5 M5): move the unused
   `Effects`-based service-program model (about 150 lines) out of the core root, to `Laws` if a
   theorem reads it, else delete it; keep `Requirement`, `Satisfies`, `keysRow`; fix the stale
   header (`:7-12`). Afterwards the core root's import closure reaches no `Effects` module: show
   it with the library-root gate's output (`lake env lean -DwarningAsError=true Test/All.lean`)
   and `git grep '^import Effects' src/Effect4` restricted to the core root.
3. **Guard tidiness** (`src/Effect4/Laws/Program/Guard/`): M1, `Single.lean`'s `held_driveState`
   through `driveState_lift_unit` (the proved form is in `organization/probes/GuardLiftRedundancy.lean`);
   M2, probe whether one `DecisionLift` instance for `Held` and one for `Preserved` replace the six
   decision-level hand inductions in `Single.lean`, `OuterDriver.lean` and `Decision.lean`
   (`:113,202,238,277,358,478`; `:102,172,279`; `:69`): land it if it closes with the existing
   lift, else record the exact obstacle (the verifier says the `interrupt` field may fail for
   `Held`); M3, lower the twelve slack `ceiling`s to their measured open counts (0 where the
   verifier found 0 open; `organization/verify-ledger-reports.py` lists them); move `foldl_lift`
   from `Guard/Core.lean:62` to `src/Effect4/Laws/Machine/Lift.lean` beside the other lifts (keep
   a one-line alias in `Guard/Core.lean` only if a caller outside Guard would otherwise break).
4. **`ExitOk`'s two meanings** (plan O5): rename `Effect4.Program.Denote.ExitOk`
   (`src/Effect4/Laws/Program/MeaningSound.lean:324` and its 27 uses in 3 modules; the typed-state
   `ExitOk` of `Laws/Program/Typed/Admission.lean` keeps the name) to `Denote.ExitHasTy`; then land
   the connector `exitOk_of_fitsExit` with its two red controls (`redA_scope`, `redB_external`,
   proved in `organization/verify-ExitOkConnector.lean`) as a new
   `src/Effect4/Laws/Program/Typed/ExitConnector.lean` imported from `Laws.lean` beside the typed
   modules, docstring naming the two premises and why each is necessary.
5. **`Test/Counterexamples/REGISTER.md`**: add the seven rows of plan §2 (SEEDED 2026-10-01, the
   witness paths as given, "repaired by" the seat named); add the DI-67 row the data probe's row
   127 said to register (`E4-TYPED-CE-015`, witness in `docs/research/2026-10-01-data-probe/`:
   find the probe that admits `prod never nat` and `except never never`); refresh the header's
   counts (`:8`); define REPAIRED and RETIRED in the header; note the four ids that exist in both
   the live and the archived register (TYPED-003, SCHED-004, PROV-005, PROV-006) with no
   renumbering.
6. **Contract packets** (`Test/contracts/`): the citations of deleted falsifiers in
   `environment-context-key.contract.md:517,525` (`scripts/test-trust-gate.sh`, deleted
   2026-09-19), `faces.contract.md:28` (`Wire.lean` moved 2026-09-20),
   `schema-payload.contract.md:89,180,404` (`scripts/check-schema-fields.sh`, deleted 2026-09-13):
   pin each to `git:<last commit holding it>:<path>`, never invent; `schema-codec` and
   `schema-recursor` cite counterexamples row 39 moved to the archive: point at the archive
   register. `Test/Schema/SubAlphabetContract.lean:97-98`'s stale baseline claim (ORG-24): correct
   the comment. `Test/contracts/README.md` if a packet moves.
7. **`docs/GENERATED.md`** (organization §2.5.1): the derived row cites the manifest's groups by
   reference ("every group of `tools/Effect4Gen/manifest.json`") instead of a hand list; fix the
   `Store/Derived` path; a `variances` row; a line for the promoted projections and `tsdiag`; drop
   "the compatibility snapshot" at `:89`. If `tools/Tools/Architecture.lean` can read
   `GEN_GROUPS` and the manifest in a few lines so the map stops copying a hand table, do it and
   regenerate nothing (the coordinator regenerates the map at the merge).
8. **`docs/DESIGN-ISSUES.md:51-66`**: rename the obligation kinds K1–K5 to O1–O6 (and every use
   of them in that file), so "K1–K5" means the arrow kinds of the system map only. No ruling
   changes.
9. **The untracked rulings** (organization §4.4; ORG-27: eighteen notes cited by tracked
   authorities, seventeen on disk): `git add -f` each cited note that exists, by explicit path,
   content unchanged; list the one that does not exist with the authority that cites it. The
   DESIGN-BASIS refresh seat force-adds eight of them in parallel; adding the same file with the
   same content on two branches merges clean.
10. **Stale texts** the pass found in files no other seat owns (organization §4.3; algebra
    verify "stale texts"): correct in place and list each in the receipt. Files owned by seats A,
    B, C (`Laws/Program/Typed/{Membership,Residual,Contracts,Stack,Assembly,Sources,Scheduler,
    World}.lean`, `Program/Admission.lean`, `TypeAlgebra.lean`) are not yours: list their lines
    for the coordinator instead.

## Out of scope (propose lines in the receipt; the coordinator applies)

`docs/core/decisions.md` (rows for the foreign-reader domain statement, `composeAt`'s laws,
"observation finality is not claimed", R5's `build_total` and `lower_refines_build`, row 2's status
after row 119, row 129's additions), `docs/STATE.md:280-305` (the pointer to the register),
`docs/core/system-map.md` (§2 status column against §8; K4's row; the three senses of
"signature"), `AGENTS.md` (the authority map lines; line 21; lines 73-80 per row 128), the
coherence principle and the census banners (plan O8), the glossary (O7).

## Checks

Narrow builds after each code change (`LEAN_NUM_THREADS=4 lake build <modules>`); the census
fixtures and `Test/All.lean` by `lake env lean -DwarningAsError=true`; after the Context and
Guard changes, `lake build Effect4 Effect4.Laws Test.Audit.AxiomGate`. At the end `lake build
Effect4.Laws Test.All` once. `#print axioms` for every theorem landed or moved. No generator;
no `make check`.

## Receipt

`docs/research/2026-10-01-landing/receipt-F.md` in your worktree (force-added): the one thing
first; base and head; every changed path; per item the before/after measurement (census counts
per family, the `Effects` closure, the ceilings, the rename's declaration count), the exact
commands and results, axiom lines; the obstacles; the proposed lines for the coordinator's files.
