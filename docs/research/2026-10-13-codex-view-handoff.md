# The SVG kit and the view: status and hand-off to Codex on the PC (2026-10-13)

Status: hand-off note (history, not authority). Written by the Mac coordinator for Codex on the
PC. Effect4 base: `refactor/phase1-phase3` at this note's commit. Kit base: see §1.

## The one thing to know first

The kit (`lean4-whatwg`, branch `html/svg`) has two unmerged lines from `80bb06b` (S22), and
GitHub holds neither:

| Where | Head | What it adds | Ruling numbers |
| --- | --- | --- | --- |
| GitHub `origin/html/svg` | `80bb06b` | S22 up to units and the flow network (W18, W20) | up to R-S49 |
| PC `C:/Users/kokok/Dev/lean4-whatwg-svg`, branch `html/svg` | `59c59a1`, plus 16 uncommitted files | the ribbon and the vessel (W17, W22); the uncommitted S22 close (headers, `ARCHITECTURE.md`, `TrustConfig`) | R-S50 (ribbon), R-S51 (close, uncommitted) |
| Mac, now also on the PC as branch `mac/html-svg` | `e64e915` | S23 solid tubes, S24 one blend for every join, S25 cheap films and the light board (29 commits) | R-S50 (S23), R-S51 (S24), R-S52 (S25) |

The ruling numbers R-S50 and R-S51 collide. Effect4 pins `e64e915` (`lake-manifest.json`), which
GitHub does not have; §2 seeds it on the PC so `lake build` finds it.

## 1. What the coordinator synced to the PC

- Effect4: `C:/Users/kokok/Dev/lean4-effect4`, branch `refactor/phase1-phase3`, fast-forwarded
  from `6ad8f7b8d` to the Mac's head by a git bundle. Untracked `ocaml/link/` and `tools/viewer/`
  are untouched. Every note this file cites is tracked, so it came with the bundle.
- The kit: the Mac's `html/svg` fetched by bundle into the PC checkout as `mac/html-svg`. The
  checked-out `html/svg`, its working tree and its 16 uncommitted files are untouched.
- `C:/Users/kokok/Dev/lean4-effect4/.lake/packages/whatwg`: a clone of the PC kit checkout at
  `e64e915`, its `origin` set to GitHub's URL, so Lake accepts it.

## 2. The kit: where it stands

- S22 (PC): ribbon (`Geometry/Ribbon*`, W17), vessel (`Geometry/Vessel*`, W22), the S22 close
  uncommitted. Owed by R-S51 (c), the PC's numbering: moves of declarations to the modules they
  are about (debts D137, D143), among them `Monotone.rise_nonneg`, the `Distinct` instance,
  `Bracket.opening`/`closing`, sixteen token lemmas, twenty ribbon and vessel helper lemmas.
- S23 (Mac): solid tubes; `Html.Svg.cased`, `casedByUse`; the kit tube in exact `Rat`.
- S24 (Mac): one blend for every join; bulges as profiles (trapezoid spline, exact cubics),
  coalescence of two discs, the bend guard, graph edges as tubes, curvature combs.
- S25 (Mac): cheap films with exact moments (`Smil.filmShared`, 2.12 MB to 0.88 MB on the Queue
  film), `SvgBoard` (changes-only markings, phased cadence, a dash chaser).
- Open asks from Effect4 (`docs/research/2026-10-12-whatwg-requests.md`): W21 (a body along a
  path in one beat; a keyed join), W23–W29 (soft field, Vogel disc, Murray junction, Physarum,
  metal parts, kinematic pairs, rotation), W30–W33 (the tube form, cased layers, the SMIL
  writer, stroke changes), which wait for the decomposition pass. W17 and W22 close when the
  PC line merges.

## 3. Effect4's view: where it stands

- `tools/Tools/View/`: 48 modules, 15,168 lines; the tube language is `Tube/` (15 modules).
- Drivers: `lake exe view-pages` (`tools/Drivers/GlyphSheet.lean`), `lake exe view-live`
  (`tools/Drivers/Live.lean`), `tools/Drivers/{DocSpecimen,Site,View}.lean`; the shell tool
  `tools/view/v` (macOS viewer calls; on the PC, open the written pages directly).
- The pivot of decisions row 374: pegs and strings on a grid replace blended joins; motion is
  computed as a light board (rule 184 over bit strings) and drawn as fluid. The design is
  `docs/research/2026-10-13-tube-language/pegs.md`. Its port has six slices (§10 there):
  1. Belt: landed `25369c654` (`Tube/Belt.lean`; nothing imports it yet).
  2. Tour: skeletons, their Euler tour, the tuning fork, the vessel as a string round its slots.
  3. Light board: the observer of each control's marking change, the board as their fold.
  4. Glyphs on the grid: the 37 figures as tiles; the old outline code retired.
  5. Films: the Queue and the score as markings over still skeletons.
  6. Tiles: the program's picture as the tile algebra over `Eff`, with FORMAL's signature
     (`docs/research/2026-10-13-tube-algebra/`).
- Code the port retires as figures move (pegs.md §9): `Tube/Kit.lean`'s blends, the stretch
  shoulders, `Tube/Outline.lean`, and `7e39d2a62`'s pre-pivot surge and interrupt films.
- Never imported by another module (built by the `Tools` glob; check before you cut):
  `Tools.View.FlowOrder`, `FlowPath`, `LiveChecks`, `Tube.Belt`.
- Known duplicates (`docs/research/2026-10-11-view-model/README.md`): two `Frame`s, two `Key`
  aliases, `Live` naming both a tool and the API face, and a change type per level
  (`Edit.Delta`, `Retained.Patch`, `Motion.Join`, per-kind samplers).
- The motion plan (`docs/research/2026-10-13-motion-everywhere/README.md` §7): M1, M2, M5's
  first cut and M7's first two steps landed; M3, M4, M6, M8, M9, M10 open. The pegs pivot
  supersedes M7's blends.

## 4. The work, in order (the owner's steer of 2026-10-13)

The owner: focus on the pegs port; improve the code base; make the semantics firm; tidy and
clean up modules; share code; give proofs more expressive seams; speed; "really anything".

1. **Reconcile the kit.** On the PC, commit the uncommitted S22 close, merge `mac/html-svg`,
   and renumber the colliding rulings (recommended: S22 keeps R-S50 and R-S51; S23, S24 and S25
   become R-S52, R-S53, R-S54). Build and run the kit's trust gate. Pushing is the owner's.
2. **Re-pin Effect4** to the merged kit head in `lake-manifest.json` only, and check that
   `lake exe view-pages` writes the same pages, or name each change.
3. **The pegs port, slices 2 to 6**, each retiring the code it replaces in the same commit.
4. **Consolidation.** Move what belongs in the kit there (W30–W33), then delete Effect4's local
   copies; settle the duplicates of §3; do the kit's owed moves (D137, D143). One definition per
   idea; a second copy is a defect.
5. **Proof seams.** State each geometric law once, in the kit; let Effect4's view prove by it.
   Pegs.md §8 lists the laws to state.
6. **Speed.** Measure `view-pages` and the film sizes before and after each slice.

## 5. Boundaries

- Effect4: edit only `tools/Tools/View/**`, `tools/view/**`, the view drivers named in §3,
  `Test/Audit/GlyphControls.lean`, and notes under `docs/research/`. The view never bleeds into
  Effect semantics (the owner's rule, decisions row 362): no edits under `src/` or the rest of
  `Test/`. The light board's observer in the run loop waits for the coordinator; build the
  board from the journal and trace that the current APIs return.
- Never edit `lakefile.toml` or `docs/core/decisions.md`: propose rows in your receipt.
- Work on a branch from `refactor/phase1-phase3` (recommended `codex/pegs-port`); the Mac
  coordinator merges it. Commit by named paths. Never push without the owner's word.
- Follow each repository's `AGENTS.md`: the trust rules, the axiom gate at
  `[propext, Quot.sound]`, no `sorry`, `partial`, `native_decide`, `simp_all`, `first` or `try`.
- Leave a receipt: `docs/research/2026-10-13-codex-pegs-receipt.md` in Effect4, and the kit's
  rulings in its `COORDINATION.md`.

## 6. Questions still open for the owner

- Pegs.md §11: the grid step as one slot (12 px); structure changes glide while units hop; a
  fade of a fifth of a tick on the board.
- `docs/research/2026-10-13-organic-mechanical/README.md`: the rotation primitive (row 354), the
  rule "an invariant is metal; state is tissue", the metal look (ISO 128 flat or rendered).

## What this does not establish

No build ran on the PC for this note. The kit's merge is not attempted, and its conflicts are not
counted.
