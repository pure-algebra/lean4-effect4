# 2026-10-13 seat glyphs receipt: the vocabulary of marks as tubes

**The one thing to know before merging:** the 37 figures are data drawn through `Draw`. Each
names its solid joins, reducers and struts (`Figure.joins`, `reducers`, `struts` in
`tools/Tools/View/Tube/Glyphs.lean`). Map them to the pen's `Join`, `into` or `reducedOf`, and a
strut's fill at the merge, or the joins stay plain overlaps.

Every piece already keeps the pen's 24 px bend (a guard). The merge's build proves `figure_ok`
again by `decide` under the pen's `BEND`.

## Base and head

- Branch: `worktree-agent-a444b32de2a8255de`, in the worktree
  `/Users/pooks/Dev/lean4-effect4/.claude/worktrees/agent-a444b32de2a8255de`.
- Base: `25c798d50` on `refactor/phase1-phase3`, as the brief names. The worktree started at
  `9187b9b60` on `main`'s line; `git switch -C` moved the branch to the base before any work.
- Head: the commit that adds this receipt and the note. Its parent, `26e3de398`, is the code's
  last commit.
- Commits, in order:
  - `bcf7374a7`: stage 1, the figures and their laws;
  - `7945489b7`: the morph lemmas ready for the solid-tube pen;
  - `7dbac779b`: stage 2, the page;
  - `c34666dd7`: stage 3, the struts;
  - `26e3de398`: the page's kind names;
  - then stage 4, the note and this receipt.

## Changed files

- `tools/Tools/View/Tube/Glyphs.lean` (new): the seven families, `figure`, `draw`, the laws
  `figure_ok` and `morph_ok`, the morph's step lemmas, and the guards.
- `tools/Tools/View/Tube/GlyphPage.lean` (new): the page's blocks and its rules, and six films.
- `tools/Drivers/GlyphSheet.lean`: one import and one `page` line.
- `tools/view/v`: the branch `tube-glyphs`, and its name in the usage line.
- `docs/research/2026-10-13-tube-language/glyphs.md` (new, force-added): the note.
- `docs/research/2026-10-13-seat-glyphs-receipt.md` (new, force-added): this receipt.

## Commands and results

Each command ran in the worktree. `SCRATCH` is
`/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/e1e92e6e-f6fa-4134-946a-d08ffba1e7ca/scratchpad/glyphs`.

| Command | Result |
| --- | --- |
| `df -h /System/Volumes/Data` | 13 GiB available |
| `git switch -C worktree-agent-a444b32de2a8255de 25c798d50` | Reset branch |
| `cp -c -R /Users/pooks/Dev/lean4-effect4/.lake/packages .lake/packages` | 509 MB cloned copy-on-write |
| `LEAN_NUM_THREADS=3 lake build Tools.View.Tube.Sheet` | Build completed successfully (377 jobs) |
| `LEAN_NUM_THREADS=3 lake build Tools.View.Tube.Glyphs` | Build completed successfully (369 jobs) |
| `LEAN_NUM_THREADS=3 lake build Tools.View.Tube.GlyphPage` | Build completed successfully (405 jobs) |
| `LEAN_NUM_THREADS=3 lake build view-pages` | Build completed successfully (809 jobs) |
| `.lake/build/bin/view-pages tools/view/out/docs` | wrote `glyphs.html`, `cells.html`, `tubes.html`, `tube-glyphs.html` |
| `/usr/bin/time -p env LEAN_NUM_THREADS=3 lake env lean tools/Tools/View/Tube/Glyphs.lean` | real 1.87 s, the 37 `decide` proofs included |
| `LEAN_NUM_THREADS=3 lake env lean SCRATCH/probe/Audit1.lean` | 145 declarations within `[propext, Quot.sound]` |
| `LEAN_NUM_THREADS=3 lake env lean SCRATCH/probe/Audit.lean` | 10 of 182 reach `Classical.choice`, all in `GlyphPage` |
| `python3 scripts/check-language.py --show docs/research/2026-10-13-tube-language/glyphs.md` | no finding |
| `sh SCRATCH/chrome.sh --headless=new --hide-scrollbars --force-prefers-reduced-motion --window-size=1100,9200 --screenshot=SCRATCH/shots/page-final.png file://…/tools/view/out/docs/tube-glyphs.html` | written, and looked at |
| `sh SCRATCH/capture.sh SCRATCH/films.html 330 760 SCRATCH/shots/films 100 1000 2000 4000 7000` | written, and looked at |
| `sh SCRATCH/capture.sh SCRATCH/films.html 330 760 SCRATCH/shots/films 2900 3300` | written, and looked at |

`SCRATCH/chrome.sh` runs Chrome by its path, and `SCRATCH/capture.sh` runs it once per virtual
time. A plain command stood in for each, since the worktree guard refuses a quoted command name.

## Axiom output

`#axiom_audit Tools.View.Tube.Glyphs Tools.View.Tube.GlyphPage` reports 10 of 182 declarations
reaching `Classical.choice`. All ten are page writers in `GlyphPage`:

- `filmKept`, `filmFilled`, `filmClosed`, `filmJoined`, `filmHeld`, `filmAny`, `still`, `card`
  and `blocks` reach it through the kit's `SvgNode` (`SvgNode.toRaw` and `SvgNode.raw`, then
  `Whatwg.Html.Schema.Tag.ofForeignName?`, then `String.toList`).
- `name` reaches it through `Lean.Name.toString`.

`#axiom_audit Tools.View.Tube.Glyphs` reports all 145 declarations within `[propext, Quot.sound]`.
That includes every theorem and every figure.

## Evidence

- Proved: `figure_ok`, `morph_ok`, `step_ok`, `tracksOf_ok`, `bend_ok`, `width_ok`,
  `window_ok`, `gone_ok`, `viaTube_ok`, `clamp_le` and `reverse_ok`, at the base's `BEND` of
  15 px.
- Tested, by the guards of `Glyphs.lean`:
  - no two figures are alike;
  - the sort pairs closer than two parts are exactly `near`;
  - the run's morphs change one part;
  - every figure stands in its cell;
  - every piece keeps a 24 px bend;
  - a key names one role;
  - joins, reducers and struts name tubes.
- Tested (the guard of `GlyphPage.lean`): every tube of every picture of every film keeps the bend
  law.
- Reading: the pen's commits `027157447` and `fb74420d0` keep `tracksOf`, `Picture.step`,
  `Stroke.at` and `Mark.gone` as the proofs unfold them, and keep the builders' signatures.
- Judged by eye on headless Chrome captures, a host run and not a checker: the figures and the
  page. The films were seen at their start, at five moments within, and at their end.
- Bounded: every check is at 96 px, with the base's pen. The look after the merge is not seen.

## Landed theorems and their placement

`figure_ok` and `morph_ok`, with `step_ok` and its steps:

- Concept: none of the ten in `docs/core/semantics.md`. They are laws of the visual language,
  rows 367 and 369, not of Effect's semantics.
- Question: no registry claim. The consumers are `morph_ok`, which uses `figure_ok` and
  `step_ok`, and the page's films, which use `step_ok` with the page's guard.
- Reach: the stroke pen's tracks (a bend, a width, a window) of `Picture.step`, between pictures
  whose marks keep the bend law. The figures are the 37 at 96 px.
- Does not establish: the solid-tube pen's outlines, fillets and stretches. Nor a gap or a join
  kept during a morph, the cell during a morph, or a cubic's distance from its arc.
- Unlocks: nothing on the M5 → M6 → M7 spine, and no requirement R1 to R14. It serves the
  decomposition pass of rows 367 and 369.

`reverse_ok` (to move into `Form`) has the same placement. Its consumer is a mark drawn
`fromEnd`.

## Open obligations

- At the merge: map `Figure.joins`, `Figure.reducers` and `Figure.struts`, and replace `AIRGAP` by
  the pen's `GAP`. The build then proves `figure_ok` under the pen's `BEND` again.
- The driver's docstring (`tools/Drivers/GlyphSheet.lean`) still says that it writes three pages.
  It now writes four; the brief allowed only the import and the page line there.
- Move the module's "to move into" blocks into `Form`, `Draw` and `Motion`.
- `Motion.film` draws a tube that enters later as a dot at its root, and leaves one where a tube
  ends. The page avoids it by `complete`; the writer itself is the coordinator's.
- The semiotics verdicts taken and not taken are in the note's §7. The "small sizes" verdict is
  not taken; it waits on the owner's first question below.
- The note holds three questions for the owner. They ask about small figures under a 24 px bend,
  the defect's form, and whether a fork is a fitting.

## Proposed decisions rows (proposals only)

- The marks as tubes (`docs/research/2026-10-13-tube-language/glyphs.md`), representation: each
  kind is one plumbing family. A figure names its solid joins, reducers and struts as data. Keys
  name roles, so the run's morphs change one part.
- Small figures, representation: under a 24 px bend a half turn needs about 64 px. Either small
  figures take their own straight forms, or the bend law scales with the picture.
