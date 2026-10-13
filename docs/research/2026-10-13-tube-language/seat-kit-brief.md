# Seat brief: solid tubes in the html/svg kit (slice S23)

Status: brief (history, not authority). 2026-10-13. The coordinator dispatches it. The seat works
in the kit's Mac worktree `~/Dev/lean4-whatwg-svg`, branch `html/svg`, from `80bb06b`.

**The one thing to know first.** The owner asked that the drawing of smooth solid tubes and their
joins live in the kit, made the clean way d3 makes shapes: "yes update the html / svg libs for
that looking at d3 for the clean ways to do that its all there". Effect4 holds a working version
at commit `027157447`; this slice gives the kit the general abstractions, with laws, so Effect4
re-pins and deletes its local copies.

## The owner's words, 2026-10-13, in order

- "start with solid fills and think of joining... i kind of like when they dont join necessarily
  by solid trans forms but by airgaps for some semantics... and we need to ensure there are
  smooth no kinks"
- "i kinda want everything with a smooth outline, more rounded natural joins with curve, bend,
  and feel still see sharp edges... joins should be organic rounded docks like tree branch
  widening or joints smooth with appropriate curves"
- "yes update the html / svg libs for that looking at d3 for the clean ways to do that its all
  there"
- Earlier, the ruled direction (Effect4 decisions row 369): one body, the tube, for every glyph;
  every transition a morph that keeps the bend law; SMIL for shape motion; pills for units.

## What the kit has already (read these first)

- `Whatwg/Svg/Geometry/Shape.lean`, `Through.lean`, `Natural.lean`, `Monotone.lean`: d3-shape's
  curves (linear, step, bump, cardinal, uniform Catmull–Rom, basis, natural, monotone), the
  curve as a value, `line`, `link` and `area`.
- `Whatwg/Svg/Geometry/Stroke.lean`: a line drawn as a filled outline whose half-width changes
  along it (`Stroke.samples`, `side`, `outline`, `stroke`), and `Stroke.collar`, where a line
  meets a surface: the nearest thing to a dock.
- `Whatwg/Svg/Geometry/Outline.lean`, `Smooth.lean`: closed outlines, and the laws that a spline
  has no corner at its joints.
- `Whatwg/Svg/Scene/`: `Join` (the data join), `Motion` (tracks, `Transition`), `Spring`, `Units`.

## What Effect4 holds, the reference (commit `027157447` of lean4-effect4)

Read `~/Dev/lean4-effect4/tools/Tools/View/Tube/` at that commit (`git -C ~/Dev/lean4-effect4
show 027157447:<path>`):

- `Trig.lean`: sine, cosine, `sinc`, `tanc` by Taylor series in whole numbers.
- `Form.lean`: the tube (start, heading, bore, pieces of a length and a turn); the bend law
  `BEND · |θ| ≤ ℓ` with `BEND` 24 px; `Piece.mix`, `Tube.mix` and their laws (`Piece.mix_ok`,
  `Tube.mix_ok`: the law's pieces form a convex cone); `Tube.reverse`, `Tube.cut`, `Tube.at`,
  drawing each piece as two cubics.
- `Outline.lean`: `Tube.offset` (the exact parallel: an arc's is an arc), `bodyCubics` (a body's
  outline: two parallels and round or cut caps), `patchCubics` (a stretch whose width changes,
  eased by the smoothstep), `crotch` (a fillet in the crotch of a branch that leaves a body on its
  tangent, the widest that fits), `partCubics` (an air gap between two round ends).
- `Draw.lean`: the pen (one body tone, contents stroked), joins (`Join`), partings (`plugOf`,
  `cutOf`), reducers and sleeves.
- `Motion.lean`: `Stroke` (bend through a pose, width, window), `Track`, `Track.at_done`,
  `Mark.under` (a mark under all its tracks at a moment), the SMIL writer (`animate`,
  `markAnims`, `film`), a film's still for reduced motion.
- Effect4's asks W30, W32 and W33 in `~/Dev/lean4-effect4/docs/research/2026-10-12-whatwg-requests.md`.
  W31 (cased layers) is withdrawn: solid fills replace casings.

## d3, the source

d3-shape 3.2.0 is on this machine, read-only:
`~/Dev/skygest-cloudflare/node_modules/.bun/d3-shape@3.2.0/node_modules/d3-shape/src/`
(ISC licence, Copyright 2010–2022 Mike Bostock). Cite each file you port by its path and version,
as the kit's modules already do. Read at least `curve/catmullRom.js` (the centripetal spline,
`alpha` a half by default, which has no cusp and no self-crossing within a segment), `link.js`,
`area.js` and `curve/bundle.js`. d3 has no parallel curve, no fillet and no tube; for those the
kit follows Effect4's construction, and the note says so.

## What to build, in this order

1. **The design note** first, as the kit's process asks (its `AGENTS.md`, "Development order"):
   a section S23 in `docs/SVG-PACKAGE-PLAN.md`, the public declarations, their
   specification anchor (the path chapter's cubic, the painting chapter's fill), and the
   assurance route. Record the owner's direction as a ruling in `COORDINATION.md` (the next
   free R-S number, after R-S49) and claim your files there before you write them.
2. **The tube** (W30): the form, the bend law and the intrinsic mix with their laws, reverse,
   cut, the point at a length, drawing by cubics; trigonometry where the kit has none. Choose
   the number type with the kit's conventions (exact `Rat` geometry since S11); the laws of the
   mix are about lengths and turns and need no trigonometry.
3. **Solid bodies and their joins**: the exact parallel and a body's outline; a stretch whose
   width changes, built on `Stroke` where it fits; a parting (an air gap between two round ends);
   a dock where a branch meets a body: the fillet of Effect4's `crotch`, generalised from
   `Stroke.collar`, at any departure that keeps a smooth outline, with a branch that widens into
   what it leaves as a tree's branch does. Laws: each outline is a closed chain (`Cubic.Closed`);
   moved inputs give the moved outline; the parallel of a piece keeps its turn.
4. **d3's centripetal Catmull–Rom** (`alpha`), if the kit lacks it, as a `Curve.Through`, with
   the laws every curve of the kit has.
5. **Motion** (W33, W32): the three changes of a stroke in `Scene/Motion`'s shape, a mark under
   all its tracks at once, and the SMIL writer beside the CSS writer, with `Track.at_done`'s law.
6. Batteries, the axiom receipt, the gates the change reaches, and the reviewer the kit's process
   names. A battery line is a reader, a control or a finite evaluation; it restates no theorem.

## Boundaries

- Work only in `~/Dev/lean4-whatwg-svg`. Commit there on `html/svg` by named paths; never push
  (the owner pushes). Never touch `~/Dev/lean4-whatwg` (its main has someone's uncommitted
  edits) and never edit lean4-effect4.
- Build with `LEAN_NUM_THREADS=2`, one `lake` at a time: two other Lean builds run on this
  machine. Narrow builds; no bare `lake build` until the slice's end, and then only what the
  kit's gates ask for.
- Disk: run `df -h /System/Volumes/Data` first; stop under 5 GiB free.
- No `sorry`, `partial`, `unsafe`, `native_decide`, `axiom`; the kit's trust gates hold.

## Stop rules

Stop and hand back at: a law you cannot prove that a design change would fix (say which); a
question of meaning for the owner; a change the kit's process forbids without the owner; under
5 GiB free; five hours of work. The hand-back is a receipt that first names the one thing the
Effect4 coordinator must know to re-pin, then the base and head commits, the files, the commands
and results, the axiom receipt, the public declarations Effect4 should switch to, and what is open.
