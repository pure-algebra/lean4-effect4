# Seat brief: one blend for every join, coalescence, smooth bulges, and graph edges as tubes (slice S24)

Status: brief (history, not authority). 2026-10-13. The coordinator dispatches it. The seat works
in the kit's Mac worktree `~/Dev/lean4-whatwg-svg`, branch `html/svg`, from `eac9121` (S23).

**The one thing to know first.** The owner wants every join and every merge drawn by one precise
rule that scales and conserves, with "known nice aesthetic detailing". The coordinator proposes
the rolling-ball blend, a closing by a disc, as that rule. S23's dock is one case of it. This
slice makes the blend the kit's one join, adds the coalescence of two discs, smooth bulges, and
graph edges built from tubes.

## The owner's words, 2026-10-13, in order

- "graph figure need polish to have cleaner joints and splitting behavior, arrow arrival etc.. the
  organic trunks have defects.. .like wise it looks like a straight edge on the bulge with the
  pipes... i think making large versions so you can see overall shape close up is important.. it
  should be clean and smooth... look up more advanced algorithms for handling that as well"
- "still sharp bits on forks / joins... improve and needs much cleaner merging of circles.. again
  im sure there are clean algos for all this or we should be able to model it more prceisely to
  have aesthetic joining and merging of streams that scales, concsserves, aand has known nice
  aesthetic detailing"

## What Effect4 has decided since S23 (its commits `b3a9d503c` and before)

- **One proportion.** Line 2 px, margin 3 px, a unit a circle of 10 px (2 : 3 : 10). Body widths
  10, 14, 20 and 28 px, a step of √2, so two bodies of one step hold one of the next: Leonardo's
  rule, `w² = w₁² + w₂²` at a split.
- **The prototype** `~/Dev/lean4-effect4/tools/view/out/proto/physics.html` (open it in a browser;
  it is plain HTML and JavaScript) draws the coordinator's construction of the blend and of the
  coalescence. Its functions `closedPair`, `coalesce` and `crotchWeb` are the reference. Read them.
- **The research note** `~/Dev/lean4-effect4/docs/research/2026-10-13-tube-language/algorithms.md`
  is being written by another seat. The coordinator sends you its path when it lands. Read its
  sections A, B and F then, and follow its verdicts where they improve on this brief.

## What to build, in this order

1. **The design note first**: section S24 in `docs/SVG-PACKAGE-PLAN.md`, a ruling in
   `COORDINATION.md` (the next free R-S number after R-S50), and your file claims.
2. **The blend** (`Tube/Blend.lean` or within `Dock.lean`): the closing of the union of two bodies
   by a disc of radius `ρ`. The ball's centre stands `w₁/2 + ρ` from one centre line and `w₂/2 + ρ`
   from the other, and its arc between its two touching points fills the crotch. Cases, all one
   construction:
   - a branch that leaves a body at any angle (S23's dock, both sides);
   - a wye, where a branch joins a trunk on its tangent, and a fork, two arms from one point;
   - an arrival, where an edge meets a straight frame (a body that is a line).

   The radius is a rule of the widths, so a scaled figure has the scaled blend. Laws: closed;
   moved and scaled inputs give the moved and scaled web; the arc touches each edge along it.
3. **Coalescence** (`Tube/Coalesce.lean`): two discs closed by a ball, as `closedPair` does. Its
   outline is four arcs as cubics, and as `ρ` grows without bound it becomes the two discs' convex
   hull, a pill. The merge is a path in one parameter: the neck's half width `n = r √t`, the
   inertial law of coalescence (Eggers, Lister and Stone 1999), with the centres closing so the
   area stays two discs' area. The area of the outline is in closed form from sectors and
   triangles; state the conservation to within the kit's rounding of angles, and say so. Unequal
   discs if the construction allows it; equal discs first.
4. **Smooth bulges**: a stretch whose width follows any profile, with sides at least C²
   (curvature-continuous) where the profile is. Two things make S23's vessel read as a flat capsule
   with straight ramps: short ramps (`2 Δw`), and G1 sides whose curvature jumps at every station.
   Take the profile as data: smootherstep (`6u⁵ − 15u⁴ + 10u³`, C²) and the others the research
   note names. Draw the sides through the stations by a C² spline (d3's natural cubic spline is in
   `Natural.lean`), or by an exact construction if one exists. Give the ramp a rule of the widths.
5. **Graph edges as tubes** (W-numbered asks to come from Effect4; build the forms now):
   - a route between two ports that leaves and arrives square to the boxes' sides, made of
     straights and arcs that keep the bend law (an S of two arcs and a straight between);
   - a split: a trunk that divides into branches, the widths by Leonardo's rule, each crotch the
     blend;
   - an arrival: the branch's end docked onto the frame by the blend on both sides, narrowing
     toward its target so the direction reads from the taper (Holten and van Wijk 2009 found
     tapered edges read better than arrowheads; check the research note).
6. **An inspection writer**: curvature combs for any list of cubics, a mark at every place two
   cubics meet with no common tangent, as an SVG overlay. A probe page draws every form of this
   slice eight times larger with combs, at the widths 10, 14, 20 and 28. The owner asked for large
   versions; this is the instrument both sides use.
7. Batteries, the axiom receipt, the gates the change reaches, and the reviewer the kit's process
   names. A battery line is a reader, a control or a finite evaluation; it restates no theorem.

## Boundaries

- Work only in `~/Dev/lean4-whatwg-svg`. Commit there on `html/svg` by named paths; never push
  (the owner pushes). Never touch `~/Dev/lean4-whatwg` (its main has someone's uncommitted edits)
  and never edit lean4-effect4.
- Build with `LEAN_NUM_THREADS=2`, one `lake` at a time. Narrow builds.
- Disk: run `df -h /System/Volumes/Data` first; stop under 5 GiB free.
- No `sorry`, `partial`, `unsafe`, `native_decide`, `axiom`; the kit's trust gates hold.
- Performance: S23's exact numbers cost about 2.6 times Effect4's whole numbers on a body's
  outline. Keep the blend's searches bounded, and say what a film of 20 moments costs.

## Stop rules

Stop and hand back at: a law you cannot prove that a design change would fix (say which); a
question of meaning for the owner; a change the kit's process forbids without the owner; under
5 GiB free; five hours of work. The hand-back is a receipt that first names the one thing the
Effect4 coordinator must know to re-pin, then the base and head commits, the files, the commands
and results, the axiom receipt, the public declarations Effect4 should switch to, and what is open.
