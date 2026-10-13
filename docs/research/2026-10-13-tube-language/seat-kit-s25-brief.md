# Seat brief: the kit's slice S25, cheap films with exact moments

Status: brief (history, not authority). 2026-10-13. The coordinator dispatches it after S24's
receipt. The seat works in `~/Dev/lean4-whatwg-svg` on `html/svg`, as S23 and S24 did.

**The one thing to know first.** Path data is most of a film's bytes. The capacity-13 Queue film
is 3.13 MB, and 2.71 MB of it is path data in 1450 animations. Slice M1 measured it
(`tools/Tools/View/Tube/Measure.lean`, commit `9cc3ae42d`). S25 makes the kit's film writer share
what does not change and sample only where a shape changes. Every saving keeps each moment's
value: a law or a finite evaluation says so.

## Read first

- The motion plan `docs/research/2026-10-13-motion-everywhere/README.md` (in lean4-effect4): §6.2
  to §6.4 (the costs and the sampling rules) and the kit asks W34 to W38 at the end of §7.
- The research note `docs/research/2026-10-13-tube-language/algorithms.md`, G6 (smooth SMIL
  morphs, the sampling rule) and H1 to H4 (motion detailing).
- The kit's `Whatwg/Html/Node/SvgSmil.lean`, `Whatwg/Svg/Geometry/Tube/Motion.lean` and S24's
  `Bulge.lean` (`Join.bulb`).

## What to build, in order

1. **W35, sharing.** Write each tube's centreline once, with its own animation, and each stroke
   on it as a `use` with scalar animations of its dash and width. Write a change that is linear in
   an eased progress under a cubic easing as two values with `calcMode="spline"` and `keySplines`.
   Law: at every moment, the shared film's values equal the unshared film's.
2. **W38, fewest moments.** Choose a bend's moments so that the straight lines between them stay
   within a stated distance of the mix. G6 gives the rule for a point that turns through `θ` at
   radius `r`: `n ≥ θ / (2 arccos(1 − ε / r))`, with `ε` a tenth of a pixel. Arc-length `keyTimes`
   are the alternative. Law or finite evaluation: every chord stays within `ε`.
3. **W36, a bulb moved by a transform.** On a straight piece, a bulb's outline depends only on its
   place and its rise. Move it by a translation, and sample only its rise. Law: the moved bulb
   equals the bulb drawn at that place.
4. **W34, staged changes of tubes.** `Plan`, `Stage`, `Score` and `Reel` over a tube's changes, so
   a film of tubes keeps `Reel.at_joint`, `Motion.Respects` and `Motion.reduced`.
5. **W37, a film as stream rows.** A film's sampled values as rows for the C player, with the law
   that a straight reading between rows is SMIL's linear reading.

## How it is checked

- The kit's narrow builds and batteries for each module touched, and its axiom audit, as S24's.
- A probe page of each new SVG feature (a `use` that inherits an animated dash, `keySplines`, a
  moved bulb). Chrome passed the motion plan's probe. Write the page for WebKit and Firefox too;
  the coordinator opens it in both, since the owner's viewer runs on WebKit.
- The receipt `docs/research/2026-10-13-s25-receipt.md` in the kit names first the one thing to
  know, then the commits, the commands and results, the audit, and each film's bytes before and
  after on a fixture of the Queue's shape.

## Boundaries

- Never push. The owner pushes `html/svg`, and the coordinator re-pins.
- Keep the kit's own rules (`COORDINATION.md`). Edit only the kit's checkout.
- One `lake` at a time, with `LEAN_NUM_THREADS=3`. Temp files go in the session's scratchpad.
- Stop at a question of meaning, or at about five hours, with a short hand-back.
