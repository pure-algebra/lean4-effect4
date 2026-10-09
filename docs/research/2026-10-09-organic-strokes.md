# Organic strokes: growth rules for the view's lines

The owner's requests of 2026-10-09, by voice:
- give the places where lines meet boxes and one another a more organic feel;
- let a line widen where it joins, as a branch does, its width loosely the strength of what it
  connects;
- use rounder corners;
- give the lines natural noise, within a limited, relative width;
- follow growth rules, from the resources on the owner's computer about organic algorithms and
  ornament.

This note records what those resources say, the rules taken from them, and where each lives.

## 1. The sources read

| Source (on the owner's computer) | Its finding | What we take |
| --- | --- | --- |
| Prusinkiewicz and Lindenmayer, *The Algorithmic Beauty of Plants* (`~/Documents/Books_Reading/03_Design_Generative/`), pp. 57–58 | da Vinci's postulate: the branches at each height, put together, equal the trunk below in thickness; for two equal daughters `w₁² = 2 w₂²`, so each is `1/√2` of the mother | a line's width by its share of the work: `1/√n` for each of `n` parallel parts |
| the same, §1.7 (stochastic L-systems) | identical plants look artificial; variation should keep the general aspects and modify the details; varying the interpretation alone leaves the topology | noise in a line's width only, never in the layout or the structure |
| the same, §6.2 (growth functions) | a module's shape is a continuous function of its age | a growing line narrows to its tip while it is drawn, continuously |
| O'Brien, *Architecture as Ornament: Louis Sullivan's Late Work* (`~/Documents/Books_Reading/`) | Sullivan's medallions: organic growth runs along a geometric container's axes and bursts out where an axis crosses its perimeter | the organic is held by the geometry: the layout stays a proved fold, and the organic is only in the stroke |
| Lamprecht, *Why Ornament Matters, Part II* (`~/Desktop/`) | ornament as communicator, scale-weaver and mediator of boundary | a mark carries a meaning: here, the share of work |
| the owner's foldlab ornament direction (`~/Dev/foldlab/.staging/ornamentation/MATHY-DIRECTIONS.md`, rules G1, G6, G10) | no form without a meaning; growth is accretive; motion renders spend, not structure | a line's noise is fixed by its key and never wiggles; widths come from the structure |
| the owner's noise code (`~/Dev/drawing_learning/src/noise.js`) | hashed value noise, smoothstep between cells, octaves | the same family, in integers |

The books are read in place, and nothing is copied into the tree.

## 2. The rules

| Rule | What it draws | Where |
| --- | --- | --- |
| **da Vinci's split** | where work runs in `n` parallel parts (a fork's branches, a race's entrants, a merge's layers, a forked fiber beside its parent), each part's lines carry `1/√n` of the work; a choice keeps all of it, since one branch runs. A line's width is the trunk's times its share, never finer than the finest line | `Grow.split`, `Box.reshare` and `shares` (`tools/Tools/View/Flow.lean`), the edge's `share` |
| **A collar** | where a line meets a box or a bar, it widens by a quarter circle on each side, as a branch widens into its trunk; the collar's radius scales with the line's width | `Grow.collar`, `Laid.organicCalls` |
| **Noise in a band** | each edge of a line moves by smooth value noise in two octaves, seeded by the line's key, at most `noise` per mille of its half-width, and not at all at its ends | `Grow.noise`, `Grow.halfWidth`, `Grow.stroke` |
| **A growing tip** | a line still being drawn narrows to its tip | `Grow.stroke` with `tip` |
| **Round corners** | a box, a region and a bar take round corners; a frame is a ring filled by the even-odd rule | `Grow.roundRect`, `Grow.ring` |

The drawing has one new call, a shape (`Call.shape`, `tools/Tools/View/Picture.lean`). It fills
closed paths of cubic segments by the even-odd rule, its points in thousandths of a pixel. The
stream, the C painter (`paint_device_shape`, `tools/view/paint.h`) and SVG all draw it. The move
law covers it (`lowerCall_move`).

Every rule is a token of the look (`organic` and `stroke.radius`,
`tools/Tools/View/Tokens.lean`). The look `classic` (`tools/view/looks/classic.tokens.json`) sets
the trunk and the radius to 0. It draws every page byte for byte as before (a finite check over
the flow specimen, the graph specimen and the eight corpus builds).

## 3. The laws

- `noise_band` and `halfWidth_band` (`tools/Tools/View/Organic.lean`): the noise lies in
  `[-1000, 1000]`, and a moved half-width differs from its own by at most the amplitude per mille.
  The width is limited and relative, by proof.
- `good_reshare` and `Realizes.reshare` (`tools/Tools/View/FlowLaws.lean`,
  `tools/Tools/View/FlowOrder.lean`): splitting the shares moves no edge's ends. So `lay_good`,
  `place_descends`, `place_apart` and `place_keeps_order` hold as before.
- da Vinci's split comes within rounding of the rule for 2 to 16 parts (`#guard`s in
  `Organic.lean`): a finite evaluation.

Each rests on `propext` and `Quot.sound`.

## 4. Rulings the owner must make

1. **What a line's width means** (meaning). Recommended: the share of the work, by da Vinci's
   rule. This refines row 337, point 2, where weight and tone show depth. The tone still can; the
   weight becomes the share. The owner may prefer the weight to show depth, as row 337 has it.
2. **The default look** (representation). Recommended: the organic strokes and round corners in
   the base look, with `classic` kept for the plain drawing.

## 5. What this note does not establish

- The noise and the collars carry no meaning; they are form.
- The collar assumes a vertical line meeting a horizontal surface, as `bumpY` and `stepY` draw. A
  `linear` edge's end is slanted, and its collar is drawn upright.
- No law covers the smoothness of the outline, or that two strokes do not touch.
