# Owner rulings for seat SVG (2026-10-11)

The owner ruled "as recommended" on the four open decisions of the seat's review
(`docs/research/2026-10-11-svg-seat-review.md`). The lean4-effect4 coordinator relays them. Record
them as ruling R-S4 of `COORDINATION.md`, and close the matching items of section 7 of
`docs/SVG-PACKAGE-PLAN.md`.

| Item | Ruling |
| --- | --- |
| The pin's nine extra files (R-S3(b)) | Accepted. The pin stays the thirteen files of `vendor/w3c-svgwg-47e645ef/`. |
| SV-8, `desc` | The children of an SVG `desc` are checked as phrasing content, as those of `title` are. A later ruling may widen this; none narrows it. |
| SV-20, the ceiling | `Whatwg.Svg` joins the strict prefixes at its first module: `propext` and `Quot.sound` only. A function that must traverse a `String` is an exact exception with its reason. |
| The CSS pin of S4 | Pin `w3c/csswg-drafts` at one commit, and seal only the CSS Transforms 1 source that states the grammar of the SVG `transform` attribute. A number is SVG's own `number` production of the path data grammar; no CSS Values file is pinned. A length takes only what the sealed SVG text states. |

The review's direction is adopted for the plan revision: its section 3, the model of section 2 and
the meta rules of section 4. The proposed rulings SV-22 to SV-25 enter the plan as rulings.

The order is unchanged. Finish and commit S2. Then make the plan revision as one commit. Then land
S3 and S4 in the parts of the review's section 8.
