# SVG seat, guidance 6: the site draws with the kit, and the semantics move to the package (2026-10-12, late night)

From the Effect4 coordinator to the PC's seats on `lean4-whatwg`. Take it as the owner's direction.
The owner's words of the night: "for a lot of these HTML things, we're going to want to keep
pushing that out of the Lean 4 [Effect4 tools] as much as we can, pushing that into the HTML [and]
SVG, … the monoid representation, … what is a scrollable [region], … the semantics we keep pushing
out as we learn". The asks stay in `2026-10-12-whatwg-requests.md`, copied beside this note; it
gained W12 and W13 tonight.

## What landed in Effect4 tonight, on the pin `c33ce29`

- **The site's frame is the typed tree** (decisions row 364; `tools/Tools/Site.lean`). Every page's
  head, header, navigation, breadcrumbs, parts, neighbours and footer are written in `html!` and
  admitted when Lean compiles them, in about two seconds. A block folded from data enters through
  Effect4's `admit` (the shape of W1). `head` and `html` have ordered models, so the head is typed
  `Element .head InHtml` with a proof that its attributes are empty (W9).
- **The site is one value.** The semantics report is split into a page for each concept and each
  requirement, and the navigation is a fold of the value. `Site.check` refuses a dead link or a
  reference outside its space before anything is written (W2 and W6, done locally).
- **Figures are drawn by the kit** (decisions row 365; `tools/Tools/Document/Figure.lean`,
  `SvgOut.linkedPicture`). A requirement's open spine and its concept map are graphs as data.
  Effect4's layered layout places them, and the kit writes them. Each node that opens a part is
  one SVG `a`, built with `SvgNode.element .a [.attr .href …]`, since `SvgBuild` has no
  constructor (W10). The site runs no script, so Mermaid could not draw the plan.
- **One monoid fold** (`Algebra.collect`, `tools/Tools/Document.lean`): the site's links, keys and
  parts and the document's census are its instances.

The site is live at `https://effect4-docs.pages.dev` with all of this.

## What to take, in order

1. **W11 before more motion.** The site serves `Content-Security-Policy: default-src 'self'`. A
   motion written as a `style` element and `style` attributes (`SvgMotion.lean`) is refused there.
   Motion that reaches the site needs keyframes in a stylesheet file and the animation named by a
   class. Your CSS plan (`docs/CSS-PACKAGE-PLAN.md`) is the natural home for the file's text.
2. **W1 and W2**: `Child.check?`, and the document-wide rules (one `id` per key, every `#` link
   resolving). Effect4 writes both locally and switches when they land.
3. **W13, the semantics to move.** Each is written in Effect4's tools tonight and belongs in the
   package. The figure is a linked picture, its caption and its words. The scrollable region is a
   focusable `role="region"` with a name, around a wide table or figure. The site's checks are
   the third.
   The monoid fold is a pattern, not a type of yours; take it if a document type of yours wants it.
4. **W10, W4**: `SvgBuild` constructors for `a`, `title` and `desc`.
5. **W5** (your CSS plan): when a sheet reads by its grammar, Effect4's line-scanning check of its
   page rules (`Sheet.problem`) goes.
6. **W12, W8, W9, W7**: when convenient.

## Not asked

No change of the pin is asked until a slice above lands; say which commit to pin, as before.
