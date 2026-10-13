# Requests to lean4-whatwg from Effect4's pages and pictures (a living list)

Status: research note (history, not authority). Started 2026-10-12, on the owner's steer: "as we're
building, any improvements we can make to the HTML packages we should note". Each entry is a gap
that Effect4's documentation site (decisions row 363), its studio (row 362) or its picture writer
(row 360) meets in `lean4-whatwg`. The SVG seat on the PC owns the package; it takes these as the
Effect4 coordinator's asks (row 360, point 3). Read at the pin `c33ce29` (S16).

Every entry names its use in Effect4, what exists in the package today, the ask, and a priority.
An entry closes with the package commit that answers it.

## Open

| Id | Ask | Effect4's use | In the package today | Priority |
| --- | --- | --- | --- | --- |
| W1 | `Child.check? : RawNode → Option (Child ctx)`: a raw node admitted with its proof when the checker accepts it | the site's shell becomes the typed tree, and data-driven content (a fold of `Tools.Document`) enters it once, checked | `Child.of`, `Child.text`, `Child.entity`, `Child.ofSvg` (`Whatwg/Html/Node/Typed.lean`, `SvgValid.lean`); no admission of a checked raw node | high |
| W2 | Conformance across a document: unique `id` values; each `href="#x"`, `for`, `aria-labelledby` and `aria-describedby` names an id that exists; one `main`; a skipped heading level reported | the semantics page writes 245 permalinks and an id per part; the view's clip ids `c{n}` repeat across figures on one page (the SVG adoption probe, section 6) | the content model is per element; no document-level rule found | high |
| W3 | Easing readings as test vectors: `Easing.at` for each easing at every moment 0 to 1000, exported as a table | the C player samples the same tracks (row 363, point 5); a check holds C's readings equal to the kit's | `Easing.at` is whole-number arithmetic rounded down once (`Whatwg/Svg/Scene/Motion.lean`), which C can transcribe | high, with P5 |
| W4 | A figure for a picture: an `SvgNode` inside `figure` with `figcaption`, `role="img"` and `aria-labelledby`; links on nodes (`a` with `href` inside the SVG) | the plan's graphs become figures whose nodes link to their claims and goals | `Child.ofSvg`; whether the SVG schema's `a` admits `href` at the kit's constructors was not read | medium |
| W5 | CSS Syntax (level 3) sealed and read: tokens, rules and declarations, so a stylesheet is checked by its grammar | `page.css` must take every colour and family from a look's custom property (row 354, point 1); `Sheet.problem` in `tools/Tools/Document/Html.lean` checks that by scanning lines | no CSS module (`Whatwg/` holds Ecma262, Html, Infra, Signatures, Streams, Svg, Url, WebIdl) | medium |
| W6 | `href` values read by the URL Standard, and a site-level check that a relative link resolves to a page of the site | the site's pages link each other by relative paths (`Inline.link`) | `Whatwg/Url` exists; whether attribute admission reads `href` through it was not read | medium |
| W7 | A located refusal in words, the element names along its path (`Refusal.describe tree`) | Effect4 writes this itself (`describe`, `tools/Tools/Document/Html.lean`) | `Reason.describe`, `RawNode.at?` (`Whatwg/Html/Content/Explain.lean`) | low |

## Notes, not asks

- **The typed tree's cost.** Effect4 will measure the elaboration of a page shell written with `E.*`
  and `html!` before it adopts them. `Typed.lean` notes that a list literal of more than 32
  children costs seconds; a shell stays well under that.
- **`Scene/Strip`** (S16: lanes of states over a run) fits the scheduler's score of row 354
  (point 7, sequences). Effect4 will try it for the run view.

## Closed

None yet.
