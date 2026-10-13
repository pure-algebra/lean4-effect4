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
| W5 | CSS Syntax (level 3) sealed and read: tokens, rules and declarations, so a stylesheet is checked by its grammar | `page.css` must take every colour and family from a look's custom property (row 354, point 1); `Sheet.problem` in `tools/Tools/Document/Html.lean` checks that by scanning lines | no CSS module (`Whatwg/` holds Ecma262, Html, Infra, Signatures, Streams, Svg, Url, WebIdl) | medium |
| W6 | `href` values read by the URL Standard, and a site-level check that a relative link resolves to a page of the site | the site's pages link each other by relative paths (`Inline.link`) | `Whatwg/Url` exists; whether attribute admission reads `href` through it was not read | medium |
| W8 | The `admits` tactic reads a computed attribute name: `"aria-" ++ "label"` from `AttrVal.aria`, `"data-" ++ k` from `AttrVal.data` | the shell's `nav` takes `aria-label` beside spliced children; Effect4 writes the literal `⟨.aria_, "aria-label", "Pages"⟩` (`tools/Tools/Site.lean`) | `Admit.str?` reads a literal or `String.mk` of characters; an append of two literals reaches neither | medium |
| W9 | `html!` reads the tag of a spliced `E.el e` from the type of `e`, under an element with an ordered model (`head`, `html`) | the head's styles differ by page, and `html`'s model reads its children's tags; Effect4 types the head `Element .head InHtml`, proves its attributes empty by cases (`head_attrs`) and places it with `Child.of` | the elaborator checks the ordered model only when no child is spliced, and leaves the kernel to evaluate it over spliced terms | medium |
| W11 | Motion that passes a page's policy `default-src 'self'`: keyframes in a CSS file and the animation named by a class, never an inline `style` | the site serves that policy (`Tools.Site.headers`); the understanding note's Q5 | the kit writes a motion's timing as an inline `style` (the understanding note, section 1) | medium, before motion reaches the site |
| W12 | An optional attribute in `html!` and the combinators: `aria-current={o}` with `o : Option String`, the attribute left out at `none`, proved admitted for either | the site's navigation marks the current section and page; Effect4 writes each link twice, with and without `aria-current` (`sectionItem`, `crumb`, `pagerLink`, `tools/Tools/Site.lean`) | the `admits` tactic needs a closed attribute list, so an `if` over attributes is refused | low |
| W13 | Semantics Effect4 learns while building, to move into the package (the owner, 2026-10-12): a monoid fold over a document's lines and parts (`Algebra.collect`, `tools/Tools/Document.lean`); a scrollable region (a focusable `role="region"` with a name, around a wide table or figure); a figure whose SVG nodes link, with its caption and the figure in words (`tools/Tools/Document/Figure.lean`, W4, W10); a site's checks: one id per key, every reference and relative link resolving (W2, W6) | Effect4 keeps only what is Effect4's: the documents' content and the plan's data | Effect4 writes each in its tools today | medium, as the package takes them |
| W14 | A stylesheet as typed data whose every rule names the structural fact it draws (the owner, 2026-10-12: design in the semantics, by the abstractions of the Lean side): a type of facts (a part's boundary, a table's head, a block of code, a scrolling region, a status's emphasis), a rule as a fact with its selector and declarations, and the sheet as a fold over them, the values taken from a look's custom properties. A rule that names no fact is then a type error, not a review point; emphasis is a function from a status to a tone | Effect4's `page.css` is text with a comment per rule and a line-scanning check (`Sheet.problem`, decisions row 366, point 3); it becomes one such value, printed by the package | declarations and rules as data (`Whatwg/Html/Node/Css.lean`, S17) and the CSS plan (`docs/CSS-PACKAGE-PLAN.md`) | medium, with W5 |

## Notes, not asks

- **The typed shell landed** (Effect4 `e04ea78a5`, decisions row 364): every page's frame is
  written in `html!` in `tools/Tools/Site.lean`, and the module elaborates in about two seconds.
  A block folded from data enters through Effect4's `admit`, the shape asked as W1:
  `admit {ctx} (n : RawNode) : Except Refusal (Child ctx)`, from `explain_none_iff`. A computed
  `href`, a computed text and a computed `aria-current` splice without trouble.
- **The typed tree's cost.** Effect4 will measure the elaboration of a page shell written with `E.*`
  and `html!` before it adopts them. `Typed.lean` notes that a list literal of more than 32
  children costs seconds; a shell stays well under that.
- **`Scene/Strip`** (S16: lanes of states over a run) fits the scheduler's score of row 354
  (point 7, sequences). Effect4 will try it for the run view.

## Closed

| Id | Answer |
| --- | --- |
| W1 | `Child.check?`, `check`, `accept` and their list forms (`Whatwg/Html/Node/Check.lean`, S17 `6c06259`). Effect4 deleted its `admit` and calls `Child.check` (`tools/Tools/Site.lean`) |
| W2 | `Content.Document.problems`, `errors`, `advice` (`Whatwg/Html/Content/Document.lean`, S17). Every page of the site passes `errors` before it is written (`Site.html`) |
| W3 | the readings as tables and a division C can write, under 2^63 on checked data (`Whatwg/Svg/Scene/Vector.lean`, `Machine.lean`, S18 `53bab8a`); 0 of 114,074 readings differ under gcc. Effect4 takes them with the motion port (P5) |
| W4 | `Svg.figure`, `Svg.titled` (`SvgFigure.lean`, `SvgDefs.lean`, S17). Effect4 keeps its own `figure` for now: its nodes link, so `role="img"` would hide them |
| W7 | `Refusal.describe tree` (`Whatwg/Html/Content/Explain.lean`, S17). Effect4 deleted its `describe` |
| W10 | `Svg.link` (`SvgDefs.lean`, S17). Effect4 builds a node's link with it (`SvgOut.linkedMarks`) |

Effect4 pins `53bab8a` (S18) since 2026-10-12, late night; the site, the specimen's figure and
`generated/semantics.md` are unchanged by the move.
