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
| W5 | CSS Syntax (level 3) sealed and read: tokens, rules and declarations, so a stylesheet is checked by its grammar | `page.css` must take every colour and family from a look's custom property (row 354, point 1), and draw no ornament without a meaning (row 366, point 3). Since S19 `Tools.Document.Sheet` reads it by the package's tokens (`tokenizeText`) and refuses a declaration located under its rules; a fold of its own finds the declarations until the parser lands | K1 extractor (S18), K2 tokenizer and writer with their round trip (`e4e4ac1`), K3 value definition syntax and `admits` (`f72f702`); the parser is K4 | medium: what is left is the parser |
| W9 | The rest of W9: under an element with an ordered model (`html`, `head`, `details`), a spliced list or a variable `Child`, and `E.el e` for a tag with a conditional category (`a`, `input`), checked by the elaborator and not left to the kernel | the shell places a head and a body by `E.el` (S21); the figure in words is a `details`, whose ordered model keeps it a raw node | answered in part at S21 (`Ctx.admitsWith_unread`, the position from the expected type, an ordered model read through a spliced child that shows its element) | low |
| W13 | Semantics Effect4 learns while building, to move into the package (the owner, 2026-10-12). Left: where the figure in words stands. `Region.figureRaw` puts the words between the region and the caption, so the caption sits below the words and away from the picture; Effect4 keeps the caption beside the picture and the words after the figure, named by `aria-describedby`. The ask: a placement for the words (after the figure), or the caption first | `tools/Tools/Document/Html.lean`, the `graph` case | the region and the figure in one (`Whatwg/Html/Node/Region.lean`, S21); the site's checks (S20). The seat declined the fold (`Algebra.collect` folds Effect4's documents, not trees) | low |
| W14 | A stylesheet as typed data whose every rule names the structural fact it draws (the owner, 2026-10-12: design in the semantics, by the abstractions of the Lean side): a type of facts (a part's boundary, a table's head, a block of code, a scrolling region, a status's emphasis), a rule as a fact with its selector and declarations, and the sheet as a fold over them, the values taken from a look's custom properties. A rule that names no fact is then a type error, not a review point; emphasis is a function from a status to a tone | Effect4's `page.css` is text with a comment per rule and a check on its tokens (`Tools.Document.Sheet`, decisions row 366, point 3); it becomes one such value, printed by the package | two trees of one sort: S17's writer (`Whatwg/Html/Node/Css.lean`: `Decl`, `Rule`, `Sheet`, values as strings) and K3's tree (`Whatwg/Css/Syntax/Tree.lean`: `Declaration`, `Rule`, `Stylesheet`, values as component values, the tree the parser will return). The ask includes one tree: S17's writer as a fold of K3's, so the typed sheet prints through the tree that the tokenizer and the parser read back | medium, with W5 |

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
| W11 | `Play.reach := .sheet`: `Step.sheet` is the rules for a file (the `@keyframes`, a rule per thing under `[data-track="<stem>-<n>"]`, the rule of reduced motion), and `Step.things` the things with no `style` (`Whatwg/Html/Node/SvgMotion.lean`, `SvgStep.lean`, S19 `6beedd9`); observed in Chrome 152 under `default-src 'self'`. Effect4 takes it when motion reaches the site (row 366, point 10) |
| W6 | `Content.Site.errors`, `Site.Checked` (`Whatwg/Html/Content/Site.lean`, S20 `eb9a930`): every href of every page, the shell's too, read by the URL Standard's relative states. Effect4 deleted its `resolve`, its link loop and its shape checks; `Site.checked` runs the package's check over every rendered tree, and found a dead fragment the old check could not see |
| W8 | `admits` reads a computed attribute name (S21 `990ee7d`). Effect4's pager writes `aria-label="Pages"` in markup beside a spliced list |
| W12 | `aria-current={o}` and `A.opt` (S21). Effect4 writes a section, a crumb and a title once each |

Effect4 pins `990ee7d` (S21) since 2026-10-12, night (`18368e767`); the move changed no output. The
page's rules are read by K2's tokens (`77bcd8141`); the shell is markup throughout and the site
passes the package's check (`6ad53e0ca`); tables and figures stand in the package's region
(`8fbb484d4`).
