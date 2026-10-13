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
| W14 | A stylesheet as typed data whose every rule names the structural fact it draws (the owner, 2026-10-12: design in the semantics, by the abstractions of the Lean side): a type of facts (a part's boundary, a table's head, a block of code, a scrolling region, a status's emphasis), a rule as a fact with its selector and declarations, and the sheet as a fold over them, the values taken from a look's custom properties. A rule that names no fact is then a type error, not a review point; emphasis is a function from a status to a tone | Effect4's `page.css` is text with a comment per rule and a check on its tokens (`Tools.Document.Sheet`, decisions row 366, point 3); it becomes one such value, printed by the package | the HTML half (S22 `82630b1`): `Whatwg/Html/Content/Structure.lean`, a structural fact as a place in a tree (`Where`), `places`, the class `Vocabulary` and `unused`; `WhatwgTest/Html/SheetFacts.lean` reads `page.css` against it. The CSS half waits for the parser. Two trees of one sort: S17's writer (`Whatwg/Html/Node/Css.lean`: `Decl`, `Rule`, `Sheet`, values as strings) and K3's tree (`Whatwg/Css/Syntax/Tree.lean`: `Declaration`, `Rule`, `Stylesheet`, values as component values, the tree the parser will return). The ask includes one tree: S17's writer as a fold of K3's, so the typed sheet prints through the tree that the tokenizer and the parser read back | medium, with W5 |
| W15 | Two parts of a layout that the view's value pictures write by hand (`tools/Tools/View/Cell.lean`, VS-2): a part centred down a height, as `centred` is across; and a part drawn at the room of a composite after the composite is laid out: a frame around it, and a rule at each edge where two parts of a `row` or a `column` meet | a record is a panel whose rows are ruled apart, a list a row of cells ruled apart, each in a frame | `Whatwg/Svg/Scene/Layout.lean` (S22): `beside`, `above`, `over`, `row`, `column`, `inset`, `centred`, `stack`; the seat's wanted list names "a column as its parts at the edges of `Row.spans`" | low |
| W16 | Scales: linear with an exact inverse, bands for the beats of a run, ticks (the seat's wanted list) | the living-quantities language (`docs/research/2026-10-13-living-quantities/`): a count on one scale with others | none | high, for the quantities |
| W17 | A ribbon: a stroke whose width varies along a curve, as one closed outline, with a collar where it meets a body; a split whose branch widths sum to the trunk. Laws: the outline stays in its band; widths add at a split; a moved ribbon is the ribbon moved | a channel's width is what it carries in a step (da Vinci's rule); Effect4's `Tools.View.Organic` (`stroke`, `collar`) is the start | `Curve`, the monotone curve (S22) | high |
| W18 | A flow network laid out on `Layers`: nodes with values, links with widths; at each node what enters equals what leaves | the run's totals: where the units went | `Layers` (S22), d3-sankey read for it | medium |
| W19 | Areas and stacks: an area between two curves, stacked layers, a signed baseline (a deficit below zero), through the monotone curve; a layer's height at a beat is its value | the run as one level: deficit, held, pressure | `Curve.monotoneX` (S22) | high |
| W20 | Units in a vessel: n units in c slots, the order kept and the room shown; above a threshold one mark for k units (Isotype). Laws: the count is kept, the front stays at the front | a bounded place drawn as its units | `Layout` (S22) | high |
| W21 | A body moved along a path in one beat, and a keyed join in which a key that leaves one place and enters another is one move, not an exit and an enter | a step's flows: a unit travels from place to place | `Plan.ofJoin`, `Motion.later` (S22), the reach by a sheet (W11) | high |
| W22 | A vessel: a rounded hull around a layout's room, with openings where ribbons meet it, as one outline | the bounded place | `IBox.hull` (S22) | medium |

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
| W9 | `Run ctx t a b` and `Element.ofRun` (`Whatwg/Html/Node/Run.lean`, S22 `82630b1`): children under an ordered model in parts, a loop checked once, children whose tags are data by `Run.content`; `E.el e` of a variable `a` or `input` elaborates (`Content/Monotone.lean`). Left to the kernel: a list splice inside `html!` under an ordered model, written with `Element.ofRun` instead (debt D139) |
| W13 | `Region.withWords`, `withWordsRaw` (`Whatwg/Html/Node/Region/Words.lean`, S22): the figure names its words, the caption stays beside the picture, the words follow. Effect4's figure is `Region.withWordsRaw` (`tools/Tools/Document/Html.lean`); the site is unchanged byte for byte |

Effect4 pins `bae6a2e` (S22) since 2026-10-13; the move and the figure's words through the package
changed no byte of the site. Before, `990ee7d` (S21, `18368e767`). The
page's rules are read by K2's tokens (`77bcd8141`); the shell is markup throughout and the site
passes the package's check (`6ad53e0ca`); tables and figures stand in the package's region
(`8fbb484d4`).
