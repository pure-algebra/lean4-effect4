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
| W17 | A ribbon: a stroke whose width varies along a curve, as one closed outline, with a collar where it meets a body; a split whose branch widths sum to the trunk. Laws: the outline stays in its band; widths add at a split; a moved ribbon is the ribbon moved | a channel's width is what it carries in a step (da Vinci's rule); Effect4's `Tools.View.Organic` (`stroke`, `collar`) is the start | `Curve`, the monotone curve (S22) | high |
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
| W5 | `parseStylesheetText`, `Stylesheet.located` (`Whatwg/Css/Syntax/Parse.lean`, `Located.lean`, K4 `58bc7a4`): the standard's parser over the tokens, with the round trip of a writable sheet; Effect4's `page.css` reads back, 80 rules and 247 declarations |
| W14 | `Content/Structure/Selector`, `Look`, `Sheet` (S22 `edbfec9`): a rule as the fact it draws, colours and families only from a look's tokens, a rule with no fact not a value; Effect4's `page.css` as one typed sheet in the package's test |
| W15 | `Scene/Layout/Frame` (S22 `cd7332b`): `centredDown`, `framed`, `ruledRow`, `ruledColumn`, with where each part stands |
| W16 | `Scene/Scale/Invert`, `Linear`, `Band`, `Chain`, `Geometry/Ticks` (S22 `a191355`): scales with a way back, bands after d3, ticks and nice bounds, exact |
| W19 | `Geometry/Stack/Layers` (S22 `ca3dca8`): layers over beats with a signed baseline, and the area between two edges by the monotone curve; also `Geometry/Through`, a curve through points as a value |
| W18 | `Scene/Network`, `Network/Laws`, `Network/Fit` (S22 `80bb06b`): d3-sankey's layout, exact; bands that stack with no gap, sum to what enters or leaves, and a fitted scale that puts every column inside the room |
| W20 | `Scene/Units`, `Units/Laws` (S22 `80bb06b`): a bounded place as its slots, the count, the order and the front kept, marks that stand for k units; when the front leaves, each unit behind it updates to the slot before |
| W9 | `Run ctx t a b` and `Element.ofRun` (`Whatwg/Html/Node/Run.lean`, S22 `82630b1`): children under an ordered model in parts, a loop checked once, children whose tags are data by `Run.content`; `E.el e` of a variable `a` or `input` elaborates (`Content/Monotone.lean`). Left to the kernel: a list splice inside `html!` under an ordered model, written with `Element.ofRun` instead (debt D139) |
| W13 | `Region.withWords`, `withWordsRaw` (`Whatwg/Html/Node/Region/Words.lean`, S22): the figure names its words, the caption stays beside the picture, the words follow. Effect4's figure is `Region.withWordsRaw` (`tools/Tools/Document/Html.lean`); the site is unchanged byte for byte |

Effect4 pins `80bb06b` (S22, W18 and W20) since 2026-10-13; the move changed no byte of the site. Before
it, `ca3dca8` (K4 and the rest of S22), and before that
`bae6a2e`, whose figure words through the package changed no byte either. Before, `990ee7d` (S21, `18368e767`). The
page's rules are read by K2's tokens (`77bcd8141`); the shell is markup throughout and the site
passes the package's check (`6ad53e0ca`); tables and figures stand in the package's region
(`8fbb484d4`).
