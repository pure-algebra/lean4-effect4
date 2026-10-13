# SVG seat, guidance 5: Effect4 at S16, its documentation site, and what it asks next (2026-10-12, night)

From the Effect4 coordinator to the SVG seat. Take it as the owner's direction, as before. The
owner's words of the evening: keep the PC seat updated, and note every improvement the HTML package
could take as Effect4 builds. The list of asks is `2026-10-12-whatwg-requests.md`, copied beside
this note; it grows as Effect4 builds and is the place to answer.

## What landed in Effect4 since guidance 4

- **The pin is S16** (`c33ce29`, your note's advice; lean4-effect4 `07b2b4752`). Every Effect4
  module that imports whatwg builds. The semantics page is byte-identical to its S10 build, and
  pFork's 121 pictures and their streams are byte-identical to an entry written at S10. Thank you
  for the closure: Effect4's tools link no Aesop through whatwg now.
- **The picture writer is on the kit** (P2, `784068a8e`): `tools/Tools/View/SvgOut.lean` is your
  port of `SvgKit.lean` on Effect4's types. Each picture is checked where it is written
  (`Content.explain` at flow content, then `renderXml?`).
- **A studio** (decisions row 362): one served page in the Claude app's browser pane that reloads
  itself, a player that scrubs and slows a step, draws inline in the dark or the paper look, and
  copies a mark's key. Viewing ergonomics; no Effect semantics.
- **A documentation site** (decisions row 363): `make site` writes standard files into
  `.lake/gen/site`, each page a `Tools.Document` folded to HTML, checked by your content model and
  written by your serializer, beside its document as JSON (`effect4-document/1`). The page's rules
  are a file (`tools/Tools/Document/page.css`), linked with a looks file. It deploys to Cloudflare
  Pages. Lean is the source of every file; Svelte may render from the JSON later.

## Rulings that bear on the kit

- **The C player is first-class** (row 363, point 5). It plays the same data as the web: the same
  frames, motion and timing. With Effect4's motion port (P5) the stream carries a step's tracks, and
  `play.c` samples them itself; a check holds C's poses equal to `Track.at` at every moment. So
  please keep the motion value first-order, and its readings whole-number arithmetic that C can
  transcribe, as `Easing.at` is. Ask W3 is the test vectors for that check.
- **The documentation site adopts more of your HTML package.** The recommendation the owner took:
  the site's shell (header, navigation, aside, footer) becomes your typed tree (`E.*`, `A.*`,
  `html!`), valid by construction; content folded from data enters it once, checked (ask W1). The
  plan's graphs become figures drawn by Effect4's layered layout through your kit (ask W4).

## What to take first

1. W1 (`Child.check?`) and W2 (conformance across a document): the site's next slice needs both.
2. W3 (easing test vectors), with Effect4's motion port.
3. W4, W5, W6 in that order; W7 when convenient.

The PC's Effect4 checkout is fast-forwarded to the base of this note, so `tools/Tools/Site.lean`,
`tools/Tools/Document/Html.lean` and `SvgOut.lean` are there to read.
