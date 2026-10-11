# Seat SVG: inline SVG for lean4-whatwg (brief, 2026-10-11)

**First, the base.** Branch `html/svg` starts at this PC's `main` (`a13097f`). That `main` holds 163
commits that are not on GitHub. The HTML package lives on `origin/html-h7` (`2c6e3bc`), which
lean4-effect4 pins. Slice S0 merges the two.

## The seat

- Worktree `C:\Users\kokok\Dev\lean4-whatwg-svg`, branch `html/svg`. Edit nothing else.
- Read `AGENTS.md` and `COORDINATION.md` first. Record your claim in `COORDINATION.md` on your
  branch. After S0, read `docs/HTML-PACKAGE-PLAN.md`.
- Never push: the owner pushes. Commit by explicit paths.
- Run one `lake` at a time. The shell is PowerShell, so join commands with `;`, not `&&`.
- Stop at the end of each slice with the handoff that `AGENTS.md` ("Handoff") names.

## Why: the consumer

lean4-effect4 builds its documentation pages through `Whatwg.Html`: one document becomes a
`RawNode` tree, `Content.validIn` checks it, and `Print.renderDoc` writes it (its decisions row 353).
It wants inline SVG figures of program and machine structures:

- the classes and custom properties of its look tokens;
- `data-key` on every mark;
- CSS `@keyframes` in a `<style>` for motion;
- `<title>`, `<desc>` and the ARIA graphics roles.

Today `validIn` refuses `svg` ("not an element of the HTML Standard"). The stub
`Whatwg/Html/Svg.lean` declares nothing (ruling HP-9).

The consumer's code is in `C:\Users\kokok\Dev\lean4-effect4`. Read it with
`git -C C:/Users/kokok/Dev/lean4-effect4 show refactor/phase1-phase3:<path>`:

- `tools/Tools/View/Output.lean`: the SVG it writes as strings today;
- `tools/Tools/View/Tokens.lean`: its CSS;
- `tools/Tools/Document/Html.lean`: its page;
- `docs/research/2026-10-11-docgen/README.md`: its design.

## Who owns what

- **The HTML Standard** owns where `svg` and `math` may stand: embedded content. It also owns the
  switch into the SVG namespace at `svg` and the switch back at an HTML integration point
  (`foreignObject`, and SVG's `desc` and `title`). And it owns how the fragment serializer prints a
  foreign element: the raw-text rule holds for HTML's `style` and `script` only. This seam goes in
  `Whatwg/Html`, and the stub `Whatwg/Html/Svg.lean` becomes it.
- **W3C SVG 2** owns the elements, their content models by element category, their attributes and
  the attribute value grammars. This is a library `WhatwgSvg` under `Whatwg/Svg/`, beside
  `Whatwg/Html` (HP-9).

## Representation

- Keep `RawNode` as it is. A node's namespace is an inherited attribute of its path, as in the
  standard's tree construction: the checker and the printer carry it down. Add no namespace field
  and no raw-markup constructor.
- An attribute value grammar is typed first-order data, with a printer and a checker. Each has its
  retraction laws: `check (print v) = true` and `read (print v) = some v`.

## Slices

**S0, the base.** Merge `origin/html-h7` into `html/svg`.

- `git merge-tree` measured eight conflicts:
  - `.github/workflows/ci.yml`, `README.md`, `SPEC-MANIFEST.md`, `lakefile.toml`;
  - `Gates.lean`, which `main` deleted;
  - `Gates/HtmlStandard.lean`, `Gates/HtmlStandardEmit.lean` and `bin/HtmlStandard.lean`, which
    `html-h7` added under the old names: move them to `WhatwgGates/` and `whatwgbin/`.
- Exit: `lake build` green, and every gate row of `AGENTS.md` that applies.

**S1, the plan and the pin.**

- Write `docs/SVG-PACKAGE-PLAN.md` in the HTML plan's shape: authority order, proposed rulings
  `SV-n`, slices, and the anticipated proof graph.
- Pin the SVG 2 source: the svgwg repository's machine-readable definitions (`master/definitions*.xml`)
  at one commit. Seal it under `vendor/` with its `docs/PROVENANCE.md` row, then run
  `lake exe whatwg_vendorseal`.
- Check that those files hold what the plan needs: element names, categories, content models and
  attributes. If they do not, say so and propose another source.

**S2, the schema as data.**

- Write a projection gate in the shape of `HtmlStandard`/`HtmlStandardEmit`. It emits
  `generated/svg-*.tsv` and `Whatwg/Svg/Schema/*.lean`, under the drift gate.
- This is passive data: no theorem.

**S3, the seam.** It starts only after a breaker freezes its packet (`AGENTS.md`, "Development
order"). The behaviour:

- `validIn` admits `svg` where the HTML Standard does.
- It checks the subtree with the SVG checker, and returns to HTML at an integration point.
- The serializer escapes the text of an SVG `style` child.

Write the packet's proposal into the plan, with these red cases:

- `<p><svg>` admitted;
- `<svg><div>` refused;
- `<svg><foreignObject><div>` admitted;
- `<svg><style>a<b</style>` printed with `&lt;`;
- the names `viewBox` and `xml:space` printed as written.

**S4, the values.** `d` (path data), `viewBox`, `transform`, `points`, numbers and lengths.

This seat does S0, S1 and S2. S3 and S4 wait for a breaker's packet.
