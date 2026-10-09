# ECMA-262, the 2026 edition: the specification's source

The ECMAScript language specification, as its editors keep it: `spec.html` from
`tc39/ecma262` at the tag `es2026`. Its grammar is the standard the TypeScript printer's syntax
is checked against (`docs/research/2026-10-09-js-semantics-audit.md`, slice J9). The grammar
stands in 121 blocks `<emu-grammar type="definition">`: a production's name and parameters, then
its alternatives, one a line, with terminals in backquotes. A Lean rule that transcribes a
production cites its clause and its name, such as `spec.html#sec-conditional-operator`,
`ConditionalExpression`.

| File | What it is |
| --- | --- |
| `spec.html` | the specification's source, 2,979,557 bytes; git blob `e8bfc6c7526c22b5200613edf39f0efa56040f15` |
| `LICENSE.md` | its licence: Ecma's text copyright policy, alternative notice, for the prose |
| `SHA256SUMS` | the SHA-256 of both files |
| `fetch.sh` | downloads both again into a folder and verifies them |

Downloaded 2026-10-09 with the owner's permission. Nothing here is run: the files are data.
