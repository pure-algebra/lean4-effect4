# effect4-eff — the Eff program IR as a TypeScript library

`Eff`, the Effect program IR of this repository (`src/Effect4/Program/`), in TypeScript:
the nodes as Effect Schema nodes, one function from TypeScript text into them, and the JSON and canonical byte
formats shared with Lean and OCaml. The counterpart of `ocaml/eff` for the TypeScript host.

## The function

```ts
import { readTypeScript } from "./read.ts"      // (source: string) => Result<Eff, Refusal>
import { toJson } from "./json.gen.ts"          // (eff: Eff) => string
```

`readTypeScript` is the whole path, in order:

| step | from → to | where |
| --- | --- | --- |
| `parseSync` | text → oxc's ESTree | oxc-parser 0.147.0 |
| `programExprOf` | the one expression a program file holds (bare, or `export const x = …`) | `read.ts` § 2 |
| `exprOf` | ESTree → the fragment the Lean printer emits; any other node refused by type name | `read.ts` § 2 |
| `readEff(0, ·)` | fragment → Eff, `src/Effect4/Codegen/Read.lean` clause for clause, one reader per head | `read.ts` § 3 |
| `decodeEff` | the node checked against the schema | `eff.gen.ts` |

A refusal is data (`Refusal`): Lean's seven `ReadRefusal` cases plus three for the layer
below them (`node`, `program`, `parse`).

The reader includes the printed service and provision operations and all eight Layer
forms. Layer effect bodies start with an empty variable environment. Service keys retain
both numeric fields and the native signature's type argument; a key outside JavaScript's
safe-integer range is refused. Lean's key round-trip theorem covers arbitrary natural
numbers, so its domain is wider than this host representation.

## Files

| file | written by | what |
| --- | --- | --- |
| `read.ts` | hand | the printed-image reader above |
| `eff.gen.ts` | `tools/Tools/TsGen.lean` | one Schema per family of the Eff IR and its typing (24 families: `Eff`, `Term`, `NativeOp`, `Ty`, `Row`, …), read off the Lean environment: names verbatim, constructors in declaration order; `decodeEff`, `isEff` |
| `json.gen.ts` | `tools/Tools/TsGen.lean` | one JSON writer per family, the bytes `OCaml5.Eff.Goldens` writes and `ocaml/eff/eff_json.ml` prints; `toJson` |
| `profile.gen.ts` | `tools/Tools/TsGen.lean` | the image profile as one JSON payload decoded at import through the schemas above: the address, the 50 reserved heads, and one entry per native operation, `{ op: NativeOp, row: Row }`; a stamp over the payload bytes is recomputed at import |
| `taxonomy.gen.ts` | `tools/Tools/TsGen.lean` | 23 refusal codes, their spectra, detail templates and active/reserved status; stamped at import |
| `forms.gen.ts` | `tools/Tools/TsGen.lean` | 19 relative expansion templates, argument classes, host citations, dual arities and four unambiguous lambda shapes; `takeAndBump` stays named; stamped at import |
| `wire.gen.ts` | `tools/Tools/TsGen.lean` | one canonical byte writer per family, including `encodeProgram`; explicit work stack, exact natural-number checks and strict Unicode strings |
| `check.ts` | hand | the corpus differential against Lean's JSON and wire (below) |
| `check-styles.ts` | hand | construction checks over all indexed foreign sources with TypeScript and oxc, recycling parser children after 128 files |
| `test/read.test.ts` | hand | the pinned cases |

No row type is written by hand: `Row`, `Ty`, `NativeOp` are families like any other, and the
profile's entries are values of those schemas. A `.gen.ts` file is written by
`scripts/generate-ts-eff.sh` and never edited; `scripts/check-ts-eff.sh` is the drift
gate, stamped and in the sweep, so a stale file fails the sweep and nobody runs a generator by
hand. Two carrier rules, stated in the generated header: a `nil`/`cons` family is
`ReadonlyArray`, an all-nullary family is a union of string literals.

## Check

The receipt is a differential against Lean's own reader: `scripts/check-ts-eff-corpus.sh`
(host lane of the sweep; needs bun). It runs `tools/Tools/Corpus.lean`, which writes 400
generated programs and the wire corpus as `.ts` (the printer's bytes) with a `.json` and `.eff` beside
each — the program Lean's reader gets back after the printer (`Api.roundTrip`) — then
`check.ts`, which reads every `.ts` here and must produce the same JSON and wire bytes, then `bun test`.
A pass means: on every program of that corpus, this reader and Lean's reader agree. It does
not say anything about TypeScript the printer never wrote; such a file is refused by name.

By hand, the same thing:

```
lake build Tools
lake env lean -M4096 --run tools/Tools/Corpus.lean <dir> 400 4
cd ts/eff && bun install && bun run check.ts <dir> ../../harness/truth/generated --oracle <dir>
```

## Foreign spelling corpus

`Tools.Corpus --styles <dir> 400 4` constructs foreign target syntax beside the
original Lean JSON and wire oracles. Each isolated axis runs the full printed corpus,
seven targeted probes and all 19 form examples at four surrounding depths. The full
Cartesian product of nine axes runs a composite probe: five pipe modes, eight duration
spellings, three import modes, three trivia modes, and five Boolean choices (lambda
replacement, omitted fork options, one-parameter release, omitted empty else, field order).
`Tools.Styles` owns rendering; `Effect4.Codegen.Styles` owns the structured syntax.

```sh
lake build Tools.Corpus
lake env lean -M4096 --run tools/Tools/Corpus.lean --styles .lake/ingest-styles 400 4
cd ts/eff && bun run check-styles.ts ../../.lake/ingest-styles
```

This construction check proves neither foreign recognition nor runtime agreement.
The later two-engine gate must recover each oracle exactly. The table reserves
`E-HELPER-UNPINNED`; it does not claim active-code fixture reachability before that gate.
The wire writer takes exact safe integers because the generated host carrier is `number`;
Lean's natural-number domain is wider. It rejects unpaired UTF-16 surrogates instead of
letting `TextEncoder` replace them.

## Pins

`effect@4.0.0-rc.112`, `oxc-parser@0.147.0`, `typescript@5.9.2` (`package.json`, exact).
The profile address in `profile.gen.ts` names the Effect and lean4-typescript revisions the
bytes were printed under; a program printed under another profile refuses at the head.
