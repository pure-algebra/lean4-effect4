# effect4-eff — the Eff program IR as a TypeScript library

`Eff`, the Effect program IR of this repository (`src/Effect4/Program/`), in TypeScript:
the nodes as Effect Schema nodes, one function from TypeScript text into them, and the JSON
shape shared with Lean and OCaml. The counterpart of `ocaml/eff` for the TypeScript host.

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
| `readEff(0, ·)` | fragment → Eff, `Effect4/Codegen/Read.lean` clause for clause, one reader per head | `read.ts` § 3 |
| `decodeEff` | the node checked against the schema | `eff.gen.ts` |

A refusal is data (`Refusal`): Lean's seven `ReadRefusal` cases plus three for the layer
below them (`node`, `program`, `parse`).

## Files

| file | written by | what |
| --- | --- | --- |
| `read.ts` | hand | the function above; the only hand-written logic |
| `eff.gen.ts` | `src/Tools/TsGen.lean` | one Schema per family of the Eff IR and its typing (23 families: `Eff`, `Term`, `NativeOp`, `Ty`, `Row`, …), read off the Lean environment: names verbatim, constructors in declaration order; `decodeEff`, `isEff` |
| `json.gen.ts` | `src/Tools/TsGen.lean` | one JSON writer per family, the bytes `OCaml5.Eff.Goldens` writes and `ocaml/eff/eff_json.ml` prints; `toJson` |
| `profile.gen.ts` | `src/Tools/TsGen.lean` | the image profile as one JSON payload decoded at import through the schemas above: the address, the 37 reserved heads, and one entry per native operation, `{ op: NativeOp, row: Row }`; a stamp over the payload bytes is recomputed at import |
| `check.ts` | hand | the corpus differential (below) |
| `test/read.test.ts` | hand | the pinned cases |

No row type is written by hand: `Row`, `Ty`, `NativeOp` are families like any other, and the
profile's entries are values of those schemas. A `.gen.ts` file is written by
`./scripts/generate-ts-eff.sh` and never edited; `./scripts/check-ts-eff.sh` is the drift
gate, stamped and in the sweep, so a stale file fails the sweep and nobody runs a generator by
hand. Two carrier rules, stated in the generated header: a `nil`/`cons` family is
`ReadonlyArray`, an all-nullary family is a union of string literals.

## Check

The receipt is a differential against Lean's own reader: `./scripts/check-ts-eff-corpus.sh`
(host lane of the sweep; needs bun). It runs `src/Tools/Corpus.lean`, which writes 400
generated programs and the wire corpus as `.ts` (the printer's bytes) with a `.json` beside
each — the program Lean's reader gets back after the printer (`Api.roundTrip`) — then
`check.ts`, which reads every `.ts` here and must produce the same JSON bytes, then `bun test`.
A pass means: on every program of that corpus, this reader and Lean's reader agree. It does
not say anything about TypeScript the printer never wrote; such a file is refused by name.

By hand, the same thing:

```
lake build Tools
lake env lean -M4096 --run src/Tools/Corpus.lean <dir> 400 4
cd ts/eff && bun install && bun run check.ts <dir> ../../harness/truth/generated --oracle <dir>
```

## Pins

`effect@4.0.0-rc.112`, `oxc-parser@0.147.0`, `typescript@5.9.2` (`package.json`, exact).
The profile address in `profile.gen.ts` names the Effect and lean4-typescript revisions the
bytes were printed under; a program printed under another profile refuses at the head.
