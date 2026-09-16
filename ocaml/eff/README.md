# effect4_eff — the Eff program IR as an OCaml library

`Eff`, the Effect program IR of this repository (`src/Effect4/Program/`), reified in OCaml:
the canonical byte wire Lean decodes, the JSON printer and the native tables, all generated
from the Lean environment by one tool over a hand-written framing kernel. An OCaml host
reads and writes the programs Lean cuts. It does not type them — the typing has one face,
`effTy` in `src/Effect4/Program/Typing.lean` — and it does not run them; that is the engine
in `ocaml/engine`, under the generated machine.

Standard library only. OCaml 5.1.1 / dune 3.24 (opam switch `effect4`).

## Layout

| file | kind | what it is |
| --- | --- | --- |
| `eff_frame.ml` | hand | the framing kernel: `emit_*`/`decode_*` for the twelve tags, base-256 naturals, UTF-8 validation |
| `eff_json_text.ml` | hand | JSON string escaping and number/array/object assembly for the printer |
| `eff_types.ml` | **generated** | one OCaml variant/record per Lean inductive/structure, constructor order pinned, `ctor_index_*` / `ctor_name_*` / `ctor_names_*` per family |
| `eff_layout.ml` | **generated** | the wire families and their fields, as data |
| `eff_wire.ml` | **generated** | `encode_*` / `decode_*` per family, `*_exact` at the top level |
| `eff_json.ml` | **generated** | `print_*` per family (a printer only — there is no JSON parser anywhere) |
| `eff_native.ml` | **generated** | the native alphabet as data: atom names and const-generic metadata, the 55 op values `all_ops` and their rows `row_of`, `scope_key`, the handle types; typing remains in Lean |
| `eff_manifest.txt` | **generated** | one line per family: name, OCaml type, constructors and their carriers, in order |
| `program-structure.json` | **generated** | the constructor families the engine's layout check reads |
| `goldens/` | **generated** | for 48 programs: `<name>.bin` (the canonical bytes), `<name>.json` (the Lean JSON printer's output), `<name>.ty` (Lean's `typeOf`); `corpus.txt` (each name with Lean's `wellTyped` verdict); `coverage.txt` (constructor counts over the corpus) |
| `goldens/val_*.hex` | **hand-derived** | `val_handle.hex`, `val_ref.hex` — two `Store.Val` trees derived by hand from `Val.lean`'s encoder on 2026-09-07, pending a Lean cut |
| `test/test_eff.ml` | hand | the golden battery and the wire kernel |
| `test/prop_wire.ml` | hand | the wire property test on random untyped values |
| `test/test_lean_wire.ml` | hand | the differential against Lean's own encoder (`ocaml/goldens/eff/*.hex`) |
| `test/test_metadata.ml` | hand | Lean's metadata bytes decode and re-encode |
| `test/test_val_frames.ml` | hand | the `ref` (11) and `handle` (12) frames |
| `tools/*.sh` | hand | build and test drivers for WSL |

Until 2026-09-13 the library also carried a hand-written typing checker (`eff_typing.ml`),
a GADT authoring surface (`eff_typed.ml`), and four tests that re-derived Lean's typing rules
in OCaml. They were retired with the checking refactor: a second hand-written copy of the
typing judgement was drift with no consumer, the engine's random program generator that
was built on it is replaced by Lean's own printed corpus (`make corpus`), and the `.ty`
goldens stay as the typing's expected output.

## Build and test

`make check-ocaml` from the repository root runs everything below together with the engine
and seam checks, and writes the printed corpus the engine differential reads. By hand, from
inside `ocaml/eff` (its own project root, so its `_build` does not contend with the
`ocaml/` workspace):

```
eval $(opam env --switch=effect4 --set-switch)
cd ocaml/eff && dune build --root . && dune test --root .
```

or `cd ocaml && dune build eff && dune test eff` from the workspace root. On Windows the
same through WSL: `wsl -e bash ocaml/eff/tools/test.sh`.

## Regenerating

`make gen-eff` regenerates the five generated modules, the manifest, the goldens and the
engine's layout files from one Lean tool that reads the families out of the environment
(`src/OCaml5/Tools/EffGen.lean`, then `scripts/generate-engine-structure.py`). Each generated
file carries a `GENERATED … do not edit` header; a fix to a generated file belongs in the
tool. `make check-gen` refuses a committed generated file that differs from what the tool
emits.

The Lean-side hex goldens the differential compares against are a second tool,
`src/OCaml5/Tools/EffWire.lean` (`make gen-wire`), which writes `ocaml/goldens/eff`.

## The wire

Canonical bytes, as `src/Effect4/Store/Canonical.lean` frames every stored value:
`framed tag payload = tag :: be64 (length payload) ++ payload`, `be64` eight big-endian
bytes.

| value | bytes |
| --- | --- |
| `Unit` | `framed 9 []` |
| `Bool b` | `framed 1 [b ? 1 : 0]` |
| `Nat n` | `framed 2 (base-256 digits, big-endian, no leading zero; 0 = empty payload)` |
| `String s` | `framed 3 (utf8 bytes)` |
| `List xs` | `framed 4 (concat (encode x))` |
| `Option none` / `some x` | `framed 6 []` / `framed 7 (encode x)` |
| `a × b` | `framed 5 (encode a ++ encode b)` |
| constructor `i`, args `a₁…aₙ` | `framed 10 (encode (i : Nat) ++ encode a₁ ++ … ++ encode aₙ)` |
| a structure (one constructor) | as constructor 0 with its fields in declaration order |

`i` is the constructor's 0-based index in declaration order as the Lean environment reports
it. `Var` is a `Nat`. The list families (`Terms`, `Stmts`, `Effs`) are inductives: `nil` = 0,
`cons head tail` = 1. `Op` is `NativeOp` throughout.

Decoding is length-directed — every frame is self-delimiting — and **exact**: trailing bytes,
a wrong tag, an out-of-range constructor index, a short payload, a non-canonical natural (a
leading zero digit), a bool byte other than 0/1, and invalid UTF-8 are all refusals, never
repairs. `decode_program` returns `(value, bytes consumed)`; `decode_program_exact` refuses
anything left over.

Naturals are OCaml `int`: encoding refuses a negative, and decoding refuses more than eight
digits or eight digits above `max_int` (2⁶² − 1 on a 64-bit host). Lean's `Nat` is unbounded,
so a program carrying a literal above 2⁶² − 1 is outside this library's range and is refused
rather than truncated.

## Constructor index tables

`eff_manifest.txt` records the current constructor and field order, with carrier types.
`ocaml/goldens/eff/manifest.txt` records the wire subset, read directly from the Lean
environment by EffWire. Both are generated and drift-checked; consult those files for the
current tables, and `test_lean_wire` checks the two against each other.

Tags: `bool=1 nat=2 string=3 list=4 pair=5 none=6 some=7 bytes=8 unit=9 ctor=10 ref=11
handle=12`. The last two are not program frames — no `Eff` constructor carries them and the
program decoder refuses them at the tag comparison. They belong to the shared value carrier
`Effect4.Store.Val` (`src/Effect4/Store/Val.lean`), whose encoder writes
`ref k d = framed 11 (k :: d)` — the kind byte then opaque digest bytes — and
`handle k n = framed 12 (k :: natBytes n)` — the kind byte then the key's `nat` digits, so
the key `0` is one kind byte and no digits. `Eff_frame` carries both so that an OCaml host can
read and write the value alphabet the machine layer shares; the refusals are the encoder's (a
payload with no kind byte, a key digit string with a leading zero, a key past `max_int`).

## What each test establishes

* `test_eff` — every golden decodes exactly, re-encodes byte for byte and prints the JSON
  Lean printed; a trailing byte, a truncation, a flipped tag and a length past the end are
  refused; the kernel's naturals, bools, strings and frames round-trip and refuse the
  non-canonical forms above. The `.ty` beside each golden and the verdict column of
  `corpus.txt` are printed for the record; nothing in OCaml compares with them.
* `prop_wire` — `decode_*_exact (encode_* v) = Some v` and `decode_*` never reads past its
  frame, on 1 250 random values of every family, plus injectivity of `encode` on the sample.
* `test_lean_wire` — Lean's own encoder (`Effect4.Program.Wire`, printed as hex by EffWire)
  is an implementation of the byte rule independent of the one this library is generated
  from. Its manifest must be this library's constructor tables family by family, every hex
  golden must decode exactly and re-encode to Lean's bytes, and the programs the two corpora
  define identically must be byte for byte equal.
* `test_metadata` — Lean's metadata bytes decode and re-encode.
* `test_val_frames` — the `ref` and `handle` frames against the two hand-derived goldens.

The engine differential (`ocaml/engine/test/test_diff.ml`, `make check-ocaml`) widens the
third point to the whole printed corpus: every `.eff` that `make corpus` wrote — 408 programs
Lean cut with `Wire.encodeProgram` — must decode exactly here and re-encode to Lean's bytes
before it is run through the three engines.

## The open theorem

The wire's exactness is stated for a Lean seat, in `src/Effect4/Program/Wire.lean`'s terms,
with `encodeProgram : Eff NativeOp → Bytes` and `decodeProgram : Bytes → Option (Eff NativeOp)`:

```lean
/-- T2a (round trip). -/
theorem decodeProgram_encodeProgram (p : Eff NativeOp) :
    decodeProgram (encodeProgram p) = some p

/-- T2b (exactness / canonicity): every byte string the decoder accepts is the encoding of
    the program it produces — so there is exactly one byte string per program, and a decode
    never repairs. -/
theorem encodeProgram_decodeProgram {b : Bytes} {p : Eff NativeOp} :
    decodeProgram b = some p → b = encodeProgram p
```

T2b is the load-bearing half: with it, `decodeProgram` is a partial inverse whose domain is
exactly the image of `encodeProgram`, which makes trailing bytes, a leading-zero natural digit,
an out-of-range constructor index and a short payload refusals *by construction* rather than by
case analysis. The route: prove the framing lemma first — for `Store/Canonical.lean`'s
framing, `readFrame (framed t p ++ r) = some (t, p, r)` and conversely
`readFrame b = some (t, p, r) → b = framed t p ++ r` — then lift it through the mutual
`encEff`/`decEff` recursion, with a `natOfDigits`/`digits` canonicity lemma for the `Nat` case.

Evidence today: `Wire.lean` `#guard`s T2a and the two refusal corollaries on its own corpus.
On the OCaml side the same statements are tested on the 48 goldens, on the 8 Lean-authored
byte strings, on the 408 programs of the printed corpus and on 1 250 random values. Not
proved.

A third statement is what the differential measures and is not a Lean theorem, because one
side is OCaml code: for every `p : Eff NativeOp`, `Effect4.Program.Wire.encodeProgram p` and
`Eff_wire.encode_program (ocaml_of p)` are equal. It is discharged empirically on every
program Lean has published bytes for; widening `Wire.Corpus` or the generator's depth is the
cheapest way to strengthen it.

## What remains owed

* T2 is open.
* `goldens/val_handle.hex` and `goldens/val_ref.hex` are hand-derived from `Val.lean`'s
  encoder, not cut by Lean; `src/OCaml5/Tools/EffWire.lean` is the tool that would cut them.
* Naturals above 2⁶² − 1 are refused, not encoded.
