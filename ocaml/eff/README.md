# effect4_eff — the Eff program IR as an OCaml library

`Eff`, the Effect program IR of this repository (`src/Effect4/Program/`), reified in OCaml.
It holds the program types, the canonical bytes Lean writes and reads, and the native tables.
Every module but the framing kernel is generated from Lean. A program's bytes are Lean's own
exact embedding, lowered by the LCNF route (`eff_image.ml`). The hand-written kernel frames them
(`eff_codec.ml`, over `eff_val.ml` and `eff_frame.ml`). A program's JSON is not this library's: it is Lean's own printer and located reader, lowered into `effect4_gen`
(`ShapeDoc.printTree`, `ShapeDoc.readLocated`, `src/Effect4/Store/Domain/ShapeJson.lean`). An OCaml host
reads and writes the programs Lean cuts. It does not type them — the typing has one face,
`effTy` in `src/Effect4/Program/Typing.lean` — and it does not run them; that is the engine
in `ocaml/engine`, under the generated machine.

Standard library only. OCaml 5.1.1 / dune 3.24 (opam switch `effect4`).

## Layout

| file | kind | what it is |
| --- | --- | --- |
| `eff_frame.ml` | hand | the framing kernel: `emit_*`/`decode_*` for the twelve tags, base-256 naturals, UTF-8 validation |
| `eff_val.ml` | hand | a value's canonical frames (`Val.encode`): the one writer and reader the engine's lanes compare values by |
| `eff_types.ml` | **generated** (the LCNF route, `make gen-lcnf`) | the program types, one OCaml variant, record or abbreviation per Lean family, spelled as the generated engines spell them; both engines open it |
| `eff_ctors.ml` | **generated** | `ctor_index_*` / `wire_tag_*` / `ctor_name_*` / `ctor_names_*` per family |
| `eff_layout.ml` | **generated** | the wire families and their fields, as data |
| `eff_image.ml` | **generated** (the LCNF route, `make gen-lcnf`) | Lean's exact embedding of a program, of each node sort, of a row table and of a program type (`Effect4.Run.Kit.programToVal`, `programOfVal`, …), lowered |
| `eff_codec.ml` | hand | a program's canonical bytes (`Wire.encodeProgram`, `Wire.decodeProgram`): `eff_image.ml` composed with the framing kernel; it decides nothing of its own |
| `eff_subterm.ml` | **generated** | the node sorts of `Effect4.Program.Node`, each constructor's children as (value argument index, child sort), the one-step `child`, and one witness per constructor with pairwise different children |
| `eff_native.ml` | **generated** | the native alphabet as data: atom names and const-generic metadata, the op values `all_ops` (`NativeOp.spelled`, one per spelling key; a read-modify-write row stands once, at its face), `scope_key`, the scope and context types; typing remains in Lean |
| `eff_manifest.txt` | **generated** | one line per family: name, OCaml type, constructors and their carriers, in order |
| `goldens/` | **generated** | for each program of the corpus (89 at 2026-10-20): `<name>.bin` (the canonical bytes, `Canonical.encode`), `<name>.json` (the program in `V`'s spelling, face 7's fixture format), `<name>.ty` (Lean's `typeOf`); `corpus.txt` (each name with Lean's `wellTyped` verdict); `coverage.txt` (constructor counts over the corpus). The engine's lanes and `ts/eff`'s printer test read the `.bin` files as programs |
| `goldens/val_*.hex` | **hand-derived** | `val_handle.hex`, `val_ref.hex` — two `Store.Val` trees derived by hand from `Val.lean`'s encoder on 2026-09-07, pending a Lean cut |
| `test/test_eff.ml` | hand | the codec's refusals and the wire kernel |
| `test/prop_wire.ml` | hand | the codec's property test on random untyped values |
| `test/test_lean_wire.ml` | hand | the lowering's finite check on Lean's own bytes (`ocaml/goldens/eff/*.hex`) |
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
the estate's one dune project, `ocaml/`:

```
eval $(opam env --switch=effect4 --set-switch)
cd ocaml && dune build eff && dune test eff
```

On Windows the same through WSL: `wsl -e bash ocaml/eff/tools/test.sh`.

## Regenerating

`make gen-eff` regenerates the tables, the subterm module, the manifest and the goldens from one
Lean tool that reads the families out of the environment (`src/OCaml5/Tools/EffGen.lean`). The
program types and the images are `make gen-lcnf`'s (`ocaml/eff/eff_types.ml`,
`ocaml/eff/eff_image.ml`, recipe `ocaml/gen/roots.json`), and the tables spell every name by
that route's rule. Each generated
file carries a `GENERATED … do not edit` header; a fix to a generated file belongs in the
tool. `make check-gen` refuses a committed generated file that differs from what the tool
emits.

The Lean-side hex goldens the lowering is checked against are a second tool,
`src/OCaml5/Tools/EffWire.lean` (`make gen-wire`), which writes `ocaml/goldens/eff`.

## The wire

Canonical bytes, as `src/Effect4/Store/Domain/Canonical.lean` frames every stored value:
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

`i` is the constructor's wire tag. For `Eff` and `NativeOp` it is the tag in
`tools/Effect4Gen/wire-tags.json`, which keeps a retired constructor's number, so it is not the
position (`yieldNow` is position 14 and tag 17). For the other families it is the 0-based index
in declaration order. `Var` is a `Nat`. The list families (`Terms`, `Stmts`, `Effs`) are inductives: `nil` = 0,
`cons head tail` = 1. `Op` is `NativeOp` throughout.

Decoding is length-directed — every frame is self-delimiting — and **exact**: trailing bytes,
a wrong tag, an out-of-range constructor index, a short payload, a non-canonical natural (a
leading zero digit), a bool byte other than 0/1, and invalid UTF-8 are all refusals, never
repairs. `Eff_codec.decode_program` reads the whole string as one value tree and that tree by
Lean's `programOfVal`, which re-encodes what it read and compares. A requirement row out of
order is no program's image: the OCaml list encodes it, and the reading refuses its bytes.

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
handle=12`. The last two are not program frames — no `Eff` constructor carries them, and the
program reading refuses them. They belong to the shared value carrier
`Effect4.Store.Val` (`src/Effect4/Store/Carrier/Val.lean`), whose encoder writes
`ref k d = framed 11 (k :: d)` — the kind byte then opaque digest bytes — and
`handle k n = framed 12 (k :: natBytes n)` — the kind byte then the key's `nat` digits, so
the key `0` is one kind byte and no digits. `Eff_frame` carries both so that an OCaml host can
read and write the value alphabet the machine layer shares; the refusals are the encoder's (a
payload with no kind byte, a key digit string with a leading zero, a key past `max_int`).

## What each test establishes

* `test_eff` — the codec's refusals. A constructor tag no program has, a missing or an extra
  argument and a requirement row out of order are refused at decoding. A negative natural is
  refused at encoding. The kernel's naturals, bools, strings and frames round-trip, and the
  kernel refuses the non-canonical forms above.
* `prop_wire` — 1 250 random values. A program built from each reads back through the codec,
  and its frames stop at their end. A trailing byte is refused, and no two programs share bytes.
  A row and a program type read back through their own images. Each value's JSON print reads back
  under Lean's lowered reader, or is refused for a natural above the profile's limit (2⁵³ − 1).
* `test_lean_wire` — the lowering's finite check (decisions row 391 (1)). Lean's own bytes
  (`Effect4.Program.Wire`, printed as hex by EffWire) decode through the lowered reader. The
  lowered writer re-encodes them to the same bytes. A trailing byte, a truncation, a wrong tag
  and a length past the end are refused. Lean's manifest must be this library's constructor
  tables, family by family.
* `test_val_frames` — the `ref` and `handle` frames against the two hand-derived goldens.

The engine differential (`ocaml/engine/test/test_diff.ml`, `make check-ocaml`) widens the
lowering's check to the whole printed corpus. Every `.eff` that `make corpus` wrote is one of 408
programs Lean cut with `Wire.encodeProgram`. Each must decode exactly here and re-encode to
Lean's bytes before the two engines run it.

## The laws and the lowering

Lean proves the codec's two laws for every program whose tree is well-formed
(`src/Effect4/Store/Domain/ProgramWire.lean`). `decode_encode` is the round trip. `decode_exact`
says that every byte string that decodes is that program's encoding. Both come from the class
`Canonical` (`src/Effect4/Store/Domain/Canonical.lean`), so trailing bytes, a leading zero digit
and a short payload are refusals by construction.

The OCaml codec runs that definition. `eff_image.ml` is `Canonical.toVal` and `Canonical.ofVal`,
lowered. `eff_val.ml` and `eff_frame.ml` are `Val.encode` and `Val.decode`, written by hand.
Decisions row 391 (1) trusts the lowering and keeps its finite checks: `test_lean_wire`, the
differential and `prop_wire`. They are the hand kernel's evidence too.

## What remains owed

* No theorem relates the hand kernel (`Eff_val`, `Eff_frame`) to `Val.encode` and `Val.decode`.
  The finite checks above are its evidence.
* `goldens/val_handle.hex` and `goldens/val_ref.hex` are hand-derived from `Val.lean`'s
  encoder, not cut by Lean; `src/OCaml5/Tools/EffWire.lean` is the tool that would cut them.
* Naturals above 2⁶² − 1 are refused, not encoded: the framing kernel's bound.
