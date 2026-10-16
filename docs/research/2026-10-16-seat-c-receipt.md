# 2026-10-16 seat C receipt: the C face, from routes to a C host over the wire frames

**The one thing to know before merging:** this seat adds a research note and a C prototype. It changes
no Lean, OCaml, script or gate file. The prototype's three tests pass. One is a differential
against Lean's compiled `Val.decode` and `Val.encode`, which needs a built core library in some checkout.

## Base and head

- Branch `claude/sad-williamson-6d3b65`, in the worktree `.claude/worktrees/sad-williamson-6d3b65`.
- Base: `81f9a4354` on `refactor/phase1-phase3`. The branch stood at `9187b9b60` (`main`), and
  `git switch -C` moved it to the base before any work.
- Head: `5efde1328`, the note and the prototype. This receipt is the next commit. Nothing is pushed.

## Changed files

- `docs/research/2026-10-16-c-interop/README.md`: the note. It covers the routes to C, C types as
  codes, strings and paths, a C host, the prototype's results, proposals, and limits.
- `docs/research/2026-10-16-c-interop/proto/e4val.h`, `e4val.c`: the value tree; the exact reader with
  located refusals; the checked writer; equality; rendering as `Val.render` writes it.
- `docs/research/2026-10-16-c-interop/proto/e4host.h`, `e4host.c`: the method layer (`e4_method`,
  `e4_serve`, `e4_serve_bytes`), the typed to-do host and its codecs, a repository in C, its broken twin.
- `docs/research/2026-10-16-c-interop/proto/fixture.h`, `fixture.c`: the scanner of the committed
  fixtures' hexadecimal frames.
- `docs/research/2026-10-16-c-interop/proto/test_val.c`: properties R1 to R7.
- `docs/research/2026-10-16-c-interop/proto/test_host.c`: properties C1 to C6.
- `docs/research/2026-10-16-c-interop/proto/lean_diff.c`: properties D1 to D3.
- `docs/research/2026-10-16-c-interop/proto/Makefile`: `make test`, `make test-san`, `make lean-diff`.
- `docs/research/2026-10-16-seat-c-receipt.md`: this receipt.

## Commands and results

The toolchain is Apple clang 21.0.0 (`arm64-apple-darwin25.2.0`) and GNU Make 3.81. Each command ran in
`docs/research/2026-10-16-c-interop/proto/`, except the first and the last.

| Command | Result line |
| --- | --- |
| `python3 scripts/check-language.py --strict docs/research/2026-10-16-c-interop/README.md` | `PASS check-language: no finding in docs/research/2026-10-16-c-interop/README.md; …` |
| `make clean && make test` | `PASS R1 111 of 111 fixture frames read and write back to their bytes` |
| | `PASS R4 111 of 111 frames exact under mutation: 128199 mutants, 10431 read and wrote back` |
| | `598 checks, 0 failures` (`test_val`), then `35 checks, 0 failures` (`test_host`) |
| `make test-san` | `598 checks, 0 failures`, then `35 checks, 0 failures`; no sanitizer report |
| `make lean-diff LEAN_LIBDIR=/Users/pooks/Dev/lean4-effect4/.lake/build/lib` | `PASS D1 D2 144978 inputs (124978 from the fixtures, 20000 random): both read 15781, both refuse 129197, disagree 0` |
| | `PASS D3 both sides read some inputs and refuse others: of the fixtures' inputs 7885 read, of the random 7896 read` |
| `lean_diff` built in the scratchpad against a copy of `e4val.c` whose boolean rule accepts any byte (a red control) | `FAIL D1 D2 136730 inputs …: both read 15447, both refuse 120787, disagree 496` |
| `nm -gU /Users/pooks/Dev/lean4-effect4/.lake/build/lib/libeffect4_Effect4.dylib` | exports `_lp_effect4_Effect4_Live_start`, `_Live_feed`, `_Live_view`, `_Api_Runner_stepBytes`, `_Store_Val_decode`, `_Store_Val_encode` |
| `python3 scripts/check-language.py --strict docs/research/2026-10-16-seat-c-receipt.md` | `PASS check-language: no finding in docs/research/2026-10-16-seat-c-receipt.md; …` |

## Axiom output

No Lean declaration changed. This seat ran no Lake, no `make check-*` and no `make batteries-touched`.

## Evidence

| Claim | Evidence | Bound |
| --- | --- | --- |
| The C reader and writer round-trip every committed frame, and refuse every proper prefix | tested | the 111 frames of the three fixture sets |
| The C reader accepts exactly what Lean's compiled decoder accepts, and the C writer gives Lean's encoder's bytes | tested | 144,978 inputs: the frames, their byte flips and prefixes, 20,000 seeded random frames |
| The differential detects a changed rule | tested | one red control: the boolean rule |
| The C host answers each recorded call of the to-do script with Lean's bytes, and ends each request in Lean's state | tested | seven requests; the model and the broken twin |
| An id past `uint64_t` is declined, located at its field | tested | one request |
| Route (a) fits "Eff runs anywhere" best | reading | an argument from rows 29, 381, 391 and 393 and the collation's §6 |
| `@[export]` is outside the axiom gate's refusals | reading | `Test/Audit/AxiomGate.lean` at the base |
| The map of C types to codes (§4.3 of the note) | proposed | tested only where the to-do codecs exercise it |
| fpath names Bünzli's library | reading | the installed `effect4` switch; the owner's intent is not confirmed |
| The differential's library holds the base's decoder | reading | the decoder's sources last changed in `d8bb17a40`; the library's file time precedes the base commit |

All evidence is host-only: C on one Mac. No claim rests on a theorem.

## Landed theorems and their placement

None.

## Open obligations

- LC-9's `@[export]` entries, and the reply entry of the note's §5.3. They touch `src/Effect4/Run/Live.lean`.
- A library target cut to the session's module closure. It touches `lakefile.toml`, the coordinator's.
- A C reader of the view's generated `Canonical` shapes, printed from their declarations.
- A printer of `Modeled` codecs for the C target, and the table of C type rows (the note's proposal 3).
- A measured layout per target profile (proposal 4).
- The prototype lives under `docs/research/`, outside every lane (proposal 7).
- If the owner meant another thing by "fpath", the note's §4.6 is the place to change.

## Proposed decisions rows (proposals only)

1. **The C host interface** (representation). A host in C is a table of methods over `Store.Val` frames.
   A method answers a status (declined, success, failure) and a value's frames. A request that does not
   read is declined with a located refusal. Lean's side builds the completion through a reply entry, as
   `Reactor.fallible` does, so C writes no cause alphabet. The same table serves routes (a), (b) and (c).
2. **C types as codes** (representation, refining row 393 (6)). A C type is a code that follows Ctypes,
   plus a layout that a target profile measures. Each pair of a `Ty` code and a C carrier has one
   behaviour (the note's §4.3). It is an exact embedding, a widening offered only as a named conversion,
   or a located refusal.
   A carrier narrower than its code refuses outside its range, as row 108 rules.
3. **Paths** (domain). A path is a declared type over `bytes`, read only in normal form. Normalization is
   a row of rc.112's `Path` service, and a path crosses to the TypeScript face only as UTF-8.
