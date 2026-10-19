# Wave 2: the cuts, why each one, and the seat briefs

Coordinator: the main session, 2026-10-18. Base: `refactor/phase1-phase3` at the commit that adds
this note. The plan is [README.md](README.md), amended by its §9. The owner asked for the reason
behind each cut before it starts. That means three things: what it improves in the semantics, how
it matches OCaml and compiler practice, and what is ours alone.

## 1. The one thing to know

Every cut in this wave applies one rule. Lean defines a behaviour once, and OCaml runs Lean's
definition. A hand OCaml copy of a Lean definition is not only a maintenance cost here. No theorem
reaches it, so it is a place where the laws stop.

Wave 1 added the shapes the cuts need: located refusals, one method table, export classes, the
name list, install metadata and model tests. It removed little. Measured with `measure.py` on the
merged tree before formatting (`5a9053fb3`), against the baseline:

| Measure | Baseline | After wave 1 |
| --- | --- | --- |
| hand OCaml lines | 43,477 | 44,488 |
| hand lines that twin Lean | 1,271 | 1,274 |
| `todo_gen.ml` definitions also in `api_gen.ml` | 1,429 | 1,430 |
| owners of the wire method names | 3 | 2 |

Wave 2 is where the twins go. The formatting commit (`94593523d`) spreads code over more lines,
so later waves compare with a baseline measured after it.

## 2. The rule, against the peers

**Compiler codebases.** Each intermediate language has one definition and one renderer.
Every tool links that one definition:
- the OCaml compiler keeps `Parsetree`, `Typedtree` and `Lambda`, each with its renderer, in
  `compiler-libs`, and its test suite links that library, never a copy;
- MLIR declares an operation once (ODS) and generates its class, verifier, parser and renderer;
- Cranelift writes instruction selection once (ISLE) and generates the Rust.

Our closure is the same idea: Lean's definitions, lowered through LCNF, are the one implementation.

**Jane Street OCaml.** A codec is derived from the type, never written by hand
(`[@@deriving sexp, compare, equal]`). A wire format is frozen in `Stable` modules, and
`bin_shape` digests catch a changed layout. Our generated codecs, the name list's append-only
check and explicit tags (ruling 1) are the same discipline. The deriver is Lean's `Canonical`
instance, lowered, not a ppx.

**CompCert.** An untrusted computation is checked by a proved validator, and the trusted rows sit
in one file. Ours is "OCaml computes, Lean decides": the lowering is trusted by decisions row 391,
and `OCaml5.Lcnf.Builtins` lists its rows.

## 3. What is ours

These four points set this tree apart from the peers above. Each cut is judged against them.
1. **Lean is the specification and the implementation at once.** The OCaml is Lean's own compiled
   code, not a second program verified against the first. So a hand OCaml twin is a third
   opinion with no law.
2. **Codecs are exact embeddings with laws** (`Canonical.ofJsonAnyOrder_exact`,
   `ShapeDoc.read_exact`). JSON libraries such as yojson state no exactness. When the OCaml path
   runs Lean's reader, the Lean theorem covers it, within the trust of row 391.
3. **Refusals are located values with a law.** A refusal is absent exactly when its judgment holds
   (`programRefusal_none_iff`). Compilers give located diagnostics, but they state no such law.
4. **Programs and runs are first-order data.** A run's journal replays to the run, and a
   specialization of a Lean definition is part of a lowered node's identity (R6.1).

## 4. The cuts

### 4.1 C5: one generated closure

| | |
| --- | --- |
| Now | Each test lane regenerates the machine. `todo_gen.ml` (28,250 lines) repeats 1,430 definitions of `api_gen.ml`; `modeled_gen.ml` repeats 25 and `ctors_gen.ml` one. |
| After | One closure from one recipe. Each lane's roots join it as `coverage`, and a generated facade per consumer re-exports what the consumer names. |
| Removes | 1,430 duplicate definitions; about 6.3 s of cold build CPU (probe 2's trace). |

**Semantics.** One Lean declaration lowers to one OCaml node. Today two copies of a definition can
come from different recipes or specializations and still share a name. After C5, one name has one
body, and R6.1's identity holds by construction: specialization, target profile and type owner.

**Idiom.** One library, many consumers, each seeing what its interface exports: `compiler-libs`
and the OCaml test suite, or a Jane Street library with its `.mli`.

**Ours.** The closure is computed from Lean's dependency graph, and wave 1's export classes decide
who sees each root. The install lane's red controls already show that an outside project cannot
name a coverage root.

**Acceptance.** The to-do, constructor, Modeled and Rocq lanes answer as before. No path of
`public-names.tsv` moves. A coverage root is unbound from outside, as today.

### 4.2 A2 and C6: one owner of carrier JSON, located and exact

These two slices are one piece of work (Codex's R4.1). A2 makes Lean's reader locate its refusals,
and C6 lowers that reader and deletes the OCaml twins. So one seat does both, A2 first.

| | |
| --- | --- |
| Now | `ShapeDoc.print`/`read` in Lean; `kit_json.ml` (539 lines), their arm-for-arm twin; `eff_json_text.ml` (75); generated `eff_json.ml` (373), a second spelling by a second generator. The tool's codec refusals say `unreadable` with no place. |
| After | Lean's located, exact reader and its printer, lowered. The kit, the MCP server and the `eff` tests use them. |
| Removes | `kit_json.ml`, `eff_json_text.ml`, `eff_json.ml` and `EffGen`'s JSON arm: about 990 lines. It also removes `kit_json.ml`'s caveat K1. |

**Semantics.**
- The JSON number domain becomes a type. Today the tree holds a number as a binary64 pattern, and
  K1's comment says the two spellings agree below 2^53. After C6, the profile reads naturals, and
  that agreement is a theorem over `CodecProfile.natLimit`.
- The OCaml reader becomes Lean's reader, so `Canonical.ofJsonAnyOrder_exact` covers it.
- A refusal names its place (`Located JsonSite JsonReason`). A site is a present value, a missing
  field at a present parent, or a place in the shape. Every refusal names one site, and Codex's
  `readLocated_site` states that it exists in the input or the shape.

**Idiom.**
- Derive the codec from the type, as `[@@deriving yojson]` does.
- Report a refusal as JSON Schema 2020-12's output format does: an instance location and a keyword
  location. `JsonSite.value` and `JsonSite.schema` are those two.

**Ours.**
- The reader is exact against a named normaliser (`ShapeDoc.order`).
- A refusal is a value with a law, not only a message.
- The sexp probe showed how lowering gets past the two blockers, binary64 numbers and
  `ByteArray.toList`: read bytes as `Nat` codes. An OCaml parser gives the tree, and lowered Lean
  does everything after it.

**Acceptance.**
- The kit's 408 corpus prints are unchanged.
- Probe 1's four `unreadable` refusals name `a.items[0][1]`, `sketch.program`, `q` and `at_[0]`.
- Red controls: a duplicate key, an extra field, a misspelt case and a natural above `natLimit`
  are refused, and `Option Unit` is refused as unsupported.

### 4.3 C4: the reference carriers, on evidence

| | |
| --- | --- |
| Now | Seven list twins of the engine's carriers (`e4_*_list.ml`) and the `Ref` instance over them (`api_engine_ref.ml`), all inside the installed `effect4_engine`. |
| After | Decided by a mutant campaign, as below. |

**Semantics.** The `Ref` instance has a real job. Its carriers copy Lean's list operations, so it
tells two failures apart. A divergence from `Api_engine_inst` blames a carrier, and one from
`Api_gen` blames an extern row. The property tests (`prop_trace`, `prop_memo`, …) also use the
twins as their models.

**The intentional version.**
1. Run the campaign: mutate each fast carrier, and record which check catches each mutant.
2. If `test_diff` against `Api_gen` catches every mutant the `Ref` instance catches, and the
   property tests keep a model, delete `Ref`. Each property test then takes its model from the
   stdlib list functions.
3. In every case, move what stays out of the installed library into a test library (H3). A
   client should not link the reference engine.

**Idiom.** A reference model belongs in the test tree, as qcheck-stm's models do in wave 1.

**Ours.** The reference that counts is Lean's semantics, lowered (`Api_gen`). A hand reference
earns its place only by catching what `Api_gen` cannot. The campaign measures exactly that.

### 4.4 C1: one session fixture

`Test/fixtures/session/requests.jsonl` and `ocaml/engine/test/kit/tool-requests.jsonl` are
byte-identical copies. No Lean file reads the copy under `Test/`: its readers are
`bench_tool.ml` and `scripts/check-mcp-protocol.py`. The OCaml copy becomes the one file, a
dependency of its dune tests, and the two readers move to it.

## 5. What waits, and why

| Slice | Why it waits |
| --- | --- |
| A4, the reply diet | It touches the protocol's replies, which A2 also touches. Wave 3, with A5 to A7. |
| H2, wrapping the four installed libraries | It renames every `Eff_types` reference, generated and hand, so it would collide with all three seats. It starts wave 3 as one mechanical commit. |
| H7, the kit's suppressed warnings | It edits the kit modules that C6 changes. It follows C6, in the same seat if time allows. |
| F1, the faces printed from Lean | It needs C5's facades and C6's lowered JSON. Wave 3. |
| Lane L, typed editing | The eleventh concept goes into `docs/core/semantics.md` first (ruling 5). |
| The six planned goals | The owner's rows 387 and 391 put building before proofs. Each goal's docstring names its route. |

## 6. The seat briefs

The rules of [wave1-briefs.md](wave1-briefs.md) hold, with these changes:
- The base is the commit that adds this note. Each worktree starts from it.
- Run `opam exec --switch=effect4 -- dune fmt` before each commit. `make check-ocaml` checks the
  format.
- `ocaml/gen/roots.json` is format v3. Add a root to a class list. A moved or dropped public path
  refuses `make gen-lcnf`; name any such change in the receipt.
- Run `make batteries-touched BASE=<base>` and `#axiom_audit` over each touched `src` or `Test`
  module.
- The receipt is `receipt-w2-<seat>.md` in this folder, force-added with the last commit.

### Seat 1: one JSON owner (`wt-w2-json`, branch `seat/w2-json`): C1, A2, C6

1. **C1.** Make `ocaml/engine/test/kit/tool-requests.jsonl` the one file. Delete
   `Test/fixtures/session/requests.jsonl`, and move its readers to the one file: `bench_tool.ml`,
   `scripts/check-mcp-protocol.py` and `test_tool.ml`'s header.
2. **A2.** Write Codex's R4.1 in Lean:
   - `JsonSite`, `JsonReason`, `ShapeDoc.readLocated`, `CodecProfile.readLocated`;
   - the laws `readLocated_erases`, `profileLocated_erases`, `profileLocated_exact`,
     `write_readLocated` and `readLocated_site`, each placed by `AGENTS.md`'s five items;
   - the tool's codec refusals carry the located refusal.

   Keep the old `Option` readers as projections until their callers move.
3. **C6.** Lower the located reader and the printer:
   - The profile's tree reads numbers as naturals, with a law that relates it to the binary64
     tree at `natLimit`.
   - Text reading follows the sexp probe: an OCaml parser (yojson, already a kit dependency)
     gives the tree, and lowered Lean does everything after it.
   - Move the kit, the MCP server and the three `eff` tests to the lowered reader and printer.
   - Then delete `kit_json.ml`, `eff_json_text.ml`, `eff_json.ml` and `EffGen`'s JSON arm.
4. If time remains, do H7: remove the kit's suppressed warnings and the dead code they hide.

Files you own: `src/Effect4/Store/Domain/ShapeRead.lean`, `Shape.lean`,
`src/Effect4/Tool/CodecProfile.lean`, their laws and batteries, `ocaml/engine/kit/`,
`ocaml/eff/`, `src/OCaml5/Tools/EffGen.lean`'s JSON arm, and the fixture files. In `roots.json`,
only add roots.

### Seat 2: the engine's reference and test hygiene (`wt-w2-engine`, branch `seat/w2-engine`): C4, H3, H5

1. **C4.** Run the campaign of §4.3 and record every mutant and the check that caught it. Delete
   `Ref` only if §4.3's condition holds.
2. **H3.** Move the reference carriers that stay, `Api_engine_ref` and `Corpora`, into a private
   test library. The installed `effect4_engine` keeps only what a client runs.
3. **H5.** Write one test-support library: `check`, the summary line, `Filename.temp_dir`. Move the
   engine's and the CAS's tests onto it, and retire the six temporary-folder variables.
4. Give each remaining hand module of `ocaml/engine/` and `ocaml/engine/cas/` its `.mli` (H8, the
   engine's part).

Files you own: `ocaml/engine/*.ml` outside `kit/`, `ocaml/engine/cas/`, `ocaml/engine/test/`
outside `kit/`, and their `dune` files. Do not touch `ocaml/engine/kit/` or the generated files.

### Seat 3: one closure (`wt-w2-closure`, branch `seat/w2-closure`): C5

1. Form one dependency graph from the v3 recipe. Check specialization and type-owner identity
   before two consumers share a node (R6.1, step 2).
2. Generate a facade per consumer. Move the to-do, constructor, Modeled and Rocq lanes onto the
   shared closure, one at a time. Check each lane's answers before deleting its old closure
   (R6.1, step 3).
3. Keep coverage roots out of the installed public facade. If one compiled unit cannot do both,
   use separate public and test emission scopes, as R6.1 says.

Files you own: `src/OCaml5/**`, `ocaml/gen/`, the lanes' generated files and their `dune` files,
and `ocaml/engine/test/install/` for any new red control.

## 7. What this note does not establish

- The cuts' sizes are this morning's measurements and today's line counts; the receipts measure
  them again.
- The peers are cited for the practice they share with us. No claim is made about their internals
  beyond what each section names.
- C4's outcome is open until the campaign runs.
- No cut changes a judgment's meaning. A2 adds a located refusal beside each existing reader, and
  `readLocated_erases` relates the two.
