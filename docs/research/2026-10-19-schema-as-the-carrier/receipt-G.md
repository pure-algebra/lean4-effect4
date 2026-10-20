# 2026-10-19 seat G receipt: the canonical defect alphabet, encoded as Effect writes a defect (move G)

**The one thing to know before merging:** every caller of the codec now passes the module's key
names first. The public operations are `Ty.encode names t v`, `Ty.decode names t j` and
`Ty.isCodecValue names t v`. The key spelling moved unchanged from `src/Effect4/Codegen/Types.lean`
to `src/Effect4/Program/Native.lean`. A branch that calls the codec, or that edits either file,
must follow both. Every step passes, `make check-ocaml` and `make check-ts` included.

## Base and head

Branch `refactor/phase1-phase3`, main checkout, no worktree. The base of the code is `fc9eb07c8`.
At the start the branch head was `b937be314`, the coordinator's research commit with the briefs.
That commit changes no code. The head of the code is `3197fde57`, and the commit of this receipt
follows it.

## Changed files

Hand-edited, the library:

1. `src/Effect4/Machine/Alphabets.lean`: `Defect.missingService (key : ServiceKey)`. `ofDefect`
   and `Defect.image` write the key at `Env.serviceKeyImage`, inside `ctor 3`. The docstring of
   `Defect.ofError` names the canonical alphabet. The image's three proofs name each case, with
   no `try`.
2. `src/Effect4/Program/Compile.lean`: `serviceLookupK` stores the key it looked up, and
   `missingScope` stores `Env.scopeKey`.
3. `src/Effect4/Machine/Stores.lean`: `missingScope` stores `Env.scopeKey`.
4. `src/Effect4/Program/Typed.lean`: the `missingService` arm of `reservedDefect`.
5. `src/Effect4/Program/Native.lean`: the key spelling, moved unchanged. It is `keyText`,
   `keyFromText`, `KeyNames`, `KeyNames.nameOf`, `KeyNames.keyOf`, `keySpelling` and
   `keyOfSpelling`.
6. `src/Effect4/Codegen/Types.lean`: the moved block is removed, and the module docstring names
   its new place.
7. `src/Effect4/Schema/Codec.lean`: the defect section and the key names. The defect's JSON is
   `encodeDefect` and `decodeDefect`. Their parts are `errorJson`, `serviceSpelling`,
   `serviceMessage`, `keyOfServiceSpelling?`, `serviceKey?`, `machineDefect?`, `machineObject?`
   and `strs?`. Each wire's encoder and decoder take the key names (`Wire.encode`,
   `Wire.decode`). So do `encodeReason`, `decodeReason`, `encodeCause`, `decodeCause`,
   `encodeRaw`, `decodeRaw`, `Prepared.encode`, `Prepared.decode`, `Prepared.isValue`, `isValue`,
   `encode` and `decode`.
8. `tools/Effect4Gen/guards/runner.lean`: the guard's `missingService` sample carries a key.

Hand-edited, the law graph:

9. `src/Effect4/Laws/Schema/Codec.lean`: every law takes the key names, and the defect lemmas are
   restated (the section on landed theorems).
10. `src/Effect4/Laws/Program/Folds/Ty.lean`: `encodeRaw.eq_cata` and `decodeRaw.eq_cata` take
    the names.
11. `src/Effect4/Laws/Program/Typed/AnswerSchema.lean` and `src/Effect4/Laws/Schema/Modeled.lean`:
    the decode theorems and `codec_roundtrip` take implicit names.
12. `src/Effect4/Laws/Author/Explain.lean`: `canonicalJson` encodes under the empty table.
13. The nine sites that build or match the defect. They are `Laws/Machine/ContextValue.lean`,
    `Laws/Machine/Witnesses.lean`, `Laws/Program/DenoteR.lean`, `Laws/Program/InterpR.lean`,
    `Laws/Program/BlockMeaning.lean`, `Laws/Program/Agreement.lean`,
    `Laws/Program/Agreement/Blocks.lean`, `Laws/Program/Typed/Commands/Clauses/Spawn.lean` and
    `Laws/Program/Typed/Commands/Evaluate.lean`.
14. `src/Effect4/Laws/Program/Typed/Denotation.lean`: the brief does not name this file. Two
    `decide` steps met the free key once `serviceLookupR` unfolds. Each is now a pair of `nomatch`
    refutations.

Hand-edited, the batteries, the harnesses, the probe and the engine:

15. `Test/Codegen/DataCodec.lean`: the empty table at each call, and the move-G section of
    controls.
16. `Test/Codegen/SchemaGenerationContract.lean`: the empty table at each call. The expected JSON
    `codecCauseJson` writes the user defect `7` raw.
17. `Test/Program/SchedContract.lean` and `Test/Program/PoolOps.lean`: the scope's key in each
    expected defect.
18. `Test/Program/H2PartOne.lean`: the admission theorems take the key, and `fullForbidden`
    matches `missingService _`.
19. `Test/Program/AnswerSchema.lean`, `Test/Schema/Modeled.lean` and
    `Test/Dogfood/P2HandlerLayers.lean`: the empty table at each call.
20. `harness/truth/Truth.lean`: `defectJson names` is `Schema.Codec.encodeDefect names`. The
    writers above it take the names, and `entry` reads them from the printing table's signature.
21. `harness/truth/run-truth.ts`: `defectWire` is gone. The `Die` case writes rc.112's own
    encoding, and the controls near its callers are rewritten. The AsyncFiberError marker is
    rc.112's `Error` object.
22. `harness/truth/schema-codec/Emit.lean` and `check.ts`: one case per defect form, and three
    named boundary differences.
23. `ocaml/engine/e4_engine.ml`: the two `Defect.MissingService` matches carry the key.
24. `ocaml/engine/kit/kit.ml` and `ocaml/engine/test/kit/test_shapes.ml`: the brief does not name
    them. The kit's exit shape changed with the defect. So the exit pin and `Kit.format_version`
    moved to 3, by the rule in `ocaml/engine/kit/kit.mli`.
25. `docs/research/2026-10-19-schema-as-the-carrier/probe/Faces.lean` and `expected.tsv`: the
    program's key names, and the four cases expect `equal`.

Regenerated:

26. `src/Effect4/Api/RunnerDerived.lean`, by `python3 scripts/generate.py --only derived`: the
    generated `Canonical` instance of `Defect` carries the key.
27. `ocaml/eff/eff_types.ml`, `ocaml/eff/eff_types.mli`, `ocaml/engine/api_engine.ml`,
    `ocaml/gen/closure_gen.ml`, `ocaml/gen/closure-api_gen.tsv` and
    `ocaml/gen/closure-api_engine.tsv`, by `make gen-lcnf`.
28. `docs/research/2026-10-19-schema-as-the-carrier/probe/out/lean.txt`, by the probe's first
    command.
29. This receipt, in its own commit.

## Commands and results

Every command ran from the checkout's root, one at a time, in the brief's order. The names below
abbreviate five strings:

- `run` is `python3 /private/tmp/seams-lean-one.py`, the runner. Every Lean command and every
  `make` target ran through it.
- `$S` is the scratch folder,
  `/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/2cfa2789-af6f-4183-90be-cdd7f2934e64/scratchpad/G`.
- `$P` is `docs/research/2026-10-19-schema-as-the-carrier/probe`.
- `tsgo` is `harness/truth/node_modules/.bin/tsgo`, version 7.0.0-dev.20260629.1. `bun` is 1.4.2.

Each time is the wall time that `/usr/bin/time -p` measured.

| Step | Command | Result |
| --- | --- | --- |
| 1 | `run lake build Effect4.Machine.Alphabets` | passed: 17 jobs, 2.78 s |
| 1 | `run lake build Effect4.Program.Compile` | passed: 71 jobs, 40.08 s |
| 1 | `run lake build Effect4.Schema.Codec` | first refused: `safeBound` stood after the defect section; the section moved after the numeric wires; then passed: 82 jobs, 1.12 s |
| 1, added | `run lake build Effect4.Laws.Schema.Codec` | first refused at three shapes: a wire lambda's type, a `do` block's layout, the `find?` step; then passed: 281 jobs, 10.17 s |
| 2 | `run python3 scripts/generate.py --only derived` | PASS, 114.41 s; `RunnerDerived.lean` moved, and no other output |
| 2 | `run lake build Effect4 Effect4.Laws`, in the background | pass 1 refused at `Typed/Denotation.lean`, 790.37 s; pass 2 passed: 1429 jobs, 316.50 s; pass 3, after a docstring repair in `Schema/Codec.lean`, passed: 1429 jobs, 865.10 s (00:57:43 to 01:12:08) |
| 3 | `run make batteries-touched BASE=fc9eb07c8` | first: 57 batteries, refused at `Test.Schema.Modeled`, an unqualified `encode`, 147.66 s; second: 57 batteries, 1376 jobs, 133.78 s, passed |
| 4 | `run lake build ProofGraph.AxiomAudit`, then `run lake env lean $S/AxiomAuditGCore.lean` | the core lines under Axiom output; 18.81 s |
| 4 | `run lake env lean $S/AxiomAuditGExplain.lean` | the `Explain` line under Axiom output |
| 5 | `run make gen-lcnf` | PASS, 85.49 s; six outputs moved; the public manifest's 382 rows unchanged |
| 5 | `run make gen-eff` | PASS, 17.74 s; nothing moved |
| 5 | `run make gen-wire`, `run make gen-cas`, `run make gen-fixtures` | PASS each: 5.90 s, 17.62 s, 43.31 s; nothing moved |
| 5 | `opam exec --switch=effect4 -- dune build @engine/fmt`, from `ocaml/` | exit 0 |
| 5 | `run make check-ocaml` | first refused at the kit's exit shape pin, 53.70 s; second, after the pin moved: passed, 23.56 s |
| 6 | `run lake env lean -M4096 --run harness/truth/schema-codec/Emit.lean harness/truth/schema-codec/.work/values.ts` | exit 0, 9.98 s |
| 6 | `tsgo --noEmit -p harness/truth/schema-codec/tsconfig.json` | exit 0, 0.28 s |
| 6 | `bun harness/truth/schema-codec/check.ts` | exit 0, 0.21 s: the PASS line below |
| 6, red | `bun check.ts` on two copies under `$S/lane`, one value altered in each | exit 1 each: `defectMissingScope: Lean/rc.112 encoding differs`, `defectUser: Lean/rc.112 encoding differs` |
| 6 | `python3 scripts/lean-imports.py harness/truth/Truth.lean`, then `run lake build` of its 19 modules | passed: 1292 jobs, 23.41 s |
| 6 | `run lake env lean -M4096 <flags> harness/truth/Truth.lean`, the flags from `python3 scripts/lean-imports.py --dynlibs` | exit 0, 15.32 s |
| 6 | `bun --no-install test` on the five files of `TRUTH_HOST_TESTS` | 27 pass, 0 fail |
| 6 | `bun harness/truth/run-truth.ts --self-test-errors`, then `--self-test-divergence` | 24 checks, 0 failures; 30 checks, 0 failures |
| 6 | `tsgo --noEmit -p harness/truth/tsconfig.json` | exit 0 |
| 6, red | the two self-tests on copies under `$S/red-truth`, one value altered in each | exit 1 each: `AsyncFiberError marker is rc.112's encoding`, `missing scope as rc.112 writes it` |
| 6, probe | `run lake build` of the probe's imports, then `run lake env lean --run $P/Faces.lean $P/out ../../../../../harness/truth/prelude.ts > $S/faces-stdout.txt`, then `head -n 40` of it into `$P/out/lean.txt` | 239 jobs; exit 0, 5.89 s; `lean.txt` moved at the four defect lines; the rest of stdout equals `out/census.txt` |
| 6, probe | `bun $P/run.ts > $P/out/bun.txt` | exit 0, 1.10 s; `bun.txt` unchanged |
| 6, probe | `bun $P/compare.ts` | exit 0: the classes line below |
| 6, red | `bun $P/compare.ts` on HEAD's `lean.txt`, then on a copy with one altered line | exit 1: the four cases `expected equal, observed differ`; exit 1 at `dieNat` |
| 7 | `run make check-ts` | passed, 32.11 s (01:24:23 to 01:24:55): the lane lines below; no file under `generated/` moved |

The codec lane's PASS line:

```text
PASS schema-codec: 60 fresh Lean/rc.112 comparisons, 60 host round trips, 17 host encodings observed by Lean decoders, 20 matching decoder refusals, 10 matching encoder refusals, 7 negative controls, 13 explicit boundary differences; 60 generated Schemas, 60 equal to rc.112's revival of their documents, 59 to its code of them (1 difference, its quoted __proto__ key)
```

The comparator's classes over the 40 cases:

```text
classes: equal 30, renamed 1, refusedBoth 8, refusedLean 1; renaming: 0→31; failures 0
```

The lines of `make check-ocaml`, second run:

```text
PASS native: shared result eaf806d6cc4c
PASS compiler: shared result 021d2acd37ac
test_kit: 61 checks, 0 failures
37 checks, 0 failures
test_transcript: 81 checks, 0 failures
test_rocq: 13 checks, 0 failures
PASS: 2 lawful aliases and 12 hostile sealed-package clients
PASS: 4 exported roots compile; 6 hidden roots are unbound
gen-check: PASS
PASS ocaml: recorded c5ae23316886 (14.382s)
```

The lane lines of `make check-ts`:

```text
PASS tsgo: shared result d14e5946e1e6
PASS assignability: no pair the order accepts is refused by the target
PASS target: recorded bbd2eb7f15b8 (18.761s)
PASS ts-reader: shared result 85bc027a0fc2
PASS tsdiag: recorded e148f3d9d7cc (2.363s)
PASS ingest-smoke: shared result dbb41fdddeea
PASS service identity: checked API emissions, inferred requirements, two TS2375 controls, four runtime outcomes
PASS service-identity: recorded f60b7eb3536a (3.639s)
```

## Axiom output

The walk ran over the 31 touched modules. Thirty of them gave the first two lines. They are the
eight core modules of the changed files, the fourteen law modules other than `Explain`, and the
eight batteries. The core modules are `Effect4.Machine.Alphabets`, `Effect4.Machine.Stores`,
`Effect4.Program.Native`, `Effect4.Program.Typed`, `Effect4.Program.Compile`,
`Effect4.Codegen.Types`, `Effect4.Schema.Codec` and `Effect4.Api.RunnerDerived`.

```text
#axiom_audit: 10034 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals
#axiom_audit: 10034 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals; checked: the walk's answers at 31565 constants agree with their captured graph, over the labels [propext,
 Quot.sound]
```

The thirty-first module, `Effect4.Laws.Author.Explain`, gave this line:

```text
#axiom_audit: 41 of 243 declarations reach axioms outside [propext, Quot.sound]
```

Each of the 41 is a `Tools.Explain` root that `Test/Audit/AxiomGate.lean` exempts by its exact
name (row 332), or a generated descendant of one. A script compared the 41 names with the gate's
list and found none outside it. `canonicalJson` is one of the 41. By reading, it renders through
`Effect4.Codegen.renderJson`, an exempt rendering declaration.

## Evidence

- **Proved:** `decode_iff`, `decode_encode`, `encode_of_hasTy`, `encode_injective`,
  `encode_of_decode`, `decode_of_encode`, `hasTy_decode` and `encode_sub` keep their statements,
  with the key names as one more implicit argument. All are in
  `src/Effect4/Laws/Schema/Codec.lean`. The raw laws `decodeRaw_normJ` and `decodeRaw_exact` hold
  at every table of key names. The walk reaches only `propext` and `Quot.sound`, and nothing rests
  on a planned goal.
- **Proved:** the defect decoder reads `normJ`'s quotient (`decodeDefect_normJ`). What it reads
  re-encodes to its JSON, modulo `normJ` (`decodeDefect_exact`).
- **Tested:** the move-G controls of `Test/Codegen/DataCodec.lean`, as finite evaluations. Each
  canonical form writes rc.112's JSON. Eleven distinct defects have eleven distinct encodings, and
  each decodes back, raw and through the public codec at `causeOf never`. The two red controls
  fail as their `#guard_msgs` expect.
- **Tested, host-only and bounded:** the codec lane, 60 Lean/rc.112 comparisons under bun, with
  two red mutants. Ten comparisons are the defect forms. Three named boundary differences record
  where the Lean codec refuses what rc.112's `Schema.Defect()` reads or writes.
- **Tested, host-only and bounded:** the truth harness's controls, 24 and 30 checks, with two red
  mutants. One control reads the AsyncFiberError marker against a real `runSyncExit` on rc.112.
- **Tested, host-only and bounded:** the faces probe, 40 programs on one machine and one host. The
  four defect cases are now `equal`.
- **Reading:** the closed world of `src/OCaml5/Eff/World.lean` holds no `Defect` family
  (`Tools.ProgramStructure.blocks`). So `src/OCaml5/Eff/Goldens.lean` has no defect golden, and
  none can be added; `make gen-eff` moved nothing.
- **Reading:** rc.112's lines, as the docstrings cite them. They are `Schema.ts:10844-10853`,
  `SchemaTransformation.ts:1081-1148`, `Context.ts:1481` and `:1591-1601`,
  `internal/core.ts:617`, and `internal/effect.ts:3772` and `:6185-6195`.

## Landed theorems and their placement

Eight helpers land in `src/Effect4/Laws/Schema/Codec.lean`, and two lemmas are restated. Two
lemmas are removed, `decodeDefect_obj_two` and `decodeDefect_obj_other`. Their one consumer was
the old `decodeDefect_normJ`. Every one serves the same claim:

- Concept: `exact-codecs` (concept 5); property: exactness modulo key sorting (`decode-iff`).
- Question: registry claim `decode-iff` (role `decidability`), pointer
  `Effect4.Schema.decode_iff`.
- Reach: every JSON value and every table of key names, with no other hypothesis. The normaliser
  is `normJ` (row 128).
- Does not establish: which defects the codec admits, the TypeScript face, or the host boundary.
- Unlocks: R3 (data). `decode_iff`, `decode_encode` and `encode_injective` stay proved over the
  new defect wire.

| Lemma | Statement, in words | Consumer |
| --- | --- | --- |
| `strs?_map_normJ` | `normJ` keeps a list's strings and its other values apart | `fieldStrs?_normJ` |
| `fieldStrs?_normJ` | an object's named string fields read alike from its key-sorted form | `machineObject?_normJ` |
| `machineObject?_normJ` | the machine-defect reader reads an object and its sorted form alike | `decodeDefect_normJ` |
| `decodeDefect_normJ` (restated) | the defect decoder reads a JSON and its sorted form alike, under any names | `decodeReason_normJ` |
| `strs?_exact` | a list that reads as strings is those strings | `machineObject?_exact` |
| `key_message` | `message` sorts before `name` in byte order | `normJ_errorJson_orders` |
| `normJ_errorJson_orders` | both orders of an `Error`'s object sort to `errorJson` | `machineObject?_exact` |
| `machineDefect?_exact` | the re-encode guard: what the reader answers encodes to that object | `machineObject?_exact` |
| `machineObject?_exact` | an `Error` object the reader reads is the defect's encoding, modulo `normJ` | `decodeDefect_exact` |
| `decodeDefect_exact` (restated) | what decodes as a defect re-encodes to its JSON, modulo `normJ` | `decodeReason_exact` |

`decodeDefect_exact` changes its statement. The encoder now answers an option, and an `Error`'s
object reads in either order. So the lemma states exactness modulo `normJ`, as
`decodeReason_exact` already did.

In `Test/Program/H2PartOne.lean`, `missingService_admitted_at_any_type` now holds for every key.
It is a battery reader of `strongExit_of_clean`, and no claim points at it.

## Open obligations

1. Which defects the codec admits has no proof. The proposed planned goal is in the last section.
   Its proof needs four steps that no lemma states yet. They are `nat? (Arch.Json.ofNat n) =
   some n` inside the bound (move J's open obligation 1), and `payloadOfHex? (payloadHex p) =
   some p`. They are `Store.decodeString` of the bytes after the message's head, and the spelling's
   retraction, which `keyOfSpelling_keySpelling` (`src/Effect4/Laws/Codegen/ReadLeaf.lean`) states.
2. `rocq/Eff_types.v` still declares `Defect_missingService` with no key. Its producer is
   `make gen-rocq`, on the opam switch `rocq`, which the brief does not name. No gate reads the
   file, and `make check-ocaml` passed with it as it is.
3. The retired truth lanes' committed outputs keep the old defect spellings. They are
   `harness/truth/corpus.json`, `harness/truth/result.json`, `harness/truth/result.md` and
   `harness/truth/corpus-results.tsv`. No target runs these lanes, and `make gen-truth` would
   write them again.
4. The frozen packet `Test/contracts/schema-codec.contract.md` still states the codec without key
   names. Its paragraph on defects still points at the truth harness's old payloads.
5. The note's §8 table and its findings 8.1 and 8.9 describe the defect carrier before this move.
   The brief keeps the note as it is, so this receipt's comparator line carries the classes.
6. `probe/out/lean-full.txt` is untracked, and it keeps the old defect lines.
7. A printed `Data.TaggedError` instance that dies is an `Error` on rc.112. The Lean codec writes
   the payload form `{"payload": hex}` for the same defect. The owner deferred the payload defect
   (R5), so this difference stays.
8. The raw `encodeDefect` writes one text for two keys under a table that names a key
   `effect/Scope`. The decoder refuses that text, so the public codec admits neither defect.
9. Part two of row 117 (`missingService` at an empty row) may read the stored key. This move does
   not touch that judgment.

## The open point of §11.2, and the refused cases

The defect stores the key, as the brief recommends. The machine has the key at both sites: the
key that `serviceLookupK` looked up, and the scope's key for `missingScope`. The codec takes the
key names as data (`KeyNames`), from the caller's signature.

- **The spelling.** `serviceSpelling names key` is `effect/Scope` for `Env.scopeKey`, rc.112's
  `scopeTag`. Every other key spells as `keySpelling names key`, the tag that `printKey` prints.
  The message is `Service not found: ` and the spelling.
- **The read-back.** `serviceKey?` reads the message's bytes after its head with
  `Store.decodeString`. It reads `effect/Scope` as the scope's key, and any other spelling by
  `keyOfSpelling`. `machineDefect?` keeps a candidate only where its encoding is the object read.
- **The scope's clash, refused.** A table can name another key `effect/Scope`. Then the text names
  two keys, and `keyOfServiceSpelling?` refuses it. `Test/Codegen/DataCodec.lean` holds the
  control `scopeClash`: the public codec writes neither missing service.
- **The other refusals.** The encoder refuses `error (tag n)` and `error boom`, which are not
  canonical. It refuses a user number past `safeBound`. The decoder refuses `{"boom": null}`, a
  number past the bound and the legacy wrapper `{"user": 7}`. It refuses an `Error` with a stack,
  and an `Error` that the machine never throws.

The key names enter at each wire's encoder and decoder, not at `prepare`. The brief lists
`prepare` and `Prepared` among the definitions that take the names. A wire's type, layout and
support read no key name, so `layout`, `isSupported` and `Compatible` stay judgments of the type.
`Prepared.encode`, `Prepared.decode` and `Prepared.isValue` take the names. Decision D-G1 below
records the choice.

## Decisions for the owner

**D-G1, where the key names enter the codec.**

- (a) As landed: each wire's encoder and decoder take the names, and `prepare` reads none. The
  layout and the support stay functions of the type alone.
- (b) As the brief lists: `wireAlgebra` takes the names, and so do `prepare` and `Prepared`. Then
  `layout` and `isSupported` either take the names too, or read a fixed table.

Recommended: (a). The names change no layout and no support, and (b) would make two type
judgments depend on a table that they never read. Nothing else in this landing depends on the
choice.

**D-G2, `rocq/Eff_types.v`.** The Rocq program types predate the key (open obligation 2).
Recommended: regenerate them with `make gen-rocq` in the slice that next compiles `rocq/`.

## Proposed decisions rows (proposals only)

None beyond part (2) of the note's row 421 (§11.3). One sentence could join part (2): "A missing
service's message spells its key as the printer spells the key's tag. A table that names another
key `effect/Scope` makes the scope's message refused."

## Proposed semantics registry text: the defect codec (proposal only)

Semantics generation is paused, so `generated/semantics.md` is not regenerated. The proposal has
three parts: a registry claim, its planned goal and its required property.

```lean
-- tools/ProofGraph/Registry.lean, under `-- 5. exact-codecs`
{ id := "defect-codec", concept := "exact-codecs", role := .compatibility
  title := "The defect's JSON is rc.112's Schema.Defect() form: a user number inside safeBound, a represented error's raw JSON, a machine defect's Error name and message; under one table of key names the codec reads back every defect it admits, so it is injective there (encode_injective at a cause type); admission is the canonical alphabet (Defect.ofError's normal form), the bound, and a missing service's spelling that names one key; nothing of rc.112's reading of other JSON, of a host exception outside the alphabet, or of the TypeScript face beyond the codec lane's finite check (the owner's ruling R5, move G)"
  pointer := .witness `Effect4.Schema.Codec.decodeDefect_encodeDefect },
```

```lean
-- src/Effect4/Laws/Schema/Codec.lean, namespace Effect4.Schema.Codec (decisions rows 203 and 207)
/-- The defects the codec admits under a table: canonical, inside the bound, and with a missing
service's spelling that names one key. -/
def defectAdmitted (names : KeyNames) : Defect → Bool
  | .user n => decide (n ≤ safeBound)
  | .error (.tag _) | .error .boom => false
  | .missingService key => keyOfServiceSpelling? names (serviceSpelling names key) == some key
  | _ => true

@[semantics "exact-codecs" (requirement := R3)]
proof_goal decodeDefect_encodeDefect (names : KeyNames) (d : Defect)
    (admitted : defectAdmitted names d = true) :
    (encodeDefect names d).bind (decodeDefect names) = some d
```

The required property, for concept 5 of `docs/core/semantics.md`:

- **The defect codec (`defect-codec`)**: under one table of key names, the codec writes each
  admitted defect as rc.112's `Schema.Defect()` writes the thrown value. It reads the defect back
  (`decodeDefect_encodeDefect`, `src/Effect4/Laws/Schema/Codec.lean`). An admitted defect is
  canonical, inside `safeBound`, and spells one key. It establishes nothing of rc.112's reading of
  other JSON, of a host exception outside the alphabet, or of the TypeScript face.
