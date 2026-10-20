# 2026-10-19 seat J receipt: one numeric bound on the nat wire (move J)

**The one thing to know before merging:** three pinned guards in
`Test/Codegen/SchemaGenerationContract.lean`, a file the brief does not name, now read `none`
under the ruling. Every step passes, `make check-ts` included, and the codec lane ran from a
byte-identical copy, since `check.ts` reads no argument.

## Base and head

Branch `refactor/phase1-phase3`, main checkout, no worktree. Base `ccba8e92d`. Head of the code:
`04fa8d57c`; the commit of this receipt follows it.

## Changed files

1. `src/Effect4/Schema/Codec.lean`: `natJson`, `natVal?` and `natWire` stand beside `intJson`,
   `int?` and `intWire`, and `wireAlgebra.ty_nat` is `natWire`. The docstrings of `safeBound` and
   `nat?` name both bounded wires, and `safeBound` cites rc.112's `isInt` by line.
2. `src/Effect4/Laws/Schema/Codec.lean`: two helpers, `natVal?_normJ` and `natVal?_exact`. The
   nat arms of `decodeRaw_normJ` and `decodeRaw_exact` take them. No statement changes.
3. `Test/Codegen/DataCodec.lean`: the brief's six controls, in a new section.
4. `Test/Codegen/SchemaGenerationContract.lean`: the brief does not name this file. Three guards
   pinned the unbounded nat wire: the encoder at 2^53 and 2^53 + 2, and the decoder at 2^53.
   They now read `none`, and two comments say why.
5. `harness/truth/schema-codec/Emit.lean`: `natAtBound` (2^53 - 1) joins the encoding cases.
   `natAboveBound` (2^53) joins the decoding refusals and the encoding refusals.
6. `harness/truth/schema-codec/check.ts`: `check` reads `natAtBound`, and both refusal loops read
   `natAboveBound`, each against rc.112's generated natural Schema.
7. `docs/research/2026-10-19-schema-as-the-carrier/probe/expected.tsv`: `exactBound` moves from
   `refusedEffect` to `refusedBoth`.
8. `docs/research/2026-10-19-schema-as-the-carrier/probe/out/lean.txt`: regenerated. Its
   `exactBound` line now reads `refused`, and no other file of `out/` moved.
9. `docs/research/2026-10-19-schema-as-the-carrier/receipt-J.md`: this receipt, in its own commit.

The lane's `tsconfig.json` needs no repair. It names `check.ts` and `../node_modules/@types`, and
both exist.

## Commands and results

Every command ran from the checkout's root, one at a time, in the brief's order. The names below
abbreviate four strings:

- `run` is `python3 /private/tmp/seams-lean-one.py`, the runner.
- `$S` is the scratch folder,
  `/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/2cfa2789-af6f-4183-90be-cdd7f2934e64/scratchpad/J`.
- `$L` is `$S/lane/schema-codec`, the lane's copy, and `$P` is
  `docs/research/2026-10-19-schema-as-the-carrier/probe`.
- `tsgo` is `harness/truth/node_modules/.bin/tsgo`, version 7.0.0-dev.20260629.1. `bun` is 1.4.2.

Each time is the wall time that `/usr/bin/time -p` measured. A first pass ran steps 1 to 6. A
docstring and comment repair followed, and the table holds the second pass on the final tree.

| Step | Command | Result |
| --- | --- | --- |
| 1 | `run lake build Effect4.Schema.Codec` | passed: 81 jobs, 4.27 s |
| 1 | `run lake build Effect4.Laws.Schema.Codec` | passed: 280 jobs, 16.09 s |
| 2 | `run lake build Effect4 Effect4.Laws`, in the background | passed: 1429 jobs, 645 compiled, 858.01 s (23:36:46 to 23:51:04) |
| 3 | `run lake env lean Test/Codegen/DataCodec.lean` | exit 0, no message, 2.24 s |
| 3, red | `run lake env lean $S/DataCodecRed.lean`, a copy whose 2^53 encoder guard holds the base's answer | exit 1 at that guard: did not evaluate to `true` |
| 4 | `make batteries-touched BASE=ccba8e92d` | `batteries-touched: 2 batteries`, `Test.Codegen.DataCodec` and `Test.Codegen.SchemaGenerationContract`; 360 jobs, 4.04 s |
| 4, added | `run lake build Test.Schema.Modeled Test.Dogfood.P2HandlerLayers Test.Program.AnswerSchema` | passed: 1132 jobs, 5.27 s; the three batteries reach the codec through `encode` and `decode` only |
| 5 | `run lake build ProofGraph.AxiomAudit`, then `run lake env lean $S/AxiomAuditJ.lean` | the first line under Axiom output; 1.94 s |
| 5, added | `run lake env lean $S/AxiomAuditJChecked.lean`, with `#axiom_audit checked` | the second line under Axiom output; 2.30 s |
| 5, added | `run lake env lean $S/NatAdmissionProbe.lean` | `inputs 4806, admitted 4513, disagreements 0`; red control: the base's wire disagrees on 142 inputs, the first 2^53 |
| 5, added | `run lake env lean $S/UnionProbe.lean` | exit 0: `nat \| number` normalizes to `number` and keeps 2^53; the raw union spelling refuses it |
| 6 | `run lake env lean -M4096 --run harness/truth/schema-codec/Emit.lean $S/values.ts` | exit 0, 1.99 s; the bytes equal the first pass's |
| 6 | `cp` of `check.ts` and `tsconfig.json` to `$L`, and of `$S/values.ts` to `$L/.work/values.ts`, then `cmp` of each copy | identical |
| 6 | `tsgo --noEmit -p $L/tsconfig.json` | exit 0, 0.27 s; `--listFiles` names 347 files, the two copies among them |
| 6 | `bun $L/check.ts` | exit 0, 0.18 s: the PASS line below |
| 6, red | `tsgo` on a copy whose `natAtBound` value is a string | exit 1: TS2345 |
| 6, red | `bun` on three copies of the values, one line mutated in each | exit 1 each: `natAboveBound: Lean encoder must refuse`, `natAboveBound: Lean must refuse`, `natAtBound: Lean/rc.112 encoding differs` |
| 6, literal | `tsgo --noEmit -p harness/truth/schema-codec/tsconfig.json`; `bun harness/truth/schema-codec/check.ts $S/values.ts` | exit 1 each, on the lane's work file of 2026-10-18: TS2339 at `natAtBound`; `natAtBound: no generated Schema` |
| 6, probe | `run lake env lean --run $P/Faces.lean $P/out ../../../../../harness/truth/prelude.ts > $S/faces-stdout.txt`, then `head -n 40 $S/faces-stdout.txt > $P/out/lean.txt` | exit 0, 6.09 s; `lean.txt` differs from HEAD at `exactBound` only; the rest of stdout equals `out/census.txt` |
| 6, probe | `bun $P/run.ts > $P/out/bun.txt` | exit 0, 1.10 s; `bun.txt` unchanged |
| 6, red | `bun $S/probe-red/compare.ts $P/out/lean.txt $P/out/bun.txt`, a copy of `compare.ts` beside HEAD's `expected.tsv` | exit 1: `FAIL exactBound: expected refusedEffect, observed refusedBoth` |
| 6, probe | `bun $P/compare.ts` | exit 0: the classes line below |
| 7 | `make check-ts` | passed, 39.64 s (23:53:07 to 23:53:47): the lane lines below; no file under `generated/` moved |

The codec lane's PASS line:

```text
PASS schema-codec: 50 fresh Lean/rc.112 comparisons, 50 host round trips, 17 host encodings observed by Lean decoders, 20 matching decoder refusals, 10 matching encoder refusals, 7 negative controls, 10 explicit boundary differences; 50 generated Schemas, 50 equal to rc.112's revival of their documents, 49 to its code of them (1 difference, its quoted __proto__ key)
```

The comparator's classes over the 40 cases:

```text
classes: equal 26, differ 4, renamed 1, refusedBoth 8, refusedLean 1; renaming: 0→31; failures 0
```

The lane lines of `make check-ts`:

```text
PASS tsgo: shared result d14e5946e1e6
PASS assignability: no pair the order accepts is refused by the target
PASS target: recorded 8bce434a920d (18.738s)
PASS ts-reader: recorded 85bc027a0fc2 (4.535s)
PASS tsdiag: shared result acd5929a66b7
PASS printed: 408 exact JSON/wire comparisons on each parser with shared form lowering; batch bound 500
PASS ingest-smoke: recorded dbb41fdddeea (1.412s)
PASS service identity: checked API emissions, inferred requirements, two TS2375 controls, four runtime outcomes
PASS service-identity: recorded 6f139d95258b (2.332s)
```

## Axiom output

`#axiom_audit Effect4.Schema.Codec Effect4.Laws.Schema.Codec`, then the same walk with `checked`:

```text
#axiom_audit: 665 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals
#axiom_audit: 665 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals; checked: the walk's answers at 4876 constants agree with their captured graph, over the labels [propext,
 Quot.sound]
```

## Evidence

- **Proved:** `decodeRaw_normJ`, `decodeRaw_exact`, `encode_of_decode`, `decode_iff`,
  `decode_encode`, `encode_of_hasTy` and `encode_injective` keep their statements over the bounded
  nat wire. All are in `src/Effect4/Laws/Schema/Codec.lean`. The audit walk reaches only
  `propext` and `Quot.sound`, and nothing rests on a planned goal.
- **Tested:** the six controls of `Test/Codegen/DataCodec.lean` and the three flipped guards, as
  finite evaluations. A red copy shows that the 2^53 encoder guard fails at the base's answer.
- **Tested, finite probe:** at `nat`, codec admission agrees with `n ≤ safeBound` on 4806 named
  inputs. This supports the proposed planned goal and proves nothing.
- **Tested, host-only and bounded:** the codec lane, 50 Lean/rc.112 comparisons under bun, with
  three red mutants. Both faces write 2^53 - 1, and both refuse 2^53 when encoding and decoding.
- **Tested, host-only and bounded:** the faces probe, 40 programs on one machine and one host.
  `exactBound` is now refused on both faces, by Lean's codec and by the prelude's arithmetic.
- **Reading, by search:** `ocaml/gen/closure-api_gen.tsv` lists no `Effect4.Schema.Codec`
  declaration. So the change reaches no lowered code, and no OCaml generation follows.
- **Tested, finite probe:** a union of `nat` with `number` or `int` reaches the public codec as
  its widest member (`normalizeRow`, `src/Effect4/Program/Ty.lean`). At `nat | number`, the
  number wire keeps 2^53, so the bound refuses nothing there.
- **Reading:** this move does not bound the defect, error and interruptor numbers, which read
  through `nat?` (open obligation 2).

## Landed theorems and their placement

Two helpers land in `src/Effect4/Laws/Schema/Codec.lean`. No statement of an earlier theorem
changes. The nat arms of `decodeRaw_normJ` and `decodeRaw_exact` now take the two helpers.

`natVal?_normJ`: the bounded natural reader reads a datum and its key-sorted form alike.

- Concept: `exact-codecs` (concept 5); property: exactness modulo key sorting (`decode-iff`).
- Question: registry claim `decode-iff` (role `decidability`), pointer `Effect4.Schema.decode_iff`;
  consumer: the `nat` arm of `decodeRaw_normJ`, which `encode_of_decode` and `decode_iff` read.
- Reach: every JSON value, with no hypothesis; the normaliser is `normJ` (row 128); the bound is
  `safeBound` (the owner's ruling R7).
- Does not establish: anything about encoding, the TypeScript face or the host boundary.
- Unlocks: R3 (data); `decode_iff` stays proved over the bounded nat wire.

`natVal?_exact`: a datum that the bounded natural reader reads is the natural's image.

- Concept: `exact-codecs` (concept 5); property: exactness modulo key sorting (`decode-iff`).
- Question: registry claim `decode-iff` (role `decidability`), pointer `Effect4.Schema.decode_iff`;
  consumer: the `nat` arm of `decodeRaw_exact`, which `encode_of_decode` and `decode_iff` read.
- Reach: the hypothesis that `natVal?` reads the datum; the image is equal, with no normaliser at
  the leaf.
- Does not establish: that every natural inside the bound reads back. No lemma states that step,
  `nat? (Arch.Json.ofNat n) = some n` below 2^53, for `nat?` (open obligation 1).
- Unlocks: R3 (data); `decode_encode`, `encode_of_hasTy` and `encode_injective` keep their
  statements and their proofs over the bounded wire.

## Open obligations

1. P1's nat half has no registry claim yet. The proposed text is in the last section. Its proof
   needs one step: `nat? (Arch.Json.ofNat n) = some n` below 2^53.
   `natOfBinary64_binary64OfNat` (`src/Effect4/Laws/Store/ShapeRead.lean`) states that step for
   the store's reader `natOfBinary64`, not for `nat?`. A search finds no lemma that states it for
   `nat?`.
2. The defect, error and interruptor images still read numbers through `nat?`, with no bound.
   They are `Defect.user n`, `Err.tag n` inside a promoted defect, and an interruptor's fiber id.
   Move G re-encodes the defects, and the owner's decision D-J1 below names the choice.
3. Three texts still say "a natural above 2^53". They are the title of the claim `modeled-codec`
   (`tools/ProofGraph/Registry.lean`), its paragraph in `docs/core/semantics.md`, and the header
   of `src/Effect4/Laws/Schema/Modeled.lean`. Each stays true after this landing, and
   `safeBound` would make each exact. This landing edits none of them, since the brief does not
   name them.
4. The note's §8 table and its finding 8.7 describe the nat wire before this landing. The brief
   keeps the note as it is, so this receipt's comparator line carries the classes after it.
5. `probe/out/lean-full.txt` is untracked, and it still holds the old `exactBound` line. This
   landing leaves it as it was.
6. For the coordinator: `harness/truth/schema-codec/check.ts` reads no argument. It imports
   `./.work/values.ts` beside itself, so the brief's third lane command reads the lane's work file
   of 2026-10-18. This landing ran the lane from a byte-identical copy under the scratch folder.
   A later brief can write the emitter's output to `harness/truth/schema-codec/.work/values.ts`,
   as the retired recipe did (`git:d956fa2ce~1:Makefile`, `_run-schema-codec`).

## Decisions for the owner

**D-J1, the defect numbers.** R7 rules one bound "on both wires and at the observation". The
observation's cause also holds the numbers of item 2 above, and this move does not bound them.

- (a) Move G writes a user defect's number, and an error tag inside a defect, under `safeBound`.
  Then every number of a terminal observation lies inside one bound.
- (b) Those numbers stay binary64-exact, since rc.112's `Schema.Defect()` takes any JSON value
  (the note's finding 8.1).

Recommended: (a) for `Defect.user` and `Err.tag`, since R7 names the observation. An
interruptor's fiber id stays as it is: it is the run's own numbering, and the comparison renames
it. Nothing in this landing depends on the choice.

## Proposed decisions rows (proposals only)

None. Part (3) of the note's proposed row 421 (§11.3) covers this landing.

## Proposed semantics registry text: the nat half of P1 (proposal only)

Semantics generation is paused, so `generated/semantics.md` is not regenerated. The proposal has
three parts: a semantics registry claim, its planned goal and its required property.

```lean
-- tools/ProofGraph/Registry.lean, under `-- 5. exact-codecs`
{ id := "nat-codec-admission", concept := "exact-codecs", role := .decidability
  title := "Codec admission of a natural at nat is the profile's bound: Ty.isCodecValue .nat (.nat n) holds exactly when n ≤ safeBound, rc.112's isInt (Number.isSafeInteger, 2^53 - 1); every natural is a member of nat (Val.hasTy), so a natural past the bound is a member and no codec value; the nat half of P1 (docs/research/2026-10-19-schema-as-the-carrier.md §5); nothing of the machine's arithmetic past the bound (M2), of the defect, error and interruptor images, or of the TypeScript face beyond the codec lane's finite check (the owner's ruling R7, move J)"
  pointer := .witness `Effect4.Schema.isCodecValue_nat_iff },
```

```lean
-- src/Effect4/Laws/Schema/Codec.lean, namespace Effect4.Schema (decisions rows 203 and 207)
@[semantics "exact-codecs" (requirement := R3)]
proof_goal isCodecValue_nat_iff (n : Nat) :
    Ty.isCodecValue .nat (.nat n) = true ↔ n ≤ Codec.safeBound
```

The required property, for concept 5 of `docs/core/semantics.md`:

- **Codec admission of a natural (`nat-codec-admission`)**: at `nat`, a natural is a codec value
  exactly when it is at most `safeBound`, 2^53 - 1 (`isCodecValue_nat_iff`,
  `src/Effect4/Laws/Schema/Codec.lean`). Membership holds for every natural, so membership does
  not give codec admission. It establishes nothing of the machine's arithmetic past the bound
  (M2), of the defect images, or of the TypeScript face.
