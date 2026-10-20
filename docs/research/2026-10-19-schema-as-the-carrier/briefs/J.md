# Brief J: one numeric bound on the nat wire

Status: brief, 2026-10-19, from the coordinator to one Opus seat. The ruling is the owner's, R7
in `docs/research/2026-10-19-schema-as-the-carrier.md` §10: "one numeric bound, safeBound, on
both wires and at the observation, under M2". The move is §9 row J and §11.1 of that note. Read
`AGENTS.md` in full before anything else. Then read §5, §8.7, §11.1 and §12 of the note.

## 1. Where you work

- The checkout `/Users/pooks/Dev/lean4-effect4`, branch `refactor/phase1-phase3`, base
  `ccba8e92d`. No worktree: you edit and commit here. Nobody else runs Lean in this checkout
  while you work.
- Your scratch folder is
  `/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/2cfa2789-af6f-4183-90be-cdd7f2934e64/scratchpad/J`.
  Every temporary file goes there, never under the checkout and never under `/tmp` directly.
- Every Lean command runs through the runner, one at a time, and never with a thread count:
  `python3 /private/tmp/seams-lean-one.py lake build <Module>` and
  `python3 /private/tmp/seams-lean-one.py lake env lean <file>`. A long build runs in the
  background with its output in a log under your scratch folder, and you wait for it.
- Never run: a bare `lake build`, `lake build Test`, `make build`, `make check-full`,
  `make gen-semantics`, `tsc`, `git add -A`, `git push`. Never write `2>/dev/null` on a Lean
  command: a hook refuses it. TypeScript is checked by tsgo 7 only (the binary under
  `harness/truth/node_modules/.bin/`).
- Never edit: `docs/core/*`, `AGENTS.md`, `lakefile.toml`, `generated/*`, `ocaml/*`, the note
  itself, `Val.hasTy`, `natLiteralsInProfile` (`src/Effect4/Codegen/Checked.lean`).

## 2. The change

Concept 5, exact codecs. Codec admission of a natural is the profile's bound, `safeBound`, on
the nat wire as on the int wire. `Val.hasTy` does not change: a natural past the bound stays a
member and stops being a codec value. That is P1 of the note's §5.

1. `src/Effect4/Schema/Codec.lean`. `wireAlgebra.ty_nat` encodes `.nat n` only when
   `n ≤ safeBound`, and its decode keeps `nat?` under the same bound, in the form `intJson` and
   `int?` have. Write the pair as named definitions beside `intJson` and `int?`. Give them
   docstrings of the same shape, and let `ty_nat` use them. Repair the docstring of
   `safeBound`: it bounds a natural's image as well as an integer's.
2. `src/Effect4/Laws/Schema/Codec.lean`. Every lemma with a nat arm is repaired under the new
   guard. `decode_iff`, `decode_encode`, `encode_of_hasTy` and `encode_injective` keep their
   statements. Search the whole tree for other readers of the nat wire before you build:
   `grep -rn 'ty_nat\|decodeRaw .nat\|decodeRaw Ty.nat\|encodeRaw .nat\|wire .nat' src Test tools harness`.
   A new helper lemma is a step of the claim it serves: its docstring names that claim and the
   consumer that uses it. No `simp_all`, no `first |`, no `try`; a `simp` is `simp only [...]`.
   Every warning is an error.
3. Controls, `Test/Codegen/DataCodec.lean`, as finite evaluations (decisions row 301):
   `Ty.isCodecValue .nat (.nat (2 ^ 53 - 1)) = true` and `= false` at `2 ^ 53`;
   `Schema.encode .nat (.nat (2 ^ 53)) = none`;
   `Schema.decode .nat (Arch.Json.ofNat (2 ^ 53)) = none`;
   `Schema.decode .nat (Arch.Json.ofNat (2 ^ 53 - 1)) = some (.nat (2 ^ 53 - 1))`;
   and the membership control that `Val.hasTy (.nat (2 ^ 53)) .nat` stays `true`.
4. The codec lane, retired from the gates but kept in the tree
   (`harness/truth/schema-codec/`). `Emit.lean` gains `("natAboveBound", .nat, .nat (2 ^ 53))`
   under `encodingRefusals`, and the decoding side gains the same datum where the lane lists
   decoding refusals. `check.ts` reads both against rc.112's generated natural Schema, so both
   faces refuse `2 ** 53` together, and both accept `2 ** 53 - 1`. Run the lane by hand:

       python3 /private/tmp/seams-lean-one.py lake env lean -M4096 --run harness/truth/schema-codec/Emit.lean <scratch>/values.ts
       <tsgo> --noEmit -p harness/truth/schema-codec/tsconfig.json
       bun harness/truth/schema-codec/check.ts <scratch>/values.ts

   If the tsconfig names files that no longer exist, repair the tsconfig, not the check.
5. The faces probe (`docs/research/2026-10-19-schema-as-the-carrier/probe/`). Rerun the three
   commands of the note's §8 (the `lake env lean --run … Faces.lean` line through the runner,
   then `bun … run.ts`, then `bun … compare.ts`). The Lean face now refuses `exactBound`, so
   `expected.tsv` moves `exactBound` from `refusedEffect` to `refusedBoth`, and `compare.ts`
   exits 0. Commit the regenerated `out/` files that changed.

## 3. The landing

In this order, each result into your receipt with its command:

1. `lake build Effect4.Schema.Codec`, then `lake build Effect4.Laws.Schema.Codec`, through the
   runner.
2. `lake build Effect4 Effect4.Laws` through the runner, in the background: the core edit's
   dependents. Note the wall time.
3. `lake env lean Test/Codegen/DataCodec.lean` through the runner.
4. `make batteries-touched BASE=ccba8e92d` (it exports its own thread bound; run nothing else
   with lake beside it).
5. The axiom gate's walk: a scratch file with `import ProofGraph.AxiomAudit`, the imports of the two
   touched modules, and `#axiom_audit Effect4.Schema.Codec Effect4.Laws.Schema.Codec`, run with
   `lake env lean` through the runner. Read `tools/ProofGraph/AxiomAudit.lean`'s header first.
   Paste the output into the receipt.
6. The codec lane by hand (§2 item 4) and the faces probe (§2 item 5).
7. `make check-ts`, once, at the end. Do not rerun a gate that passed on the same tree.

## 4. The commit and the receipt

- Commit by explicit paths only, on this branch, when every step above passes. Research files
  need `git add -f`. The message's first line: `Codec: one numeric bound on the nat wire (move J)`.
  The body names the ruling and the controls. The last line:
  `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`.
- The receipt is `docs/research/2026-10-19-schema-as-the-carrier/receipt-J.md`. It follows
  `docs/core/controlled-english.md`: one idea per sentence, at most 25 words. Check it with
  `python3 -I scripts/check-language.py --show <file>` and repair every finding. It records,
  first, the one thing the coordinator must know before merging. Then it records the base and
  head commits and the changed files. Then the exact commands and their results, and the axiom
  output. Then the open obligations, and whether any evidence is bounded or host-only. Last,
  the proposed registry text for the nat half of P1, since semantics generation is paused
  (`generated/semantics.md` is not regenerated).
- Report a compiling finite probe as a finite probe. Use the evidence words exactly.
- When a decision belongs to the owner, stop at that boundary. Write the options and your
  recommendation in the receipt, and continue with what does not depend on it.

## 5. What this move does not do

It does not make the Lean machine's `add` refuse past the bound; the prelude does, and that is
M2's decision. It does not touch OCaml: the codec is not in the lowered closure
(`ocaml/gen/api_gen.mli` names no `schema_codec` root). It does not change the public shape of
`Ty.encode` or `Ty.decode`.
