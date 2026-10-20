# Brief G: the canonical defect alphabet, encoded as Effect writes a defect

Status: brief, 2026-10-19, from the coordinator to one Opus seat. The ruling is the owner's, R5
in `docs/research/2026-10-19-schema-as-the-carrier.md` §10. Its words: "the canonical defect
alphabet with an injective encoding, raw for user defects and name-and-message for machine
defects, with missingService's key stored". The move is §9 row G and §11.2 of that note. Read `AGENTS.md` in
full before anything else. Then read §5, §8.1, §8.9, §11.2 and §12 of the note, and
`docs/research/2026-10-19-schema-as-the-carrier/receipt-J.md`, the move that landed before you.

## 1. Where you work

- The checkout `/Users/pooks/Dev/lean4-effect4`, branch `refactor/phase1-phase3`, base
  fc9eb07c8 (move J's head). No worktree: you edit and commit here. Nobody else runs Lean or
  dune in this checkout while you work.
- Your scratch folder is
  `/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/2cfa2789-af6f-4183-90be-cdd7f2934e64/scratchpad/G`.
  Every temporary file goes there, never under the checkout and never under `/tmp` directly.
- Every Lean command runs through the runner, one at a time, and never with a thread count:
  `python3 /private/tmp/seams-lean-one.py lake build <Module>`,
  `python3 /private/tmp/seams-lean-one.py lake env lean <file>`, and
  `python3 /private/tmp/seams-lean-one.py lake exe lcnfgen …`. A long build runs in the
  background with its output in a log under your scratch folder, and you wait for it.
- OCaml runs only as `opam exec --switch=effect4 -- dune …` from `ocaml/`. Never install into
  or pin the `effect4` switch.
- Never run: a bare `lake build`, `lake build Test`, `make build`, `make check-full`,
  `make gen-semantics`, `tsc`, `git add -A`, `git push`. Never write `2>/dev/null` on a Lean
  command: a hook refuses it. TypeScript is checked by tsgo 7 only.
- Never edit: `docs/core/*`, `AGENTS.md`, `lakefile.toml`, the note itself, a generated file by
  hand (regenerate it; `docs/GENERATED.md` names each group's producer).

## 2. The domain and the encoding

Concept 5, exact codecs: the defect's codec is injective on the canonical defects and writes
rc.112's raw form. It serves R3 and §9.1 item 5.

- **Canonical.** A defect is canonical when it is `Defect.ofError`'s normal form
  (`src/Effect4/Machine/Alphabets.lean`): `user n`, `error e` with `e` neither `tag _` nor
  `boom`, or a machine defect. `tag n` is `user n` and `boom` is `badName`, as `ofError` says.
  Codec admission requires the canonical form: the encoder refuses `error (tag _)` and
  `error boom`.
- **The representation.** `Defect.missingService` gains its key: `missingService (key :
  ServiceKey)`. `serviceLookupK` (`src/Effect4/Program/Compile.lean`) stores the key it looked
  up. Every match on `Defect` follows the new-field checklist below.
- **The encoding**, rc.112's `Schema.Defect()` (`vendor/effect-4.0.0-rc.112/src/Schema.ts`,
  `Defect`; `src/SchemaTransformation.ts`, `makeEncodeDefect`, `encodeJsonError`,
  `decodeDefect`, `isJsonError`): an `Error` becomes `{name, message}`, and any other value
  is its own JSON.
  - `user n` is the number `n`, when `n ≤ safeBound`; past the bound the encoder refuses, and
    the decoder reads a number only under the bound. This settles D-J1 of `receipt-J.md`
    under R7: the one bound holds at the observation, and a user defect crosses as a raw JSON
    number. A red control reads the refusal at `user (2 ^ 53)`. Fiber ids stay as they are.
  - `error (text s)` is the string `s`.
  - `error (tagged t m)` is the array `[t, m]`.
  - `error (payload p)` is `{"payload": hex}` (`payloadHex`, as `encodeErr` writes it).
  - A machine defect is the object `{"message": M, "name": N}`, its two entries in `normJ`'s
    order, so the normaliser is the identity on it.
    - `asyncFiber`: name `AsyncFiberError`, message
      `An asynchronous Effect was executed with Effect.runSync`
      (`vendor/effect-4.0.0-rc.112/src/internal/effect.ts`, `class AsyncFiberError`, its
      constructor; name the lines in the docstring).
    - `missingService key`: name `Error`, message `Service not found: ` followed by the key's
      spelling (`vendor/effect-4.0.0-rc.112/src/Context.ts`, the `Service not found` throw;
      `internal/effect.ts`, `Context.getUnsafe`). The spelling is `keySpelling names key`
      (`src/Effect4/Codegen/Types.lean`), the one spelling the printer gives a key, and
      `effect/Scope` for the scope key (`Effect4.Machine.scopeKey`; rc.112's `scopeTag`,
      `internal/effect.ts`, `Context.Service("effect/Scope")`).
    - `notImplemented` and `badName` are Lean's own: name `Effect4`, message `notImplemented`
      and `badName`.
- **The decoder** reads each form back by its JSON kind: a number, a string, a two-string
  array, a one-entry `payload` object, or a `message`-and-`name` object. The object's name and
  message must match one machine defect. `Service not found: X` reads back by `keyOfSpelling names X`
  (`keyOfSpelling_keySpelling`, `src/Effect4/Laws/Codegen/ReadLeaf.lean`, is its retraction).
  Everything else is refused. A declared name equal to `effect/Scope` would collide with the
  scope's spelling: refuse it at decode and record it in the receipt.
- **The key names are data.** `encodeDefect` and `decodeDefect` take `names : KeyNames` as a
  parameter. So does everything above them in the codec. That is `encodeReason`,
  `encodeCause`, the `ty_exitOf` and `ty_causeOf` arms of `wireAlgebra`, `prepare`,
  `Prepared`, `encode`, `decode`, `isValue` and the `Ty.encode`/`Ty.decode` exports. Pass the
  table as a parameter; never bind it
  with `let` before a closure a definition returns (`#closure_audit` refuses that shape). A
  caller takes its names from its signature: `(nativeSignature table).keyNames`
  (`src/Effect4/Program/Native.lean`), as `src/Effect4/Codegen/Admit.lean` does. Enumerate
  every caller first:
  `grep -rn 'Ty.encode\|Ty.decode\|Schema.encode\|Schema.decode\|Codec.prepare\|isCodecValue\|Codec.isValue\|encodeCause\|encodeReason\|encodeDefect\|decodeDefect' src Test tools harness docs/research/2026-10-19-schema-as-the-carrier/probe`.
- **The laws.** `src/Effect4/Laws/Schema/Codec.lean` generalizes over `names`: `decode_iff`,
  `decode_encode`, `encode_of_hasTy` and `encode_injective` keep their statements, with `names`
  as one more argument. `decodeDefect_exact`, `decodeDefect_normJ` and their consumers are
  repaired. A finite control reads injectivity on a list of canonical defects, one of each
  form. The table has two named keys and the scope key. It reads distinct encodings for
  distinct defects, and each decodes back. A red control reads that `error (tag 7)` is refused and that
  `user 7` is not.
- The exit codec's defect column is rc.112's `Schema.Defect()` already
  (`src/Effect4/Codegen/SchemaCode.lean`); it does not change.
- The codec lane (`harness/truth/schema-codec/`) is retired from the gates and run by hand.
  Every document, encoding or refusal of `Emit.lean` that carries a defect takes the new
  forms, and `check.ts` reads them against rc.112. Add one case per defect form, the scope's missing
  service among them. `check.ts` takes no argument and imports `./.work/values.ts`, which is
  ignored by Git. So run the lane as:

      python3 /private/tmp/seams-lean-one.py lake env lean -M4096 --run harness/truth/schema-codec/Emit.lean harness/truth/schema-codec/.work/values.ts
      harness/truth/node_modules/.bin/tsgo --noEmit -p harness/truth/schema-codec/tsconfig.json
      bun harness/truth/schema-codec/check.ts

  Keep a red control: one altered value fails it.

## 3. The new-field checklist for `missingService (key)`

Read the memory's checklist first: every place that must follow a new field, in order. The
sites in this tree:

1. Lean, the library: `Defect.ofError`, `ofDefect` and `Defect.image` (the key as
   `ServiceKey`'s image inside `ctor 3`). Then `reservedDefect` in
   `src/Effect4/Program/Typed.lean`, `missingScope` in `src/Effect4/Machine/Stores.lean`,
   `serviceLookupK` and the `missingScope` field in `src/Effect4/Program/Compile.lean`, and
   `src/Effect4/Schema/Codec.lean`.
   `src/Effect4/Api/RunnerDerived.lean` is generated: `python3 scripts/generate.py --only
   derived` after the Lean edit (read `docs/GENERATED.md`'s table for each group's command and
   its checks).
2. Lean, the law graph: `Laws/Machine/ContextValue.lean`, `Laws/Machine/Witnesses.lean`,
   `Laws/Program/DenoteR.lean`, `InterpR.lean`, `BlockMeaning.lean`, `Agreement.lean`,
   `Agreement/Blocks.lean`, `Typed/Commands/Clauses/Spawn.lean`, `Typed/Commands/Evaluate.lean`,
   `Laws/Schema/Codec.lean`. Grep `missingService` under `src/` and `tools/` for the complete
   list before you start; the list above was read at the base commit.
3. Batteries and tools that name it: `Test/Program/SchedContract.lean`, `H2PartOne.lean`,
   `PoolOps.lean`, `AuthoringModule.lean`, `tools/Effect4Gen/guards/runner.lean`,
   `tools/ProofGraph/Registry.lean`. `make batteries-touched BASE=fc9eb07c8` builds the ones
   the change reaches.
4. The truth harness. In `harness/truth/Truth.lean`, `defectJson` becomes
   `Schema.Codec.encodeDefect names`, with the harness's own table. In
   `harness/truth/run-truth.ts`, `defectWire` goes with its two controls. Its `Die` case
   writes the defect as rc.112 itself encodes it:
   `Schema.encodeUnknownSync(Schema.toCodecJson(Schema.Defect()))(defect)`. Rewrite the
   controls near `defectWire`'s callers in `run-truth.ts` against the new encoder, and keep a
   red control. The lane is retired from the gates. So check that `Truth.lean` compiles with
   `lake env lean` through the runner, with the `-M4096` and native flags of the Makefile's
   `gen-truth` recipe. Then run the lane's own bun tests (`TRUTH_HOST_TESTS` in the Makefile).
5. OCaml. The lcnf group generates the program types into `ocaml/eff/eff_types.ml`, and the
   eff group generates the goldens. Run `make gen-lcnf`, then `make gen-eff`. Then run the
   wire, cas and fixtures groups if `docs/GENERATED.md` says a `Defect` value reaches them.
   The hand sites are the two matches on `Defect.MissingService` in
   `ocaml/engine/e4_engine.ml`. One lists the payload-free constructors, and one prints
   `missingService`. Print the key's two numbers there, since the engine has no key names. `src/OCaml5/Eff/Goldens.lean` carries the hand golden tree: add
   the key where a `missingService` golden exists, or add one golden that uses it. Then
   `opam exec --switch=effect4 -- dune build` and `dune test` as the `_run-ocaml` recipe runs
   them.
6. The faces probe (`docs/research/2026-10-19-schema-as-the-carrier/probe/`): `Faces.lean`'s
   `typedJson` passes the built program's key names. Rerun the three commands of the note's §8
   (the Lean one through the runner). `dieNat`, `dieString`, `forkDieJoin` and `asyncSleep`
   move from `differ` to `equal` in `expected.tsv`; `compare.ts` exits 0. Commit the
   regenerated `out/` files that changed.

## 4. The landing

In this order, each result into your receipt with its command:

1. `lake build Effect4.Machine.Alphabets`, `Effect4.Program.Compile`, `Effect4.Schema.Codec`,
   through the runner, repairing as you go.
2. `python3 scripts/generate.py --only derived`; then `lake build Effect4 Effect4.Laws` in the
   background (the core edit's dependents; note the wall time).
3. `make batteries-touched BASE=fc9eb07c8`.
4. The axiom gate's walk. Write a scratch file with `import ProofGraph.AxiomAudit`, the
   imports of the touched modules, and `#axiom_audit` over every touched module. Run it with
   `lake env lean` through the runner (read `tools/ProofGraph/AxiomAudit.lean`'s header first). Paste the
   output into the receipt.
5. The regenerations of §3 item 5, then `make check-ocaml`, once.
6. The codec lane of §2, the truth harness checks of §3 item 4, and the faces probe of §3
   item 6.
7. `make check-ts`, once, at the end. Do not rerun a gate that passed on the same tree.

## 5. The commit and the receipt

- Commit by explicit paths only, on this branch, when every step above passes. Generated files
  are committed with the change that regenerates them. Research files need `git add -f`. The
  message's first line: `Codec: the canonical defect alphabet, encoded as Effect writes it (move G)`.
  The body names the ruling, the representation change and the controls. The last line:
  `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`.
- The receipt is `docs/research/2026-10-19-schema-as-the-carrier/receipt-G.md`. It follows
  `docs/core/controlled-english.md`: one idea per sentence, at most 25 words. Check it with
  `python3 -I scripts/check-language.py --show <file>` and repair every finding. It records,
  first, the one thing the coordinator must know before merging. Then it records the base and
  head commits and the changed files. Then the exact commands and their results, and the axiom
  output. Then the open obligations, and whether any evidence is bounded or host-only. Then how
  you settled the open point of §11.2 (the key stored, the spelling from the table) and any
  case you refused. Last, the proposed registry text for the defect codec's injectivity, since
  semantics generation is paused (`generated/semantics.md` is not regenerated).
- Report a compiling finite probe as a finite probe. Use the evidence words exactly.
- When a decision belongs to the owner, stop at that boundary. Write the options and your
  recommendation in the receipt, and continue with what does not depend on it.

## 6. What this move does not do

It does not add a payload defect carrying arbitrary rc.112 JSON (the owner deferred it). It
does not change the machine's own markers or when a defect arises. It does not touch the
session protocol's `fail/payload` fixtures (move B) or the kit's run replies (move A).
