# Seat B receipt: spec v3 and the Gemini implementation brief (2026-10-01)

## 1. The one thing to know first

The slice cannot land green until the coordinator adds a register row: the refuted item's witness,
`Test.Program.TypedProgBindRed.typedProg_not_bind_closed` (`Test/Program/TypedProgBindRed.lean:32`),
has no row in `Test/Counterexamples/REGISTER.md`, and the next free TYPED id is **030**, not 023
(023 is earmarked by decisions row 176, `docs/core/decisions.md:269`: "`E4-TYPED-CE-023` if it
holds"). The proposed row is §5. Second, the slice's wanted goal `denoteR_typed` is the attacked
statement of three SEEDED register rows (`E4-TYPED-CE-020`, `-021`, `-022`,
`REGISTER.md:249-251`); spec v3 shows them beside its `wanted` status (`contestedBy`), so the report
does not present a contested goal as merely open.

## 2. Base, head, files

- Base and head: `198dd533` on `refactor/phase1-phase3` (the brief's; no git command run, no commit
  made). The main checkout's working copy holds uncommitted edits to
  `src/Effect4/Laws/Program/Typed/Commands/Bookkeeping.lean` and
  `Test/Program/LayerSharingContract.lean` (the session's git status snapshot, not a command I ran);
  I touched neither. `Bookkeeping.lean` imports `Seq.lean`, which C3 edits; the brief keeps Gemini
  out of the main checkout.
- Written, all under `docs/research/2026-10-01-semantics/seat-B/`:
  - `spec-v3.md` (656 lines): the implementation spec.
  - `brief-gemini-implementation.md` (111 lines): the dispatch brief.
  - `receipt.md` (this file).
  - `probe/semantics.mts` (158 lines, the proposed schema), `probe/decode.mts` (38 lines, the decode
    controls), `probe/slice.json` (125 lines, the slice instance), `probe/commands.json` (the two
    runs), `probe/typecheck.log` (empty), `probe/decode.log` (117 lines, the controls' output).
- Edited after the runs: `probe/semantics.mts` line 3, a comment only (the cited line of
  `ts/eff/eff.gen.ts` corrected from 62 to 42); no code changed after the typecheck and the bun run.

## 3. What I read, in the brief's order

1. `AGENTS.md` (in context). 2. `review-gemini-v2.md` (all). 3. Codex:
`/private/tmp/codex-second-eyes-2026-10-01/domain-spec-review/review.md` (all; §8 at lines
102-111) and `/private/tmp/codex-second-eyes-2026-10-01/domain-spec-ledger-review.md` (all four
sections); Codex's `commands.json`, `run.py`, `api-corrected.mts`, `runtime.mts`,
`runtime-results.json`, `provenance.json`, `compiler-version.log`. 4. Gemini's
`gemini/domain-model-spec.md` v2 (all) and `gemini/note.md` §§3-5 (lines 74-256). 5. The owner's
plan, `docs/research/2026-10-01-landing/status-2026-10-01-evening.md` §§7, 7b, 7c (lines 133-248).
6. The mechanisms: `src/Effect4/Laws/Auto/Obligations.lean` (all), `tools/ProofGraph/Ledger.lean`
(all), `tools/ProofGraph/Proof.lean` (all), `src/Effect4/Laws/Auto/Census.lean` (all),
`src/Effect4/Laws/Auto/RuleSets.lean` (all), `tools/Tools/Architecture.lean` (1-200, 727-781),
`tools/Tools/ArchitectureRoles.lean` (1-62, 95-130, 160-243), `Test/Audit/AxiomGate.lean` (all 544
lines), `Makefile` (1-75, 150-500), `docs/GENERATED.md` (1-100), `ts/eff/README.md`,
`ts/eff/check.ts`, `ts/eff/package.json`, `ts/eff/tsconfig.json`, `ts/eff/eff.gen.ts` (head and the
union/filter lines), `Test/Counterexamples/REGISTER.md` (header 1-40, the TYPED rows).
Also read because the spec depends on them: `tools/Tools/GeneratedStamp.lean`,
`tools/Tools/HostProtocol.lean`, `scripts/check-host-protocol.py`,
`tools/Drivers/ProgramStructureCheck.lean`, `tools/Effect4Gen/Check.lean:240-264`,
`generated/AGENTS.md`, `lakefile.toml`, `Test/Audit/Obligations.lean:1-40`,
`src/Effect4/Laws/Program/Typed/Seq.lean:1-70`, `Assembly.lean:1625-1645,1830-1872`,
`Test/Program/TypedProgBindRed.lean` (all), `docs/core/decisions.md` rows 117, 128, 138, 148,
163, 170, 175, 176 and the header, `docs/core/language-cut.md` headings, seat A's
`citations-audit.md` head; in the Lean 4.33.1 toolchain source (`~/.elan/toolchains/leanprover--lean4---v4.33.1/src/lean`):
`Lean/Attributes.lean:140,180-224,255-315`, `Lean/Environment.lean:1925-2005,2307-2470,2515-2535`,
`Lean/DeclarationRange.lean:20-41`, `Lean/Parser/Attr.lean:1-60`, `Lean/Data/Json/Basic.lean:186,225-226`,
`Init/Notation.lean:627,644`; in the pinned `effect` install, `dist/Schema.d.ts` and
`dist/SchemaAST.d.ts` at the lines the spec cites.

## 4. What I ran

No `git`, no `lake`, no `make`. Read-only shell (`cat`, `sed`, `awk`, `grep`, `ls`, `wc`,
`shasum`, `date`) and `python3` for JSON parsing and for running the two probe commands the way
Codex's `run.py` does (subprocess, captured output, a 45-second timeout).

| Command | Exit | Output |
| --- | --- | --- |
| `ts/eff/node_modules/.bin/tsgo --version` (a version query, not a check) | 0 | `Version 7.0.0-dev.20260629.1` |
| `shasum -a 256 ts/eff/node_modules/effect/dist/Schema.js` | 0 | `5ff75f82…ed4c2177b4deec9dfaf0b1f7c68a92156804e7129aed`, the hash in Codex's `provenance.json` |
| **the one typecheck**, cwd `seat-B/probe`, env `GOMAXPROCS=1 GOMEMLIMIT=512MiB`: `/Users/pooks/Dev/lean4-effect4/ts/eff/node_modules/.bin/tsgo --noEmit --skipLibCheck --strict --target es2022 --module esnext --moduleResolution bundler --resolveJsonModule --allowImportingTsExtensions --exactOptionalPropertyTypes --noUncheckedIndexedAccess --verbatimModuleSyntax semantics.mts decode.mts` | 0 | none (0.3 s); `probe/typecheck.log` empty |
| `bun --version` (same binary as below; a version query) | 0 | `1.4.2` |
| **the one bun run**, cwd `seat-B/probe`: `/Users/pooks/.local/share/mise/installs/bun/1.3.14/bin/bun decode.mts` (the binary at that path reports 1.4.2) | 0 | `allAgree: true`; 16 of 16 controls agree (0.1 s); `probe/decode.log` |

The flags add ts/eff's own strictness (`ts/eff/tsconfig.json`: `exactOptionalPropertyTypes`,
`noUncheckedIndexedAccess`, `verbatimModuleSyntax`, bundler resolution) to Codex's `--strict`.
Not run: a red control for the typecheck itself (the budget was one typecheck), so its exit 0 is
evidence that these two files type-check, not that the compiler would catch a planted error here.

The 16 controls (`probe/decode.log`): accepted, the slice instance; refused with a path and a
reason, 14 mutations (a wall-clock `timestamp` key, a dangling concept, a duplicate claim id, a
proved status without a witness, a malformed nested name, an unknown status tag, a malformed
register id, a status word outside the register's six, concept counts that disagree with the
claims, a negative count, one goal counted by two claims, a placement outside `tagged`/`inherited`,
a blank absent reason, a malformed nested counterexample witness); accepted by the default decoder,
the wall-clock key (the control that shows `onExcessProperty: "error"` is load-bearing: the default
strips unknown keys, `effect/dist/SchemaAST.d.ts:365`).

Axiom output: none; no Lean was run.

## 5. The proposed register row (the coordinator's to add; the slice refuses until it exists)

```
| `E4-TYPED-CE-030` | SEEDED 2026-10-01 | `TypedProg` is closed under bind: a program typed at `mid` and a continuation typed at `ty` at every later world on every exit `ExitOk` admits at `mid` make a sequence typed at `ty` | `Test/Program/TypedProgBindRed.lean`: `typedProg_not_bind_closed` (a closing marker's exit must fit the current type), `bind_not_typed` and `guard_bind_not_closed` (a first program whose only closing marker sits inside a guard body does not bind either); green control `seq_sample` | no bind rule: M5 sequences per construct (`seq_typed` with `close_typed`, `src/Effect4/Laws/Program/Typed/Seq.lean:40,59`, merged `a561d604` per decisions row 148); the `onFailure`, `all` and `onExit` shapes owed beside it (decisions row 148) |
```

Reason: the witness is retained in the green battery (`Test/All.lean:41`) and is cited by decisions
row 148 (`decisions.md:241`) and by `docs/DESIGN-BASIS.md:1662`, but no register row carries it
(grep: 0 hits), so a report that cites a refutation by register id has nothing to cite. Status
SEEDED rather than REPAIRED because the forced repair (per-construct lemmas) has landed for one
shape of four.

## 6. The rulings (spec v3 §12 has the reasons)

- **R1 confirmed:** the registry is a Lean module, first-order, names checked at run time; it
  authors no fact another file owns.
- **R2 confirmed, refined:** wanted validated by `ProofGraph.check`, not existence; a RETIRED row
  cannot refute; `contestedBy` added.
- **R3 confirmed, one part refuted:** no git commit in the committed bytes (a file cannot name the
  commit that holds it; generated files lost embedded revisions on 2026-09-13); `inputs`,
  `command`, toolchain, roots, policy instead, the commit in the run's receipt. Schema
  `ts/eff/semantics.ts`, checker `ts/eff/check-semantics.ts`, check in `check-full`.
- **R4 confirmed, refined:** non-reserved `&"semantics"`, one string, one concept, current module
  only; `#semantics_census` prints the environment half only (claims are tool-side); the extension
  read after `importModules` and the gate entry are assumed until C2 and the sweep.
- **R5 refuted in two details:** the next free TYPED id is 030 (023 is earmarked by row 176); the absent
  item is the `onFailure` compatibility lemma (row 148), not the bind closure, which is the refuted
  item's own statement.
- **R6 confirmed, refined:** `who` read from the decisions register; cut rows 163, 128, 138, 117.

Other findings the spec records (reading): `Schema.NonNegativeInt`, used by v2 §5, does not exist
in the pinned rc.112 `dist/Schema.d.ts`; the producer must be a library plus a separate `main`,
because `Tools.Architecture` has a top-level `main` and cannot be imported, and the controls driver
needs the library; DI-18's text ("no `import Lean` in the audited closure",
`docs/DESIGN-ISSUES.md:91`) disagrees with four Laws instrument modules at HEAD, and its
enforcement script `scripts/check-library-roots.sh` is gone; `make check-semantics` and
`make gen-semantics` order-only depend on `build` (the whole tree, the `gen-architecture`
precedent), so Gemini runs `scripts/check-semantics.py` directly and the make targets belong to
the owner's sweep.

## 7. Open questions for the coordinator (five)

1. Row `E4-TYPED-CE-030` (§5): add it, and with status SEEDED (recommended) or REPAIRED for the
   `onSuccess` shape? C4 waits on it.
2. The absent item: the `onFailure`-shape lemma (recommended: a claim with no witness, no goal and
   no refutation) or R5 as written, with the bind closure both absent and refuted?
3. Which file names the link from a register row to the claim it attacks: the registry's
   `contestedBy` and `refutedBy` (spec v3, recommended for now), or a new register column (one
   owner of the link, but an edit to the register's format)?
4. `generated/semantics.json` carries the whole-Laws unplaced count, so it moves with almost every
   landing that adds a theorem (re-cut by its marker on the Laws trace; drift for `check-gen-full`
   until regenerated). Keep the count in the committed bytes (recommended: it is §7b's coverage
   number), or keep only the registry's concepts' modules and leave the whole-graph number to
   `#semantics_census` and the map?
5. The attribute's storage: a parametric attribute (an `initialize`, one new
   `auditImplementationModules` entry like `RuleSets`; recommended) or a declaration-backed marker
   `<decl>._semantics` in the ledger's style (no `initialize`, no admission, one extra constant per
   tag, visible to any `importModules`)?

## 8. Evidence class by section of `spec-v3.md`

| Section | Class |
| --- | --- |
| §0, §1 | reading |
| §2 model | reading for every cited mechanism; the types are a proposal (not compiled) |
| §3 derivation | reading of the ledger, proof and gate sources; the printer's determinism assumed (tested later by the two-run comparison) |
| §4 attribute | reading of the Lean 4.33.1 source; the extension's entries after `importModules` with `loadExts := false` and the gate entry assumed |
| §5 cuts | reading of the decisions register |
| §6 files, §7 wiring | reading of each precedent; the new lines not run |
| §8 schema | tested (one tsgo typecheck, one bun run, 16 controls), bounded to one instance and the TS half; `command` and `inputs` added after the run, untested |
| §9 slice | reading for every name and line; `statement`, `axioms` and the unplaced counts are emit-time values not measured; the three witnesses at the ceiling assumed |
| §10 gate | the conditions quoted verbatim (reading); their checks proposed, the TS half tested |
| §11 landing | not run |

The brief (`brief-gemini-implementation.md`): its Rules keep `brief-gemini.md`'s last two bullets
verbatim and replace the first two for implementation, as seat B's brief asks.

## 9. Minutes spent

About 27 minutes by the shell clock (`date +%s` at start 1790901433), within the 45-minute bound.
