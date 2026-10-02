# Brief for seat B: the semantics report, spec v3 and the brief Gemini builds from (2026-10-01, ~45 minutes)

You are a bounded probe in `/Users/pooks/Dev/lean4-effect4` (branch `refactor/phase1-phase3`,
HEAD `198dd533`). Gemini proposed a domain model for documenting the language's semantics and
proof state as data (`docs/research/2026-10-01-semantics/gemini/domain-model-spec.md`, v2);
Codex reviewed v1 (`/private/tmp/codex-second-eyes-2026-10-01/domain-spec-review/review.md`,
`.../domain-spec-ledger-review.md`); the coordinator reviewed v2
(`docs/research/2026-10-01-semantics/review-gemini-v2.md`: read it first, it lists the errors
with file:line). Gemini will implement. Your job: turn the three into one implementation spec
every name and path of which is checked against the tree, and the brief Gemini lands from. Stop
after about 45 minutes at a coherent place and write the receipt.

## Rules

- Write only under `docs/research/2026-10-01-semantics/seat-B/`. Edit nothing else. Run no
  `git`, no `lake`, no `make`. One exception, bounded: you may typecheck one TypeScript file and
  run one bun script in your folder, the way Codex did (`.../domain-spec-review/commands.json`,
  `api-corrected.mts`, `runtime.mts`: import from the absolute path
  `/Users/pooks/Dev/lean4-effect4/ts/eff/node_modules/effect/dist/Schema.js`, compiler
  `/Users/pooks/Dev/lean4-effect4/ts/eff/node_modules/.bin/tsgo --noEmit --strict`, version
  7.0.0-dev.20260629.1, bun 1.4.2). No installs. Never `tsc`.
- Every theorem, definition, command and path you name: found with `grep`, cited `file:line`.
  Evidence words: proved, tested, reading, assumed. Plain words.
- Decide nothing the coordinator owns (decisions rows, the register); propose, with the reason.

## Read, in this order

1. `AGENTS.md` (vocabulary, trust, working rules). 2. `review-gemini-v2.md` (the errors).
3. Codex's two reviews (their §8 acceptance conditions and the ledger review's four sections).
4. Gemini's `domain-model-spec.md` v2 and `note.md` §§ on the annotation schema and tagging
   plan; `chapter-table.md` and `lemma-census.md` only for the claim lists they already hold.
5. The owner's plan: `docs/research/2026-10-01-landing/status-2026-10-01-evening.md` §7, §7b,
   §7c (the attribute, the census, the generated group, "measured, never drawn").
6. The mechanisms you reuse: `src/Effect4/Laws/Auto/Obligations.lean` (goals, `#proof_wanted`,
   `#obligation_proved`, `#typed_state_obligations`), `tools/ProofGraph/Ledger.lean`,
   `tools/ProofGraph/Proof.lean` (`ProofRef.validate`), `src/Effect4/Laws/Auto/Census.lean`
   (`#auto_census`, the attribute/extension pattern), `tools/Tools/Architecture.lean`
   (`loadCounts`, `roots`, `concludesObligation`, `isNoise`) and `tools/Tools/ArchitectureRoles.lean`
   (the one hand-written input, its totality gate), `Test/Audit/AxiomGate.lean` (the policy
   around lines 60–120 and 420–490), `Makefile` lines 160–215 (`GEN_GROUPS`, `GENERATED_PATHS`,
   the `$(GEN)/<group>` recipes) and 375–400 (`gen-architecture`) and 460–480 (the `$(CHK)`
   host checks), `docs/GENERATED.md` lines 55–90 (the table a group is registered in),
   `ts/eff/README.md` and `ts/eff/check.ts` (how ts/eff checks a generated file today),
   `Test/Counterexamples/REGISTER.md` (the id column; TYPED ids run 001–029, 023 unused).

## The coordinator's rulings for the spec (confirm or refute each in at most five lines)

- R1 The authored registry is a Lean module, `tools/Tools/SemanticsRegistry.lean`, the second
  hand-written input beside `ArchitectureRoles.lean`: first-order data only (structures with
  `deriving Repr`), concepts, claims, literature references, counterexample references, cuts.
  Not JSON (the owner's §7b named `tools/architecture/chapters.json`; say in one paragraph why a
  Lean file is better here, or why not: the driver already loads Lean, names are `Name` values
  checked at run time against the loaded environment, one parser).
- R2 Status is derived from the environment, never authored. goal := a theorem whose type
  concludes `ProofGraph.Obligation p` (`Obligations.lean:15-24`); wanted := `<goal>.wanted`
  exists with the `ProofWanted` marker (`:26-31`, `:60-63`); proved (ledger) := `<goal>.checked`
  exists and `ProofRef.validate` accepts it (`:76-79`); proved (plain theorem) := the named
  constant is a `thmInfo` with `collectAxioms ⊆ [propext, Quot.sound]`, the Boolean named
  `withinSemanticAxiomCeiling`, the full gate verdict a separate per-run receipt
  (`pass | fail | notAudited` with the policy's identity, Codex ledger §2); refuted := the named
  counterexample theorem exists within the ceiling and its id is a row of
  `Test/Counterexamples/REGISTER.md` (the driver reads the id column; an id the register lacks
  is a refusal with the location); absent := a claim with no witness and no goal (authored
  reason required); assumed := an external statement with no local evidence. Statement strings
  are printed from the environment at emit time; the registry holds names, not propositions.
- R3 The report is `generated/semantics.json`, a plain record, bytes deterministic (no wall
  clock; provenance = git commit, `lean-toolchain` content, the roots, the policy identity). Its
  Effect Schema is a flat file in `ts/eff/` (name it after the precedent you find), checked by
  a new `make check-semantics` in the host tier, not by `check-tsgo`. Typecheck the schema once
  with tsgo 7 and decode the slice's JSON once with bun; record both in the receipt.
- R4 A declaration gets its concept by an attribute registered in `Laws/Auto/` beside
  `#auto_census` (`@[semantics "residual-program-typing"]`, or the name you argue for), with a
  module-level default in the registry shown as `inherited` (provisional) in the report;
  `#semantics_census` prints per concept the tagged declarations with axioms, the claims with
  status, and the Laws-graph theorems no concept covers, relative to the loaded roots (stated).
  Specify the extension, the attribute's arity and the command's output; the owner's §7b
  wording (`@[chapter …]`, `#chapter_census`) is superseded by concept-first (Codex §6).
- R5 The first slice is Gemini's §6 corrected: concept `residual-program-typing`; proved
  `Effect4.Program.Typed.seq_typed` (`Laws/Program/Typed/Seq.lean:59`; the statement printed,
  not typed); wanted `Effect4.Program.Typed.M3bAssembly.denoteR_typed` (goal
  `Laws/Program/Typed/Assembly.lean:1637`, `Obligation (DenotesTyped root)`; marker `:1839`);
  absent `typedProg_bind_closed` (reason: refuted below); refuted
  `Test.Program.TypedProgBindRed.typedProg_not_bind_closed` (`:32`), which has no register row:
  propose the row (next free TYPED id) in your receipt, and make the slice refuse until the row
  exists. Codex §8's six acceptance conditions are the slice's gate, verbatim.
- R6 The cut is in the model as an applicability decision: `{ conceptId, decisionRow, what is
  excluded, reason, owner }`, never a status (rows 163, 128 at least; find the others the owner's
  §7 names).

## Produce (under `seat-B/`)

1. `spec-v3.md`: the model (Lean types, every field with its source of truth: environment,
   registry, or derived), the derivation rules of R2 as a table, the file list with exact paths
   and the precedent each follows (`file:line`), the Makefile and `docs/GENERATED.md` wiring
   (the exact lines to add, in the style of the `census` and `host-protocol` rows), the schema
   file and `check-semantics`, the slice's expected JSON (names from the environment, no
   timestamp), the six acceptance conditions as the gate, and the landing order as commits by
   explicit paths with the narrow build each needs (`lake build Tools` or the lake target you
   find for `tools/Tools`; `lake env lean <file>` for a test).
2. `brief-gemini-implementation.md`: the dispatch brief Gemini lands from. Reuse the Rules
   section of `docs/research/2026-10-01-semantics/brief-gemini.md` verbatim except that Gemini
   now edits the named paths, builds narrowly (one `lake` at a time), and commits on its own
   branch `gemini/semantics-slice` from `198dd533` by explicit paths, never `git add -A`; the
   root imports and `Test/Audit/AxiomGate.lean` untouched unless the spec names the anchor;
   `docs/core/decisions.md` never; receipt format from `AGENTS.md` (base and head, files,
   commands and results, axiom output, open obligations, bounded evidence first).
3. `receipt.md`: what you read, what you ran (the tsgo and bun commands, exit codes, outputs),
   the rulings confirmed or refuted, the proposed register row, open questions for the
   coordinator (at most five), minutes spent, evidence class per section.
