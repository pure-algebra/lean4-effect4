# Brief for Gemini: land the semantics report's first slice (2026-10-01)

You implement the slice specified in
`/Users/pooks/Dev/lean4-effect4/docs/research/2026-10-01-semantics/seat-B/spec-v3.md` (spec v3,
seat B). It replaces your `gemini/domain-model-spec.md` v2 as the authority for this work; where
the two differ, the spec wins, and every name and path in it was checked against the tree at
`198dd533`. Base `198dd533` on `refactor/phase1-phase3`; your branch `gemini/semantics-slice`, in
your own worktree. The spec's §0 is the one thing to keep in mind: commit C4 cannot pass until
the coordinator adds register row `E4-TYPED-CE-030`; until then the producer's refusal of it is
the expected result.

## Rules

The Rules of `brief-gemini.md` (2026-10-01), with the first two bullets replaced because this is
an implementation, not a read-only probe; the last two are verbatim.

- Edit only the paths the spec names (§6), at the anchors it names, and nothing else. Commit on
  your own branch `gemini/semantics-slice`, created from `198dd533`, in your own worktree (never
  the main checkout `/Users/pooks/Dev/lean4-effect4`, whose working copy holds the owner's
  uncommitted edits to `src/Effect4/Laws/Program/Typed/Commands/Bookkeeping.lean` and
  `Test/Program/LayerSharingContract.lean`). Stage by explicit paths, `git add <path> …`; never
  `git add -A` or `git add .`; read `git status` before each commit. No `git merge`, `git
  rebase`, `git reset` or `git push`. The root imports (`src/Effect4.lean`, `src/Effect4/Laws.lean`,
  `Test/All.lean`) and `Test/Audit/AxiomGate.lean` stay untouched except at the anchors spec §6
  names. `docs/core/decisions.md`, `Test/Counterexamples/REGISTER.md`, `lakefile.toml`,
  `tools/Tools/ArchitectureRoles.lean` and `src/Effect4/Schema/Bridge.lean`: never. A worktree has
  no `docs/research` (it is 2 GB and never copied); read the spec at the absolute path above and
  write your receipt there too (below).
- Build narrowly, one `lake` at a time: before each commit, `lake build <Module>` for the modules
  the commit touches and their direct dependents, and `lake env lean -DwarningAsError=true <file>`
  for a test file, exactly as spec §11 lists them. No `lake build` of the whole tree, no
  `make check`, `make check-full` or `make gen` (the owner runs the sweep). If you run anything
  TypeScript-related, it is tsgo 7 (`ts/eff/node_modules/@typescript/native-preview`) and you
  name its version; `tsc` and `typescript@5.x` are never run.
- Evidence words on every claim: **proved** (a kernel theorem you located, file:line, with its
  statement quoted), **tested** (a finite check someone ran, cited), **reading** (read in code or
  a document), **assumed** (not checked). Cite `file:line` for every theorem or definition you
  name, and `vendor/effect-4.0.0-rc.112/src/...:line` for every rc.112 behaviour you mention.
  Never name a theorem you have not found with `grep`.
- Plain words. No "sound", "complete", "equivalent", "preserves" or "fully reified" without
  the exact judgment, theorem, assumptions and remaining boundary. Nothing you write is a
  decision: the decisions register (`docs/core/decisions.md`) is the coordinator's; you propose
  rows, you do not rule them.

## The trust rules that bind this code (AGENTS.md, Trust and Working)

No `sorry`, `partial`, `unsafe`, `native_decide`, `axiom`, `extern`, `implemented_by` anywhere.
Every warning is an error (`-DwarningAsError=true`, `lakefile.toml:17`): an unused variable or a
dead tactic fails the build. In a new or touched proof under `src/`, no `simp_all`, no
`first | …`, no `try`; a hand `simp` is `simp only [...]`. The slice needs no new theorem in
`src/`; the attribute module is meta code. Tools under `tools/` are outside the axiom gate
(`lakefile.toml:48-55`); `src/Effect4/Laws/Auto/Semantics.lean` is inside it, which is why spec
§4.1 adds it to `auditImplementationModules`.

## Read first, in this order

1. `AGENTS.md` (vocabulary, trust, working rules).
2. The spec, all of it; §0, §3, §4 and §11 are the ones you build from.
3. The precedents the spec cites, at their lines: `tools/Tools/ArchitectureRoles.lean`,
   `tools/Tools/Architecture.lean:163-196,753-781`, `tools/Effect4Gen/Check.lean:240-264`,
   `tools/Drivers/ProgramStructureCheck.lean`, `tools/Tools/HostProtocol.lean`,
   `tools/ProofGraph/Ledger.lean`, `tools/ProofGraph/Proof.lean`,
   `src/Effect4/Laws/Auto/Obligations.lean`, `src/Effect4/Laws/Auto/Census.lean`,
   `Test/Audit/Obligations.lean`, `Test/Audit/AxiomGate.lean:60-120,423-490`,
   `scripts/check-host-protocol.py`, `ts/eff/eff.gen.ts:42,60-70,390-399`, `ts/eff/check.ts`,
   `Makefile:160-215,270-300,460-480`, `docs/GENERATED.md:55-90`, `generated/AGENTS.md`.
4. The probe: `seat-B/probe/semantics.mts` (the schema to copy into `ts/eff/semantics.ts`),
   `seat-B/probe/decode.mts` (the decode controls to carry into `ts/eff/test/semantics.test.ts`),
   `seat-B/probe/slice.json` (the instance they decoded).

## The work, as five commits (spec §11 has the exact commands)

- **C1** the attribute and `#semantics_census` (`src/Effect4/Laws/Auto/Semantics.lean`), its
  fixture `Test/Audit/SemanticsCensus.lean` with green output and red controls under
  `#guard_msgs`, and the three anchors (Laws root, `Test/All.lean`, the gate's module list).
- **C2** the registry (`tools/Tools/SemanticsRegistry.lean`, spec §2.1 and §9.1), the library
  (`tools/Tools/Semantics.lean`, no `main`; spec §3: every status through `ProofRef.validate` or
  `ProofGraph.check`, never a name-existence test), the producer `tools/Drivers/Semantics.lean`,
  and the refusal controls
  (`tools/Drivers/SemanticsControls.lean`, one mutation per refusal of spec §3 and §10 condition 2,
  plus the control that the driver reads a tag from an imported module).
- **C3** the slice's two tags in `src/Effect4/Laws/Program/Typed/Seq.lean`.
- **C5** (land before C4) `ts/eff/semantics.ts`, `ts/eff/check-semantics.ts`, the pinned cases
  `ts/eff/test/semantics.test.ts` over the fixture `ts/eff/test/semantics.fixture.json` (the
  probe's controls and instance, with `command` and `inputs` added), three rows in
  `ts/eff/README.md`'s file table, `scripts/check-semantics.py`, the Makefile and
  `docs/GENERATED.md` lines of spec §7, exactly as written there.
- **C4** after the coordinator tells you row `E4-TYPED-CE-030` exists on your base or you rebase
  onto it by the coordinator's instruction: run the producer into `generated/`, commit the two
  outputs, run `python3 scripts/check-semantics.py` once (it builds only its two drivers).
  Not `make check-semantics` or `make gen-semantics`: both order-only depend on `build`, the whole
  tree, as `gen-architecture` does (`Makefile:380`), so they belong to the owner's sweep. Before
  the row exists, run the producer once and record its refusal (exit 1, naming `bind-closed` and
  `E4-TYPED-CE-030`) as the expected red.

Stop at a coherent place: after C3 and C5 if the row has not arrived, with C4's red recorded.
If a precedent the spec cites does not behave as the spec says (for example the extension reads
no tags after `importModules`, spec §4.1, assumed), stop at that commit, write what you saw with
the command and its output, and propose the fix in the receipt; do not change the design alone.

## The receipt

Write `/Users/pooks/Dev/lean4-effect4/docs/research/2026-10-01-semantics/gemini/receipt-slice.md`
(untracked; the coordinator tracks what matters). AGENTS.md's format, in this order: **first**, the
one thing the coordinator must know before merging; then base and head commits and the commit
list; the changed files per commit; every command you ran with its exit code and the lines of
output that matter; the axiom output (`#print axioms` for any theorem you add; the census and
controls output); open obligations (C4 if waiting; the gate entry of spec §4.1 stays assumed until
the owner's sweep runs the gate); and which evidence is bounded (one concept, one instance, the
controls you ran) or host-only (the bun and tsgo runs). Proposed decisions rows or register rows
go in the receipt with their reason, never in the registers.

## Coordinator's amendment (2026-10-01 ~22:40): rulings, base, sources

Where this section and the spec differ, this section wins.

- **Base is `66b7c525`** (branch `refactor/phase1-phase3`), the commit that adds register row
  `E4-TYPED-CE-030` (`Test/Counterexamples/REGISTER.md:258`, SEEDED). Create
  `gemini/semantics-slice` from it. C4 can run; the refusal the spec's §0 describes is no longer
  the expected result. Status SEEDED, not REPAIRED: one shape of four has its lemma.
- **The absent item** is the `onFailure`-shape compatibility lemma owed by decisions row 148 (a
  claim with no witness, no goal and no refutation), not `typedProg_bind_closed`, which is the
  refuted item's own statement and would count one statement twice.
- **The link from a register row to a claim** lives in the registry (`contestedBy`, `refutedBy`);
  the register's columns stay as they are.
- **The whole-Laws unplaced count** is not in the committed `generated/semantics.json`: it moves
  with most landings and would make `check-gen` churn. The committed report states its census
  universe (the modules the registry's concepts name) and the counts over that universe;
  `#semantics_census` prints the whole-graph number, and the map reads it at `gen-architecture`
  time. Spec §4.4 and §2.3 are read with this change.
- **The attribute** is a parametric attribute with an `initialize` and one
  `auditImplementationModules` entry, as spec §4.1 proposes. Codex's metaprogramming audit
  (`docs/research/2026-10-01-metaprogramming-audit/brief-codex-metaprogramming.md`) reviews that
  pattern read-only and touches none of your files; a later Codex slice may move your census onto
  a shared helper module. Nothing for you to wait on.
- **DI-18** (`docs/DESIGN-ISSUES.md:91`, "no `import Lean` in the audited closure") is
  contradicted by five modules at HEAD and its script is gone; the owner rules on the amendment.
  Proceed as `Laws/Auto/Census.lean` and `Laws/Auto/Obligations.lean` do today; the
  reconciliation is the coordinator's, not yours.
- **Literature in the registry comes from the audit, never from memory.** Every
  `LiteratureRef` you write is a row of `docs/research/2026-10-01-semantics/citations-audit.md`
  with status `verified` or `corrected` (the locator as that row gives it), and its source is a
  row of `docs/research/2026-10-01-semantics/sources/README.md` (cite its sha256 in the
  registry's docstring for the entry). A locator the audit marks `unverifiable` is written with
  evidence `assumed` and the note "owner's copy owed"; the full texts of TAPL and ATTAPL are not
  on this machine, so no theorem, rule or in-section page number from them is `verified`. The
  corrections that bind your v2 text: ATTAPL ch. 6 is Crary, "Logical Relations and a Case Study
  in Equivalence Checking", p. 223; ch. 7 Pitts, p. 245; ch. 8 is Harper and Pierce, "Design
  Considerations for ML-Style Module Systems", p. 293 (not logical relations, not
  Dreyer–Crary–Harper); ch. 3 is Henglein, Makholm and Niss, "Effect Types and Region-Based
  Memory Management", p. 87 (Walker's substructural systems is ch. 1, p. 3). TAPL ch. 13
  References p. 153, ch. 14 Exceptions p. 171, ch. 19 Featherweight Java p. 247 (§19.3 Nominal and
  Structural Type Systems p. 251: `tapl-19-nominal` names a section), ch. 20 Recursive Types p. 267
  (there is no Generic Java chapter). PFPL ch. 28 Control Stacks p. 261; concurrency is chs. 39–41.
  De Vilhena and Pottier's POPL 2021 paper is "A Separation Logic for Effect Handlers", DOI
  10.1145/3434314. Rendel and Ostermann appeared at Haskell 2010. The audit's §5 lists the rest.
- **Your receipt** goes where the brief says; add a section "Companion files corrected" naming
  every line of `gemini/note.md`, `chapter-table.md`, `lemma-census.md` and `domain-model-spec.md`
  you change to match the audit, or say that you left them as history.

**Base, final (coordinator, ~22:55):** branch from `8c9be258` on `refactor/phase1-phase3`. It holds
`66b7c525`'s register row, tonight's tracked notes (`36650548`) and the DI-18 re-ruling
(`docs/DESIGN-ISSUES.md`): a Laws module that imports Lean's elaboration APIs is audited like any
other, so `src/Effect4/Laws/Auto/Semantics.lean` needs no exemption text, only the gate entry spec
§4.1 names.
