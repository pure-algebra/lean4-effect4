# Bounded API and report coherence contribution

The report needs an explicit boundary between checked statements and authored associations. Five adjustments below use the existing model and owners; they propose no additional registry or general framework.

Evidence: source reading at main `d7b9cb113d6014f9439fb846bb79713ca73294e9` and audit worktree `9190c779032df0d361a1bf3ef0eace3cefd6b95b`. The shared reader and ceiling helper are implemented in the audit worktree; integration was not observed on main. None of the semantics registry, driver, attribute, generated report or `docs/core/semantics.md` files exists in either checked tree. This is a proposed documentation contribution, not an implementation or compilation receipt. The earlier Gemini drafts remain research history: `gemini/domain-model-spec.md:127` says its model is implemented, and `gemini/note.md:77-88` presents two conflicting report representations. Use v3 plus the coordinator amendments for the new draft, and remove or explicitly retire those claims when reconciling companions.

### API-1: Specify the authored claim-to-evidence association

The witness path validates a theorem against its own type. The refutedBy path adds an existing non-RETIRED register id, but no independent target or checked row-to-witness logical relation. This validates real evidence while leaving its association with the English claim authored. It is a report interpretation gap, not a Lean type-safety defect.

Evidence: `main:docs/research/2026-10-01-semantics/seat-B/spec-v3.md:92-121`; `main:docs/research/2026-10-01-semantics/seat-B/spec-v3.md:202-212`; `main:docs/research/2026-10-01-semantics/seat-B/brief-gemini-implementation.md:124-125`; `audit:tools/ProofGraph/Proof.lean:23-33`; `audit:tools/ProofGraph/Ledger.lean:88-95`.

Minimal improvement: Define the printed proposition as authoritative for witness claims; use the existing goal pointer when an independent exact proposition must be discharged. Describe refutedBy as a registered refutation with checked witness and authored association. Display both the row and witness; do not claim an automatic negation check. Singleton goal checks establish selected evidence only, not whole-scope graph coverage.

### API-2: Separate absent evidence from applicability

The documentation brief permits absent for an owed claim and a non-applicable standard role. The spec says cuts are applicability decisions, never statuses, and the schema counts both absent cases together. Reading absent counts as work owed would be incorrect.

Evidence: `main:docs/research/2026-10-01-semantics/brief-gemini-documentation.md:35-44`; `main:docs/research/2026-10-01-semantics/seat-B/spec-v3.md:310-328`; `main:docs/research/2026-10-01-semantics/seat-B/probe/semantics.mts:123-128`.

Minimal improvement: Keep both existing records. Treat absent as no selected local evidence; require its reason to say owed or not applicable and cite an existing Cut/decisions row for exclusions. Label aggregate counts as evidence counts. Do not add a new status, applicability framework or completion ratio.

### API-3: A contest link needs its attacked revision visible

contestedBy carries a register id, leading status word and null witness in v1. A SEEDED row can also say then REPAIRED in its remaining cell, and the decisions specify premise repairs. The report alone cannot prove that an old attack applies to the current printed proposition.

Evidence: `main:docs/research/2026-10-01-semantics/seat-B/spec-v3.md:175-179`; `main:Test/Counterexamples/REGISTER.md:13-28`; `main:Test/Counterexamples/REGISTER.md:249-251`; `main:docs/core/decisions.md:263`; `main:docs/core/decisions.md:268`.

Minimal improvement: Retain the link beside status and call it a registered contest association. Link to the complete existing register row, and describe its attacked revision in prose. Do not derive a current refuted status from a contest link or imply a repaired historical witness attacks new premises. No new revision register is needed.

### API-4: Use the shared ledger reader after its integration

The spec tells the driver to copy private readGoal. The audit worktree now exposes ProofGraph.readGoal and factors disallowedAxioms in ProofGraph.Proof; main still contains the private original. Copying the old reader after integration would give the same proposition extraction a second owner.

Evidence: `main:docs/research/2026-10-01-semantics/seat-B/spec-v3.md:204-206`; `main:docs/research/2026-10-01-semantics/seat-B/spec-v3.md:334-336`; `audit:tools/ProofGraph/Ledger.lean:23-35`; `audit:tools/ProofGraph/Proof.lean:13-16`.

Minimal improvement: Condition the documentation on integration: after 9190c779 is landed, reuse ProofGraph.readGoal and ProofRef.validate/ProofGraph.check. Use disallowedAxioms for any display ceiling computation instead of a second literal policy. Preserve the current diagnostics and semantic ceiling; do not widen this into a generic resolver API.

### API-5: Keep the report population separate from concept and literature links

The coordinator amendment narrows the committed population to concept-named modules, replacing the whole-Laws population in v3. A declaration has one primary home, while claims can name evidence across concepts and have many literature links. Conflating these produces misleading placement/completion counts.

Evidence: `main:docs/research/2026-10-01-semantics/seat-B/spec-v3.md:252-258`; `main:docs/research/2026-10-01-semantics/seat-B/spec-v3.md:283-308`; `main:docs/research/2026-10-01-semantics/seat-B/brief-gemini-implementation.md:126-130`; `main:docs/research/2026-10-01-semantics/seat-B/probe/semantics.mts:50-54`.

Minimal improvement: State the amended population in the report and explain its distinction from the whole-Laws command. Keep declaration placement, claim references and literature references separate. Enforce the same five literature relation values in the producer as the existing schema; avoid introducing relation vocabulary from v2.

The following section is ready to insert in the concept-first draft. It has 539 words, including the table and heading; its report behavior remains specified until implementation lands.

---

## API and evidence boundary

This report distinguishes authored descriptions from evidence checked in the loaded Lean environment. A claim's title and role explain why its evidence matters; the printed proposition states exactly what was proved or requested. The report does not check that English descriptions follow from that proposition.

| Item | Owner | What readers can conclude |
| --- | --- | --- |
| Claim identity, concept, role, title and evidence pointer | `Tools.Semantics.registry` | These are authored assignments. They identify a question and its selected evidence. |
| Theorem statement, universes, module and axioms | Loaded Lean environment | A `witness` is checked as a theorem of its own printed proposition under the semantic axiom ceiling. |
| Obligation proposition and checked/wanted evidence | Existing `ProofGraph` ledger | A `goal` is a declared question. Its checked witness or wanted placeholder must match that question, including its binders and universes. A report of selected goals does not establish coverage of an entire ledger scope. |
| Refutation and contest associations | Registry links to `Test/Counterexamples/REGISTER.md` | The report checks the referenced row and, when supplied, the witness theorem. The association with the claim is authored; checking these references does not establish that the witness negates an independently stated target. Read the row's attacked statement and revision alongside the printed evidence. |
| Applicability | Decisions register, referenced by `Cut` | A cut limits the question's domain. It does not prove, refute or discharge the question. |
| Declaration placement | Explicit concept tag, then registry module default | Each eligible declaration has one primary home; inherited placement is provisional. Claims may refer across homes, and literature references describe further relationships. Neither creates additional declarations or discharged goals. |

`proved`, `wanted`, `refuted`, `absent` and `assumed` describe the selected evidence. `absent` means that no witness, goal or refutation is selected; its reason must distinguish an owed obligation from a role outside the current cut. For the latter, name the existing decisions row and exclusion. Status counts are evidence inventories, not counts of obligations owed or a completion percentage.

`contestedBy` remains visible beside status. A retained attack against an older statement does not refute a repaired statement with new premises. Follow the register's full row for that history; its leading status word alone cannot settle which revision is attacked. Conversely, an open goal with a contest link remains open and contested until its statement and evidence are reconciled.

The semantic axiom ceiling is narrower than the repository trust gate. A producer that checks the ceiling has not thereby run `Test/Audit/AxiomGate.lean`; the run receipt records the separate gate result. Committed report bytes carry stable inputs, toolchain and policy; the receipt carries the source revision and run state.

The committed placement census covers the modules named by the registry concepts. The whole-Laws census is a separate command result. Zero unplaced declarations means classification coverage of that stated population; required claims may still be absent.

Literature uses the source index and citation audit. Keep the existing five relation names (`definitionUsed`, `proofTechnique`, `adaptedResult`, `analogy`, `excludedFeature`), and derive the bibliography from those references. Prose points to the generated evidence table, the decisions register and the system map instead of maintaining another status list.

---

Verification: checked both HEAD revisions, file presence, declaration definitions, the live register rows and amendment precedence. Every finding has exact source excerpts and SHA-256 hashes in `api-evidence.json`. No compiler or global gate was run, respecting the parent's build lane. Only this file and its evidence JSON were written.

## Delta after the new Gemini draft appeared

Read-only snapshot at `2026-10-02T01:55:50.442079+00:00`: `docs/research/2026-10-01-semantics/gemini/semantics-v1.md`, SHA-256 `371ec83de053edbf55e56d4418f2afc049676bdf8a5e34b9f73d47430f90d00c`, 640 lines. Gemini is actively writing this file. These observations apply to this snapshot; omissions are unfinished drafting, not failed deliverables. The original file-presence checks in the evidence JSON remain the earlier checkpoint, and this later snapshot supersedes the earlier absence of `semantics-v1.md`.

1. **The new organization resolves the old chapter-first presentation.** Lines 18–28 name the ten concepts, and lines 135–144 distinguish the bind refutation, per-construct compatibility and closed-row premise. These are improvements consistent with the proposed section. The report's authored-association and census boundaries still need explicit wording; their current omission is not a failure while the draft is in progress.
2. **Keep one status owner when reconciling the draft.** Lines 91–106 point to the generated table but also write “Proved” and “0 open goals” by hand. That contradicts the documentation brief's explicit instruction at lines 75–77. Keep the theorem names and explanation, and let the generated table carry statuses/counts. References to `generated/semantics.md` should be described as planned until that file exists. This tightens ownership without changing the API.
3. **Limit the first-order guarantee to stored syntax.** Lines 136–137 call `Val → RProgram` an AST branch, and lines 634–635 say all continuations in `Eff` and `RProgram` are first-order data. Actual `RProgram` is `Effects.Program RSig ExitV` (`src/Effect4/Laws/Program/Sched.lean:206`), whose `vis` constructor stores a Lean function `.lake/packages/effects/Effects/Algebra/Program.lean:37–38`. Use: “Stored `Eff` syntax is first-order data; `RProgram` is a semantic carrier with Lean function continuations, not another stored program representation.” This is a documentation correction, not a proposed production change.
