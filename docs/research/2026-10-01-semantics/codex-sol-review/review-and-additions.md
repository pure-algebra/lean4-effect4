# Gemini contribution: one model, precise claims

**Before adoption:** correct the draft's first-order claim about `RProgram`. Stored `Eff` syntax uses program-tree continuations; the proof-side `RProgram` carries Lean functions. Keep the new concept-first organization and the existing report API. The remaining refinements concern interpretation and ownership, not a second representation or registry.

Two independent **GPT-6.1 Sol** reviewers covered API coherence and literature interpretation. This note reconciles their proposals against the source. Their full notes and evidence are retained beside it. Both read the active 640-line `gemini/semantics-v1.md` snapshot, SHA-256 `371ec83de053edbf55e56d4418f2afc049676bdf8a5e34b9f73d47430f90d00c`, at integration HEAD `d7b9cb113d6014f9439fb846bb79713ca73294e9`. The draft is ongoing; unfinished sections are pending work. Neither reviewer edited Claude's or Gemini's files or ran a build. The parent rechecked 64 source hashes and all recorded exact excerpts: no differences.

## Five refinements to adopt

1. **Separate stored syntax from its semantic carrier.** Replace the claims at draft lines 83, 136–137 and 635 with the paragraph below. `Eff.bind` stores two child trees (`Program/Eff.lean:277`). `RProgram` aliases `Effects.Program RSig ExitV` (`Laws/Program/Sched.lean:206`), whose `vis` contains `Answer operation → Program signature A` (`effects/Effects/Algebra/Program.lean:33–38`). Row 163 excludes stored function values; it does not ban functions in the semantic model.

2. **Make the claim-to-evidence association explicit.** A `witness` is checked at its own printed proposition. A `goal` supplies an independently stated target. A `refutedBy` entry validates a theorem and register reference; the association with the English claim is authored, not an automatic proof of negation. Keep the full register link and attacked revision visible for `contestedBy`; a leading `SEEDED` word can coexist with later repair history. This follows spec v3 §3 and the coordinator's registry-link ruling, without adding fields.

3. **Classify by the actual judgment.** Retain the draft's correction that `machineTyped_not_halted` is an invariant consequence, then remove the remaining suggestion at lines 273–274 that it establishes progress. It projects an invariant field and supplies no successor (`Assembly.lean:310–315`). Likewise, codec exactness is not canonical forms for `Fits`, weakening is not substitution, and the no-function-value cut leaves positional environment and bind obligations. Standard textbook roles are questions to assess, not mandatory badges for every concept.

4. **Keep each semantic connection and its conditions visible.** `DenotesTyped`, handler fulfillment, step simulation, and replay agreement are separate claims. The finite scheduling theorem requires a duplicate-free queue, readiness and sufficient rounds; it promises callback entry, not completion or eventual host input (`Scheduling.lean:413–440`). M7's `run_eq_ref` compares internal observations at the empty external table and oracle (`RuntimeR.lean:198–215`). Neither an invariant nor a simulation reference adds liveness.

5. **Preserve one owner per fact.** Let the planned generated report own statements, statuses and counts; remove their hand-maintained duplicates from prose. Report `absent` counts as evidence inventory, not work owed: the reason distinguishes an owed claim from an excluded role and links the existing `Cut`. The amended committed census covers concept-named modules; the whole-Laws census is separate. Zero unplaced declarations is classification coverage of that population, not completed proofs. After cleanup commit `45e9b532` integrates, reuse public `ProofGraph.readGoal`, `disallowedAxioms`, and the existing validators instead of copying the old private reader. The helpers are tested on this branch, not yet observed on integration.

## Ready-to-use prose

### Reading the model and its evidence

Stored `Eff` syntax uses program-tree continuations with positional inputs. `RProgram` is the proof-side semantic carrier `Effects.Program RSig ExitV`; visible operations carry Lean function continuations. Those functions belong to the semantic model and are not stored function values in `Eff` or `Val`.

`Fits` is value membership in a world. `TypedProg` is residual program typing: ordinary operation clauses require permission and typed continuations for permitted replies at later worlds. Its `unguard` and `finishFinalizer` clauses require an exit payload without a continuation premise; `scopeExit` separately requires a live scope and typed continuation. `DenotesTyped` connects admitted source points to that residual judgment. These definitions resemble protocol-based program logics, but identifying them with weakest preconditions would require a named execution interpretation and a stated correspondence. The unrestricted bind counterexample alone does not settle every possible weakest-precondition interpretation.

A claim's title, role and selected evidence express an authored interpretation. The printed proposition states exactly what its theorem proves or its ledger goal requests. Checking a theorem does not check the English interpretation. Refutation and contest links therefore expose the registered attacked statement and revision alongside the witness. Historical attacks do not automatically refute repaired propositions.

Progress, preservation, scheduling service and interpreter agreement ask different questions. An invariant can exclude a halted configuration without establishing a successor. Progress must account for finished states, permitted transitions and live frontiers; preservation concerns covered transitions. Finite scheduling service concerns actual callback entry under its stated readiness and bounds. Internal replay agreement retains its empty-host fragment. None of these statements alone proves termination or eventual host cooperation.

The generated table is intended to own evidence status; prose explains meaning and scope. Cuts own applicability. Declaration placement has one primary home, while claims and literature may link across concepts. Counts describe their stated population and selected evidence, not an unrestricted measure of completeness.

### Using the literature

Use the existing relations `definitionUsed`, `proofTechnique`, `adaptedResult`, `analogy`, and `excludedFeature`. A verified contents heading establishes a locator, not a theorem's applicability. Keep ATTAPL's logical-relations chapter at the verified chapter 6; its chapter body is unavailable here.

| Source | Useful connection | Boundary to state |
| --- | --- | --- |
| Ahmed on mutable-state types | Worlds, monotonicity, semantic-store circularity | Does not impose step indexing on the current finite structural `Fits` definition |
| Interaction Trees | Semantic operation continuations as meta-level functions | That source is coinductive; the imported `Effects.Program` here is inductive |
| De Vilhena–Pottier | Effect protocols and weakest-precondition reasoning | An analogy until a particular local judgment and correspondence are stated; bind rules depend on the chosen judgment |
| PLF / Harper | Precise progress, preservation, canonical-forms and substitution questions | Apply each to the local judgment; do not substitute codec or invariant facts |
| Lynch–Vaandrager | Simulation and trace-inclusion methods | Their safety methods do not supply liveness; local one-step interfaces are particular instances, not the whole paper |

## Evidence and adoption

Detailed locators, body readings, and proposed wording are in [literature.md](literature.md); API ownership and amendment precedence are in [api.md](api.md). The body locators proposed by the literature reviewer must enter the existing citation audit before use as authoritative registry locators. No book theorem is imported by this note.

Reconciliation details: the raw API note names the later branch head `9190c779`; the actual helper change is `45e9b532`. The raw literature note's first-order cut locator is lines 136–137 in the retained draft; its general phrase “closing markers” is narrowed above to the two constructors that omit a continuation premise. Decisions row 117 already records the closed-root-row ruling while retaining a separate per-position obligation; do not copy spec v3's older blanket “open” description.

This contribution is source-reviewed prose, not a semantics-producer implementation or a new proof receipt. Main's generated semantics report and driver were absent at the snapshot. The private metaprogramming branch's tested changes and remaining proposals have their own closing receipt.
