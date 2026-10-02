# Literature and interpretation contribution for Gemini

The coordinator should keep the concept-first structure, but give each claim one precise meaning. In particular, `TypedProg` should be described as residual program typing; `machineTyped_not_halted` should not receive a progress badge; finite scheduling fairness should retain its executable-prefix and fuel conditions. These corrections need prose and claim assignments, not additional API fields.

## Receipt and scope

Active draft snapshot: `gemini/semantics-v1.md`, sha256 `371ec83de053edbf55e56d4418f2afc049676bdf8a5e34b9f73d47430f90d00c`, filesystem modification time `2026-10-01T20:53:39-0500`, 41,910 bytes. This is an actively written draft, not a claimed completed deliverable. Findings identify text present in that snapshot or proposed additions for its next pass. The earlier drafts are historical comparison material.

Integration source inspected: `/Users/pooks/Dev/lean4-effect4`, HEAD `d7b9cb113d6014f9439fb846bb79713ca73294e9` (read with `git rev-parse HEAD`). Parent implementation worktree base `8c9be258`, head `9190c779` are brief-provided, not inspected here. All repository and Gemini files were read-only. Only this file and `evidence.json` were written in the allowed temporary review directory. No Lean, TypeScript, runtime, or trust-gate builds were run. Existing theorem statements and bodies were read; that is **reading** evidence in this review, not a fresh **proved** or **tested** result. The prose below is **proposed** documentation. No missing-proof conclusion is based on search alone.

Read the operating rules, documentation brief, implementation spec v3, citations audit, source index, and relevant portions of Gemini's existing drafts. Applied the repository domain-modeling skill to distinctions in vocabulary; the repository's ownership rules prohibit creating a competing glossary or decision register. A lightweight memory pass informed the instruction to respect frozen contracts; all mathematical content, names, and source locators below were verified from current local files.

Finishing criteria: at most five material corrections, each with code and primary-source evidence; replacement wording suitable for adoption; one additional section under 600 words; machine-readable evidence with input hashes and honest evidence classes. Completed by inspecting the retained output and validating the JSON.

## 1. Keep stored syntax, semantic continuations, membership, and WP distinct

**Where it matters now.** `semantics-v1.md:83` calls `RProgram` first-order program data; `:140–141` calls `Val → RProgram` an AST branch and labels the cut “No function continuations”; `:635` says all continuations in `Eff` and `RProgram` are first-order. These are the highest-priority corrections. The latest draft improves the older WP and global step-indexing claims; keep those improvements and sharpen the carrier distinction.

**Current code, reading.** `src/Effect4/Program/Eff.lean:277` stores `bind` as two `Eff` children. `src/Effect4/Laws/Program/Sched.lean:206` aliases `RProgram` to `Effects.Program RSig ExitV`; `.lake/packages/effects/Effects/Algebra/Program.lean:33–38` defines `vis` with a Lean function continuation `signature.Answer operation → Program signature A`. `Laws/Program/DenoteR.lean:69–72` constructs such a continuation with `fun`. This is a proof-side semantic carrier, not the stored first-order syntax. `src/Effect4/Laws/Program/Typed/Membership.lean:112–174` defines `Fits` by the finite `Ty` constructors; reference leaves consult declarations. `World.lean:137–142` defines an extension relation, not a well-founded order. `Residual.lean:266–306` defines an inductive residual judgment: ordinary operations require certificates, preconditions, and typed continuations for all permitted answers at later worlds. Its closing markers deliberately impose no continuation premise. `Assembly.lean:1075–1078` defines the exact source-to-residual claim `DenotesTyped`; `:1637` declares its obligation and `:1839` publishes a wanted marker. `Test/Program/TypedProgBindRed.lean:32–49` contains the explicit counterexample to unrestricted bind closure; its live register row is `E4-TYPED-CE-030` at `REGISTER.md:258`.

**Primary source, reading.** Xia et al., the vendored `2026-09-02-web-standards-sources/text/02-interaction-trees.txt:157–160,186–192`, explicitly represents an interaction-tree continuation by a meta-level function. Its tree is coinductive; our imported `Effects.Program` is inductive, so the connection is a technique/analogy with that distinction stated. Ahmed's vendored thesis, text `ahmed-2004-semantics-of-types-for-mutable-state.txt:1755–1781`, defines a unary world-indexed logical relation with a monotonicity requirement. `:2166–2209` explains the circularity arising when semantic types themselves depend on semantic store typings. De Vilhena–Pottier, text `de-vilhena-pottier-2021-separation-logic-for-effect-handlers.txt:588–636`, defines `ewp` using a chosen postcondition, protocol, operational transitions, and guarded recursion; `:1349–1364` distinguishes a weakest precondition without a bind rule from a context-local one with a bind rule. Therefore the local bind refutation is not by itself a refutation of every possible WP interpretation. An explicit comparison is needed.

**Replacement paragraph.**

> `Eff` is stored first-order syntax: its bind continuation is another program tree with positional inputs. `RProgram` is the proof-side semantic carrier `Effects.Program RSig ExitV`; its visible operation nodes carry Lean function continuations. These functions belong to the semantic model and are not stored function values in `Eff` or `Val`. `Fits` is the world-indexed membership judgment for values. `TypedProg` is the world-indexed typing judgment for residual programs: it specifies permitted operations and the continuations that must be typed for permitted replies. Its protocol clauses resemble effectful weakest-precondition specifications, but this documentation does not identify the judgments. Such an identification would require a named execution interpretation and a stated correspondence, including the closing markers. `DenotesTyped` is the separate claim connecting admitted source points to this residual judgment. The function-value exclusion in decisions row 163 removes an arrow clause from `Fits`; the present membership definition uses structural recursion over finite type syntax. This establishes how this relation is defined, without settling the proof technique for future recursive types or whole-program safety.

**Registry use.** Keep Ahmed as `proofTechnique` or `analogy` as justified for the particular claim; keep de Vilhena–Pottier as `analogy` until the specific adaptation is stated. Use the existing `.fundamentalProperty` role for the exact `DenotesTyped` claim, not an added WP role or a silently strengthened title.

## 2. A maintained invariant is not an existence-of-step theorem

**Where it matters now.** `semantics-v1.md:255–256` correctly says the invariant theorem is not progress. Retain that correction. Reword `:273–274`, which still introduces it as the way progress is stated. The paragraph below is a next-pass clarification, rather than a claim that the corrected sentence is wrong.

**Current code, reading.** `Assembly.lean:251–260` includes `MachineLive` inside `MachineTyped`. `:310–315` says that an explicitly halted machine cannot satisfy that invariant and proves it by projecting `typed.live.running`. It produces no successor. The declared preservation/reachability obligations at `:1843–1851` and the M7 wanted markers at `:1854–1857` are separate interfaces; this review does not infer their final imported-environment status from these lines.

**Primary source, reading.** PLF `sources/plf/Types.v:394–397` states progress as a value-or-successor disjunction and `:463–467` states preservation conditional on a transition. These statements occur in exercise files with `Admitted`, so this is a reading of the statements, not a source proof receipt. Harper's actual abbreviated-edition body, `pfpl-2nded-abbrev.txt:3180–3233`, supplies the same distinction and explains why the two properties work together.

**Replacement paragraph.**

> `machineTyped_not_halted` expresses a consequence of the maintained machine invariant: an explicitly halted machine cannot satisfy it. Progress would additionally classify a typed configuration as finished, able to take a permitted step, or at one of the live frontiers admitted by this machine's semantics. Preservation must show that each covered transition retains the required invariant. The generated claim table reports these obligations separately. A conditional route from preservation and reachability assumptions to no-halt safety does not discharge those assumptions and does not imply termination.

**Registry use.** Give the invariant projection its actual title. Do not use it as the witness of a progress claim whose intended statement requires a successor or a terminal/frontier classification. No new report field is required.

## 3. Put finite fairness in its own scheduling paragraph

**Where it matters now.** The reactive-scheduling section (`semantics-v1.md:232–287`) describes invariant lifting but does not yet state the actual fairness conditions; it is an active draft, so the proposed addition fills the next-pass gap. The concept-first rewrite gives `reactive-scheduling` a natural home for this information.

**Current code, reading.** `src/Effect4/Laws/Machine/Scheduling.lean:413–421` states `flush_fair`: a duplicate-free initial armed queue, `FlushReady` for its length, and a sufficient round bound imply actual callback entry for every initial owner. `:432–442` defines `FairTape` over executable prefixes and later decisions that really service an owner. The final prefix is included: a finite tape satisfying the definition cannot end with an executable armed owner still outstanding. These are exact quantifier/bound facts, not fresh execution tests.

**Primary source, reading.** Lynch–Vaandrager's vendored scan, printed p. 230, was rendered locally and visually inspected. Its right column explicitly distinguishes its trace-inclusion safety methods from liveness, which it does not treat. OCR text anchor: `lynch-vaandrager-1995-forward-and-backward-simulations.txt:1072–1083`. This prevents the bibliography's simulation reference from being used as a fairness proof.

**Ready-to-use addition.**

> The scheduling result is finite. `flush_fair` guarantees entry of every owner initially armed when the queue has no duplicates, the readiness condition holds, and the supplied rounds cover that queue. It does not promise that a callback finishes or that a host eventually supplies a decision. `FairTape` is a property of a particular finite tape: at every executable prefix, an armed owner must have a later decision that actually enters its callback. A tape ending with an outstanding executable armed owner therefore fails this condition. State invariance and interpreter agreement remain separate claims from this service guarantee.

**Registry use.** Attach the particular scheduling theorems to `reactive-scheduling`. Do not classify `FairTape`, a definition, as a proof. No new fairness API or whole-runtime claim is proposed.

## 4. Separate simulation, handler fulfillment, and denotational typing

**Where it matters now.** `semantics-v1.md:545–603` usefully distinguishes observed interpreter agreements and states fragment bounds. Retain those improvements. Add the small table below to prevent the older `lemma-census.md:202` combination of fundamental property and denotational adequacy, or `chapter-table.md:410` use of generic projection composition as adequacy, from reappearing in registry expansion. At `semantics-v1.md:582`, a literature reference to Lynch–Vaandrager should not describe the whole paper as lock-step: the local `Projects` interface is the particular one-step shape.

**Current code, reading.** `src/Effect4/Laws/Machine/Refinement.lean:20–37` relates two one-step implementations with matched answers and frontiers. `:99–120` derives such a relation from a projection, explicitly without initialization or a host implementation instance. `Typed/Adequacy.lean:50–68` instead requires a store handler to fulfill a protocol row and derives a typed continuation from that premise. `Assembly.lean:1075–1078` is the source-to-residual typing claim. `RuntimeR.lean:198–215` states agreement of outcomes and store/fiber observations between internal frame and reference replay, at default empty external table and oracle.

**Primary source, reading.** De Vilhena–Pottier, text `:849–855`, states its program-logic safety result with a closed expression, empty protocol, and empty initial heap. Its result is about one expression's execution. Lynch–Vaandrager p. 230 distinguishes trace inclusion and refinement and does not add liveness. Neither source licenses collapsing these local judgments into one unqualified adequacy badge.

**Ready-to-use table addition.**

| Claim | What it connects | What remains separately required |
| --- | --- | --- |
| `DenotesTyped` | An admitted source point and its residual program typing | The exact source premises and construct compatibility obligations |
| `StoreImplements` / `storeStep_typed` | A permitted store request and the handler's actual reply | Fulfillment for each operation and the enclosing machine transition |
| `Projects` / `Refines` | One implementation's operation and a model operation | An instance, initial relation, validity, and any progress obligations |
| `run_eq_ref` | Internal frame replay and reference replay, on outcomes and `obs` | External rows, oracle answers, host execution, and other backend connections |

**Registry use.** Keep these as separate claims even when they share modules or literature. Preserve decisions row 138's fragment restrictions in every M7 summary.

## 5. Apply textbook roles to this judgment, not to a word with the same name

**Where it matters now.** The current draft no longer repeats these two older substitutions (`lemma-census.md:32,51`), but its next-pass standard lemma lists should not reintroduce them. The applicability table below is an addition for that pass. The brief's standard role list should guide questions, not force each role into every concept.

**Current code, reading.** `src/Effect4/Store/Domain/Canonical.lean:33–46` gives a reader/writer retraction, exactness, and shape acceptance. It does not conclude that any value satisfying `Fits` has a particular constructor. `Typed/Membership.lean:112–174` supplies the membership cases from which appropriate inversion facts can be stated. `Typing/HasTy.lean:101–106` retains a positional binder and types its continuation under an appended result type. `Typing/Sound.lean:156–161` explicitly shifts the syntax when inserting an environment slot. `Membership.lean:1503–1525,2165–2174` provides positional value/type agreement and conditional term-evaluation membership. The no-function-value cut does not remove this environment reasoning.

**Primary source, reading.** PLF `Types.v:366–381` separates canonical forms for typed values from codec laws. `StlcProp.v:230–234` states substitution with a replaced variable and a typed replacement. The type of each assertion is enough to show that weakening and retraction are not interchangeable witnesses.

**Replacement table addition.**

| Textbook role | Applicability here | Suitable local evidence |
| --- | --- | --- |
| Canonical forms | Shapes of values satisfying the named typing/membership judgment | Membership inversion; a codec retraction is a different claim |
| Weakening | Environment insertion with the required shift of positional syntax | `hasTy_weaken`, with its actual `Eff.weaken` argument |
| Substitution | Lambda beta-substitution is excluded by row 163; positional bind/environment obligations remain | State their own environment-evaluation or construct-compatibility claim; do not rename weakening |
| Progress / preservation | Defined against a particular transition and permitted frontier policy | Separate transition and invariant claims |
| Antisymmetry | Only when the chosen comparison relation is intended to be an order | Its named equality or normalization observation; do not demand it of every judgment |

**Small current-record correction.** Spec v3 §5 lists decisions row 117 as open; `semantics-v1.md:149–151` has already adopted the closed-row reading. At inspected HEAD the actual row (`decisions.md:210`) includes the owner's closed-root-row ruling while retaining a separate per-position obligation. Reconcile prose with the live row rather than copying the old spec's status. This is a reading of the ruling, not a proof that the remaining obligation has closed.

## Ready-to-use documentation section (under 600 words)

### Reading the semantics claims

Each concept groups questions about one part of Effect4. A literature reference explains a definition, proof method, adaptation, analogy, or excluded feature; it does not transfer a book's theorem into this repository. The generated table gives the evidence for each local claim. The prose explains its meaning and scope.

**Value membership.** `Fits` describes when a stored value belongs to a type in a world. Its reference cases read the world's declarations, and its structural cases follow the finite type syntax. World extension and membership monotonicity are separate facts. The function-value cut removes an arrow clause from this membership relation. It does not settle how future recursive features or whole-program properties must be proved.

**Residual program typing.** Stored `Eff` continuations are program trees. The proof-side `RProgram` carrier instead has Lean function continuations at visible operations; it is not another stored syntax representation. `TypedProg` describes permitted operations and the continuations required for permitted replies at later worlds. Closing markers have dedicated clauses because they can leave without resuming their continuations. `DenotesTyped` connects admitted source points to this residual judgment; its status belongs in the generated table. The resemblance to protocol-based weakest preconditions is a literature connection. A claim that the two coincide needs a specified execution meaning and a stated correspondence.

**Execution safety.** A maintained invariant can exclude a halted configuration without proving that a successor exists. Progress asks which finished, stepping, or permitted frontier case applies. Preservation asks whether a transition retains the required invariant. A theorem assembling those premises into safety remains conditional on their evidence. None of these statements alone proves that execution terminates.

**Scheduling service.** `flush_fair` concerns actual callback entry for an initially armed, duplicate-free queue under readiness and sufficient bounds. `FairTape` requires a later servicing decision for each armed owner at every executable prefix; a finite tape cannot satisfy it while leaving such an owner outstanding at its end. Callback completion and eventual host decisions are additional questions.

**Connections between meanings.** Handler fulfillment says that an actual reply satisfies a protocol's postcondition. Simulation says how steps or observations of two named behaviors relate. Source-to-residual typing says that admission establishes a residual typing judgment. Keep these claims separate. In particular, internal frame/reference replay agreement uses the empty external table and oracle; an external host or another backend needs its own connection and assumptions.

The standard lemma roles are an applicability checklist. A reader/writer retraction is not a canonical-forms theorem for membership, and environment weakening is not substitution. Every retained role should name the judgment and exact local claim. An excluded feature explains why a particular textbook claim does not apply; it does not erase obligations for features that remain.

## Citation handling and adoption

The active draft repeats theorem signatures and hard-coded proof/status counts even though the brief puts their ownership in the generated report. Treat these as unfinished prose awaiting consolidation: retain named semantic explanations and link to the generated statements/statuses, rather than maintaining another status inventory. This is an editorial adoption note, not a new semantic API requirement.

Use the existing verified/corrected audit rows A8, A20–A25, H1–H9, P1, P8, C4, C10, C34–C38, F10–F11 for their stated coverage only. Several verify a title or contents heading, not the body of a theorem. The direct body readings used above are proposed additions to the citation audit, not new authoritative `LiteratureRef` locators until the coordinator admits them there:

- Ahmed: text lines 1755–1781 (definition of unary Kripke relations); 2166–2209 (semantic-store-type circularity).
- De Vilhena–Pottier: text lines 588–636 (effectful WP); 849–855 (safety statement); 1349–1364 (bind-rule distinction).
- PLF: `Types.v:366–381,394–397,463–467`; `StlcProp.v:230–234` (statements, not local Lean proofs).
- Lynch–Vaandrager: printed p. 230, PDF page 17, visually checked (scope excludes liveness).

Do not reuse the old ATTAPL chapter 8 label. The verified contents put Crary's logical-relations chapter at chapter 6; the full chapter body remains unavailable in this source set. The proposed additions above require no source download, no change to the report schema, and no change to a frozen semantic contract.
