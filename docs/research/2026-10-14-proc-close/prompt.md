# Codex: close out the procedures line (the locked brief)

**Paused, 2026-10-14 evening (decisions row 387).** The owner paused this brief before any of it ran. Its findings stay as the reference for when the general theory resumes: §8 of `modelling-check.md` and `codex-review.md`, with their probes. The next work is the vertical slice (`docs/research/2026-10-14-faces/prompt.md`).

## The one thing to know first

The plan is locked (decisions row 386). Three reviews shaped it: Gemini's two (`gemini-review.md`,
`gemini-math-review.md`) and your own (`codex-review.md`). The coordinator checked each
(`review-notes.md`). Your review's amendments are now the plan's statements. The probes it left
are the starting points: `probes/CodexRelations.lean`, `CodexInline.lean`, `CodexObjects.lean`
and `CodexClosure.lean`.

Track 1 lands now, five slices:
- L0: the `effects` package's simulation, relational in results, operations and states;
- L3: parameter substitution, its typing and the meaning's weakening law;
- L1: the one order on the meaning and its lift law;
- L2: the inlining law G7;
- L4: the definitions connectors.

Track 2 designs the syntax changes and the generic object as one note. Then it stops for review
before any edit to `Eff`, `Ty`, `Store.Val` or `Point`. The line ends at the proof closure
(`modelling-check.md` §7, amended in §8): every slice is a node of it.

**The owner's rule for every choice (2026-10-14):** decide on semantics, never on rebuild cost,
and take the complete option. Every item is wanted and its users are known. If a statement falls
short of its users, the plan widens. Never drop or defer an item; report the gap and the step
that closes it.

## What the line owes

| Item | What it is | Its users |
| --- | --- | --- |
| L0 | the `effects` simulation, relational in results, operations and states, with normalized cuts (row 386 (2)) | L1; every simulation after it |
| L1 `meaning-refines` | inclusion of completed observations, its block pullback, the lift law in the call handler (row 386 (1), (3), (4)) | G7; every module claim; G10 |
| L3 `inline-types` | substitution, its checker law, subtype-aware replacement, the meaning's weakening (row 386 (5)) | G7's program and its typing |
| L2 `inline-agrees` | an invocation or call and its inlining are equivalent in every context (row 383 (2)) | the to-do's cached service now; the connectors |
| L4 `definitions-agree` | ranked expansion and recursive unfolding (row 386 (6)) | every module built from definitions; the Queue's and Semaphore's instances |
| D1 | PROC-7 (generic definitions, G8 `check_subst`) and HO-5 (methods with program parameters) | the module form |
| D2 | closures held as data, one activation stack, capture conversion: SCOPE-1's stage 0 (rows 383 (5), 385 (5)) | services; the module form; substitution into layer bodies |
| D3 | the generic object, its obligations and the checked bank constructor (row 386 (7) to (11)) | every bank entry; K1 |

CX4 is proved already (`call_arm`, `invoke_arm` and `param_arm` with `hop_typed`,
`src/Effect4/Laws/Program/Typed/Denotation.lean`). Record its placement in the receipt.

## Read first

- `AGENTS.md`, all of it.
- `docs/research/2026-10-14-proc-close/modelling-check.md`, with its §8 amendments.
- Your own `codex-review.md` and its probes; `review-notes.md`.
- Decisions rows 82, 259, 328, 331, 340, 361, 379 and 381 to 386.
- The PROC design (`docs/research/2026-10-08-seat-PROC-design.md`): §4.4, §8 and §9.
- `docs/research/2026-10-09-program-parameters.md` (HO-4, HO-5) and
  `docs/research/2026-10-10-cx-lexical-scope.md` (§3.4, §8, §9).
- `docs/research/2026-10-14-one-fiber-scout.md` and `docs/research/2026-10-14-many-fibers-scout.md`.

## Where you work

- Effect4: your worktree, `/Users/pooks/Dev/lean4-effect4-codex`, on the branch the launch
  message names, at the coordinator's head.
- L0 only: `/Users/pooks/Dev/lean4-effects`, on a new branch `codex/relational-simulation` from
  its pin `bf5ab8f` (v0.10.1). Read its own rules first.

## The rules that bind every slice

PROC-6's brief holds them: `docs/research/2026-10-14-proc6-prep/landing-prompt.md`, "The rules
that bind every slice". In short:
- build only through `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`;
- place before you prove;
- `#axiom_audit` each slice, at `[propext, Quot.sound]`;
- in the law graph, `aesop` and `simp only`, with no `simp_all`, `first` or `try`;
- every new traversal of `Eff` is a fold (an `EffAlgebra` and `cata_eff`), never a hand `match`;
- reuse before you add: name the existing declaration each new one could have been;
- commit by named paths;
- never push, download nothing, and never write `2>/dev/null`;
- `lakefile.toml` and `docs/core/decisions.md` are the coordinator's;
- append to the root imports.

## Track 1: land now

The order: L0, then L3 while the coordinator releases L0, then L1, L2 and L4.

### Slice L0: the relational simulation (the `effects` package)

- One lifting relates results, operations and states (row 386 (2)). Two finished steps relate
  when their results relate. Two calls relate when their operations relate under the related
  states; related answers lead to related continuations. The result types may differ.
- `IsSim`, `IsBisim`, the run theorems, the compositions and the unfolding theorem take the
  relational lifting.
  - A run theorem concludes an existentially related result (your `RunSoundContract`,
    `RunBisimContract`).
  - Composition composes the result, operation and state relations (`SimCompositionContract`,
    `Lift.comp`). Show it composes worlds: a state relation that grows by allocation.
- Today's names are the equality instances, with `lift_eq_iff`, `isSim_eq_iff` and
  `isBisim_eq_iff`. `unfold_approx_of_sim` and `run_eq_of_bisim` stay, as equality corollaries.
  Adjust the package's own proofs that build or eliminate `Lift.done`.
- Normalize a peeled budget cut to a system cut (`completedPeel`), so the system's own cut is
  the bottom. Land no bottom-aware second lifting.
- Prove that the peeled system's completed runs are the program's, for every host.
- Stop after this slice's commit in the `effects` repository, and report. Releasing it and
  bumping the pin are the coordinator's, after the owner's push.

### Slice L3: substitution, its typing and weakening

L2 uses all of it, so it lands before L2, and it needs no part of L0.

- `Eff.substParams` and the inlined forms (`inlineInvoke`, and the call's): your `substAlg`
  fold, in a new core module `src/Effect4/Program/Inline.lean`. It reads the generated binder
  levels (`Node.childLevel`) and uses `Eff.weaken` for every shift. An inserted argument keeps its
  caller's parameter frame and is not substituted again.
- `check_substParams` over `BodyRows`, with every premise of your
  `CheckSubstParamsObligation`: declaration formation, argument count, body checking,
  declaration admission, argument checking and requirement containment.
- **The subtype-aware replacement theorem.** Replacing a subterm by one whose answer and error
  are narrower, and whose requirements are contained, keeps the program typed. State the
  enclosing inferred type and the typing table (`check_replace` and `table_splice` need one equal
  type). Your `wideDecl` control is its first reader.
- `denoteBlockB_weaken`, your `DenoteWeakenObligation` equation.
- That substitution keeps `BodyRows`.
- Its domain: immediate `BodyRows` bodies. Substitution into a closed layer body waits for D2's
  capture conversion (your `captureBody` control); record that as the claim's open part.
- Claim `inline-types`, role preservation, beside `check_replace` under `initial-algebras-folds`
  (R14).

### Slice L1: the order on the meaning

- `ObsRefines`, the primary order (row 386 (1)): inclusion of completed observations (exit,
  stores, host state). It ranges over related initial states and admitted host pairs. The right
  budget is chosen after the host and the completed run are fixed. `exactHosts` gives the
  same-host instance.
- `RefinesB`, its pullback through `denoteBlockB`. It exposes both body tables, related contexts
  and environments, and a relation on parameter frames. `EquivB` is both directions.
- The uniform limit of `Effects.Program.Approx` is a sufficient certificate:
  `limit_sound_for_completed_observations`. It is not the same order; keep your controls.
- **The lift law** (your `HandlerLiftContract`): call handlers related by L0's simulation give
  related observations for every client that keeps the frame.
  - Define the client-frame and compatibility predicates by the admitted constructors, and
    prove their preservation. They cover terms, branches, dynamic contexts, returned values and
    captured program parameters.
  - A module's operation restores the abstraction at success and at failure. An unanswered
    host call is a frontier.
- The frame conditions:
  - `FrameCondition`, primitive answers and states, with `identity_frame` proved now;
  - `NominalFrameCondition` for modules: renamed handle arguments, and the name relation
    extended at allocation. Ownership excludes reads and indirect access to private cells. It
    follows nested values, captures and calls through the interface.
- `HostRespects` (row 386 (3)): a module claim holds for hosts that respect names. Your
  `allocation_changes_host_answer` is its control.
- Claim `meaning-refines`, role simulation, concept `translation-simulation`, R10: row 382 (3)'s
  first step.

### Slice L2: the inlining law G7

- The step laws: the call's and the invocation's two-sided sandwich (`UniversalInvokeSandwich`
  and its call form). Use L3's substitution and weakening.
- Then `sandwich_implies_limit_equivalence`, L1's certificate, and the lift law at the identity
  frame: `inline_agrees`, an `EquivB` in every context on `BlockRows`.
- On `BlockRows`, both programs reach the machine by `h9_blocks`, under its own premises. CX3
  admits the inlined program; it adds no premise to H9.
- Its first user now: the to-do's cached service (`Test/Dogfood/Scenario/Todo/Cached.lean`,
  `src/Effect4/Laws/Library/Ref/Cache.lean`).
- Keep your finite controls: nested forwarding, caller parameter frames, captured values under
  nested binders, Gemini's unequal-budget example.
- Claim `inline-agrees`, role simulation, concept `translation-simulation`, R10.

### Slice L4: the definitions connectors

- **Ranked blocks.** A decreasing rank on the definition dependencies (`callsIn`, a fold that
  counts calls inside program arguments). Total expansion on the ranked domain, with a located
  refusal outside it. The theorem gives the expansion, shows that no definition call remains,
  and relates the client over the definitions to the client over the expansion.
- **Recursive blocks** (`eff_module`'s `using self`): finite unfolding and limit agreement, with
  no call-free expansion claimed. Your `Recursive` control is its first reader.
- Register `definitions-agree` (R10) with both theorems. Register `queue-definitions-agree` and
  `semaphore-definitions-agree` as its instances. Each also needs the theorem that the module's
  definitions expand to its named `Ops` (builders, requests, captures, wrappers).
- The instances' waiting operations complete in CONC-1; the scouts carry those steps.

Each slice ends with its narrow build, its `#axiom_audit`, its commits and its receipt section.
L3 adds a core module that nothing in the `Effect4` root imports until a user does. No behaviour
gate is reached, since no compile or machine definition changes.

## Track 2: design, then stop

Write one design note, `docs/research/2026-10-14-proc-close/design.md`, in PROC-6's scout form.
Give its rulings, stages, placements of the planned goals, fan-out, gates and open checks.

- **D1, PROC-7 and HO-5.** Generic definitions: the PROC design §9's slice, with G8 `check_subst`
  and `sub_subst` under `subtyping-algebra` and `initial-algebras-folds`. Its reach is the closed
  instances of formed templates (`Bounds.TemplateOK`) and a host call's instance in a generic body
  (row 323). HO-5: methods with program parameters (`withPermits`, `withPermitsIfAvailable`,
  Pool's `use`), as the program-parameters plan sets it out.
- **D2, the closure stage: SCOPE-1's stage 0.**
  - Closures held as data (row 381 (3)): a code reference and captured values, a program path
    now and a content digest with content addressing. They stay first-order, so the renaming
    argument extends; show it.
  - Closures are opaque: no projection of captures, no equality, no codec, and the printer writes
    the type only.
  - One activation stack: show that `Point.params` and `Point.call` move together, then merge
    them into one stack of frames.
  - Capture conversion, so substitution and inlining reach closed layer bodies.
  - One capture representation: migrate `ArgSite`, `Capture` and `Point`'s capture fields with
    their connector, and keep no duplicate stored environment.
  - Settle each item row 82 lists:
    - typed entry resolution;
    - lexical captures against a captured service context;
    - lifetime and portability ("a digest alone is not proof of code identity");
    - recursive admission;
    - the printer and reader contract;
    - the `Val`, `Ty` and `Eff` forms.
  - Choose between the PROC design's V1 and V2 on semantics. A bank entry's code must be
    reachable by its digest, which a dispatch over one program's definitions cannot name. G9 is
    `resolve_typed`, R7's top node.
- **D3, the generic object and the bank interface** (row 386 (7) to (11)).
  - One `ObjectSpec`, phase-indexed, with relational steps (your `CodexObjects.lean`).
  - One agreement package, with separate fields: atomic term agreement, invariant preservation,
    the delivery protocol, the frame and progress.
  - Three strategies: attempt only (Ref), the two Deferred wrappers (Queue, Semaphore, Pool) and
    batching (Latch, with `latch_registration_agrees`). An adapter for each of the five modules;
    the existing `StepsAgree` theorems stay as compatibility readers.
  - The request protocol for the wrappers: pending requests, committed answers, stale hints,
    posted helpers and withdrawals. Cover cancellation against commit, and completion at most
    once. Reduction applies only where disjointness is proved. Add `protectedBy`'s masked-region
    law.
  - Progress: a fair-execution definition, connected to `FairTape`. State `RequestProgress` and
    `SystemProgress` per object over every admitted fair execution, with the environment
    premises named (host answers, funding, enabling, cancellation). The Queue's and Semaphore's
    rows of your Q7 table are the first instances.
  - Prefix observations: the maintained relation at funded prefixes and at rest, reusing
    `RowsEnd`, `runRowsO` and `observeRows`, and `H9Fibers` stated on prefixes.
  - The checked bank constructor: it recomputes the digest, resolves and types the theorem, and
    derives `assumes` from its premises. The author's proofs are predicates fixed by the entry's
    data (your `AuthorProofs`), never free propositions.
  - The module form's inputs: what D1, D2 and this give the module form (rows 331 (6), 382 (2)).
    Do not design the module form itself.
- **Stop after the design note** and report. The coordinator reviews it before D1, D2 or D3
  touches source.

## Stop and report at once when

- a goal is false as stated: give the counterexample;
- a track 1 proof needs an edit to a compile, a machine or a syntax definition;
- a gate fails beyond its baseline.

## What you report

The receipt is `docs/research/2026-10-14-proc-close/receipt.md`. It opens with the one thing the
coordinator must know before merging. Then, per slice:
- the base and head commits;
- the files;
- the commands and their results;
- the `#axiom_audit` output;
- each goal's status;
- the open obligations;
- whether any evidence is bounded or host-only;
- any place the plan is wrong, with evidence.

Propose decisions rows in the receipt, never in the register.
