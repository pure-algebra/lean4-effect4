# Second look at the language's authoring obligations

Status: research note (history, not authority). 2026-10-13. A second look at
`docs/research/2026-10-13-authoring-obligations/README.md`.

## 1. Each obligation checked

### O1, typed edits

The note states subject reduction for edits: `HasTy Γ p τ → op p = some p' → HasTy Γ p' τ`.
This shape is right for semantic refactorings.
Decisions row 336 (10) orders the graph operations in stage V4.
No graph operation is built yet.
The ground is a program in the store and `rebaseRefs` (seat ORG's L9).
The note is imprecise about the tree's current state.
The function `rebaseRefs` does not exist in `src/Effect4/Program/Refs.lean`.
`docs/research/2026-10-08-seat-ORG-theory-map.md` records L9 as needing a definition.
The store cannot yet key a program by content address.
No `Content (Eff NativeOp)` instance exists in `src/Effect4/Store/Domain/Node.lean`.

### O2, checking at a real application

The note states that checking runs at the empty application.
It states that the check refuses a layer reference that program admission accepts.
Decisions row 373 (7) rules the route: check the expansion, and read its table at source addresses.
The statement and the ruled route are right.
The note is imprecise about where the empty application is fixed.
The data structure `EditSession` (`src/Effect4/Program/Edit.lean`) takes any `SigApp`.
The CLI tool `Tools.Session` (`tools/Tools/Session.lean`) hardcodes the application to `"empty"`.
Both fail on layer references.
`Checker.checkLayer` (`src/Effect4/Program/Checker.lean`) refuses `.ref` with `layerReference`.
`Annotate.checkLayer` (`src/Effect4/Program/Typing/Annotate.lean`) carries the same refusal.
Program admission expands layer references with `expandRefs` (`src/Effect4/Program/Typing.lean`).

### O3, meaning covers the authoring language

The note states that `denoteRows` folds a program into a call tree over `RowsSig table`.
This matches `denoteRows` in `src/Effect4/Laws/Program/DenoteRows.lean`.
The signature is `Effects.Signature.sum StoreSig (RowSig table)`.
The note lists three missing parts: definition blocks, program parameters, and multiple fibers.
This classification is right.
`denoteRows` covers only the fragment `StraightRows`.
The probe in `docs/research/2026-10-13-proc5-probe/README.md` tests `mrecB` on three sample programs.
Goal G5 of slice PROC-5 remains open.
Decisions row 340 rules program parameters (`.invoke`, `.param`), which remain outside the denotation.
The frame machine in `src/Effect4/Machine/Fibers.lean` covers fibers and scopes, which the call tree omits.

### O4, composition laws

The note lists inlining, module agreement, SynchronizedRef, and machine-denotation agreement.
The statement is right, but the status description needs precision.
Step agreement laws are proved for six modules:
- `latch_steps_agree` (`src/Effect4/Laws/Library/Latch/Steps.lean`);
- `pool_steps_agree` (`src/Effect4/Laws/Library/Pool/Steps.lean`);
- `single_steps_agree` (`src/Effect4/Laws/Library/PubSub/Steps.lean`);
- `queue_steps_agree` (`src/Effect4/Laws/Library/Queue/Steps.lean`);
- `ref_steps_agree` (`src/Effect4/Laws/Library/Ref/Operations.lean`);
- `semaphore_steps_agree` (`src/Effect4/Laws/Library/Semaphore/Steps.lean`).
The whole module law `Agrees profile module expansion` remains open (R10, row 79, DI-89).
The inlining law (goal G7, slice PROC-6) is unstated in code.
The SynchronizedRef composition law (goal G10) is unstated in code.
The agreement of the frame machine with definition blocks (goal G4) is unstated in code.

### O5, safety at the authoring language's reach

The note states that `m7_proved` holds on `M7Fragment` modulo one planned goal, `countdown_parks_positional`.
Here the note is wrong.
`m7_proved` (`src/Effect4/Laws/Program/Typed/Commands/Clauses/All.lean`) is a fully proved theorem.
`m7_proved` rests on no planned goal.
`m7_admitted` (`src/Effect4/Laws/Program/Typed/AdmittedSource.lean`) is also a proved theorem.
`ev.countdown_parks` closes the countdown clauses in `src/Effect4/Laws/Program/Typed/Commands/Clauses/Park.lean`.
`docs/core/system-map.md` section 10.1 confirms that M7 rests on no goal.
The coordinator copied stale text from section 8 of `docs/core/system-map.md`.
Widening safety now means extending `loadsTyped` and `reachable_typed` to host rows and blocks.

### O6, application and claim records

The note states the weakest-precondition judgment `Typed o Ψ w Q t`.
This matches `Typed` in `src/Effect4/Laws/Effects/Protocol.lean`.
`Typed` composes along `bind` (`Typed.bind`).
The note states that slices 1 to 5 needed no call tree and that none is built.
This is true of HEAD.
Seat CLAIMS is running now (`docs/research/2026-10-13-seat-claims-brief.md`).
Seat CLAIMS builds `src/Effect4/Program/Authoring/Application.lean` and the claim records.

### O7, typed and checked replies

The note states that `Live` landed today with `view_funded` and `view_classifies`.
This is true of the tree.
`Live` is defined in `src/Effect4/Run/Live.lean`.
`view_funded` and `view_classifies` are proved in `src/Effect4/Laws/Api/Live.lean`.
The note states that `Typed.replay` replays raw decisions today.
This is true in `src/Effect4/Api.lean`.
Seat REPLAY is running now (`docs/research/2026-10-13-seat-replay-brief.md`).
Seat REPLAY implements `Typed.replay` through `Live.feed` and proves `replay-at-call-instance`.

### O8, what a release claims of shipped code

The note states that row 28 waits on the owner's meaning of verified lowering.
The note states that the deep dive recommends theorem-carrying Lean definitions and rule coverage.
Here the note is outdated.
The owner ruled this recommendation in decisions row 373 (4) on 2026-10-13 afternoon.
For the share, Lean definitions carry theorems, and the LCNF route carries rule coverage.
The long-term target remains a proved stage law for LCNF lowering.

## 2. What is missing

### Missing obligation 1: Hole filling after reply (`fill-by-term`)

An agent runs a sketch until a hole frontier, receives an answer, and fills the hole.
Decisions row 373 (6) rules this operation.
It owes an equal-observation law: the filled run equals the run that received the answer.
The judgment is a simulation relation (K3).
This serves requirement R14 (sketches and holes) and R13 (replay from data).

### Missing obligation 2: Content-addressable program store

Decisions row 336 (7) rules that subtrees are stored by content address at every depth.
An agent needs content addressing to find and reuse written definitions and blocks.
No `Content (Eff NativeOp)` instance exists today in `src/Effect4/Store/Domain/Node.lean`.
This obligation owes an exact embedding (K2) between `Eff` and store digests.
It serves requirement R3 (data plane) and R13 (inputs are data).

### Missing split: Split O1 into rebasing and semantic refactoring

O1 bundles syntactic reference rebasing with semantic graph edits.
These two operations owe different mathematical judgments:
- Syntactic rebasing (`rebaseRefs`) keeps reference formation `layerRefsWF` (seat ORG's L9).
  It is a located refusal or total map (K4) serving requirement R14.
- Semantic refactorings (extract and inline) alter program control flow.
  They owe subject reduction (`HasTy`) and contextual equivalence (`denote`).
  They form a simulation relation (K3) serving requirement R14 and R8.
Splitting them keeps syntax manipulation separate from semantic preservation.

### Missing split: Split O4 into module contracts and multi-fiber adequacy

O4 bundles module composition with operational adequacy.
These address two different boundaries:
- Module composition (SynchronizedRef from Ref and Semaphore, G10) preserves behavioral contracts.
  It is an algebraic composition law serving requirement R10.
- Machine adequacy proves that the frame machine simulates the call tree for concurrent programs.
  It is a simulation theorem (K3) over forks and scopes, serving requirement R6 and R8.

### Missing obligation 3: Parameter typing and substitution (HO-4, HO-5)

Decisions row 340 rules program parameters (`.invoke`, `.param`).
An agent authoring reusable combinators needs formal rules for program parameters.
This owes a typing rule for `.param` and a beta-reduction substitution lemma for `.invoke`.
It is a compatibility lemma and subject reduction step serving requirement R4 and R10.

## 3. Reuse

### O1, typed edits

Reuse `Node.replaceAt` and `Node.setChild` from `src/Effect4/Program/Refs.lean`.
Reuse `Table.splice` (`src/Effect4/Program/Typing/Splice.lean`) for incremental table updates.
Reuse `NodeHasTy.replace` (`src/Effect4/Laws/Program/Typing/Replace.lean`).
Do not build ad-hoc tree rewriting passes.

### O2, checking at a real application

Reuse `expandRefs` and `expanded_refs_nil_of_wf` from `src/Effect4/Laws/Program/ReferenceExpansion.lean`.
Row 373 (7) rules that `LayerHasTy` gains no reference rule.
Reuse `EditSession` (`src/Effect4/Program/Edit.lean`) with `SigApp`.
Do not duplicate reference resolution inside the sketch checker.

### O3, meaning covers the authoring language

Reuse the convergence laws of loops from `src/Effect4/Laws/Program/IterLimit.lean`.
The definitions of `Conv`, `conv_fixpoint`, and `conv_unique` provide the model for `ConvB`.
Parameterize `denoteDefs` over a definition block.
Make `denoteRows` the special case where the block is empty.
Do not duplicate the fifteen arms of `denoteRows`.

### O4, composition laws

Reuse the step language (`src/Effect4/Step.lean`, `src/Effect4/Laws/Step.lean`).
The step language already unifies step proofs for Semaphore, Pool, Queue, and Latch.
Reuse `Step.sound` and `Step.frame`.
Reuse the simulation framework `ReplayRel` and `BookMeans` (`src/Effect4/Laws/Machine/Book.lean`).

### O5, safety at the authoring language's reach

Reuse the route theorem `m7_of_ledger` (`src/Effect4/Laws/Program/Typed/Assembly.lean`).
`m7_of_ledger` derives M7 directly from M5 (`loadsTyped`) and M6 (`decision_preserves`).
Reuse `reachable_typed` in `src/Effect4/Laws/Program/Typed/Commands/Clauses/All.lean`.
Do not re-prove the eighteen command clauses when widening the fragment.

### O6, application and claim records

Reuse `#plan_status` from `tools/ProofGraph/Plan.lean` to read claim status dynamically.
Do not store claim statuses in static record fields.
Reuse `Typed` from `src/Effect4/Laws/Effects/Protocol.lean`.
Decisions row 375 clears the goal gate: do not create an application gate.

### O7, typed and checked replies

Reuse `Live.feed` (`src/Effect4/Run/Live.lean`) folded over the journal.
Do not build a second replay loop.
Reuse `instance_prepared_success` and `preflight_success_prepared_fits` (`src/Effect4/Laws/Program/Admit.lean`).
Reuse `acceptAtInstance` and `admitInstance` from `src/Effect4/Program/Admit.lean`.

### O8, lowering simulation

Reuse `read_print` (`src/Effect4/Laws/Codegen/ReadPrint.lean`) on the readable domain.
Reuse `read_exact` (`src/Effect4/Laws/Codegen/Read.lean`).
Reuse tsgo 7 test suites for differential testing across the target profile.

## 4. Parallel work

### Currently active tasks

Three tasks run now across distinct worktrees:
1. PROC-5 (coordinator):
   Touches `src/Effect4/Laws/Program/DenoteDefs.lean` and fragment definitions.
2. Seat CLAIMS (`docs/research/2026-10-13-seat-claims-brief.md`):
   Touches `src/Effect4/Program/Authoring/**` and `Test/**`.
3. Seat REPLAY (`docs/research/2026-10-13-seat-replay-brief.md`):
   Touches `src/Effect4/Api.lean`, `src/Effect4/Run/**`, and `src/Effect4/Laws/Api/**`.

These three tasks touch disjoint files and do not collide.

### Next two tasks to start

1. **Task A: O2 (checking at a real application).**
   Touches `src/Effect4/Program/Typing/Annotate.lean` and `tools/Tools/Session.lean`.
   It expands layer references during sketch annotation per row 373 (7).
   It allows `Tools.Session` to accept a non-empty `SigApp`.
   It collides with none of the three running tasks.
2. **Task B: O1 foundation (seat ORG's address algebra).**
   Touches `src/Effect4/Program/Refs.lean` and `src/Effect4/Laws/Program/References.lean`.
   It consolidates pure address lemmas and defines `rebaseRefs` (seat ORG's L9).
   It collides with none of the three running tasks.

### Sequencing dependencies

- PROC-6 (inlining law, G7) must wait for PROC-5's block denotation.
- HO-4 and HO-5 (program parameters) must wait for PROC-5.
- Module composition laws (G10 SynchronizedRef) must wait for PROC-5 and PROC-6.
- Fragment widening for safety (O5) must wait for PROC-5.

## 5. The mathematics

### Initial algebra

Literature marks: Goguen, Thatcher, Wagner, and Wright 1977 (audit C14); Meijer, Fokkinga, and Paterson 1991 (audit P24).
Meijer et al. 1991 is vendored under `docs/research/2026-10-01-semantics/sources/meijer-fokkinga-paterson-1991-bananas-lenses.pdf` (read).
Goguen et al. 1977 is not vendored (cited by name).

### Free monad and handlers

Literature marks: Plotkin and Pretnar 2009 (audit P29); Swierstra 2008 (audit P34).
Plotkin and Pretnar 2009 is vendored under `docs/research/2026-10-01-semantics/sources/plotkin-pretnar-2009-handlers-of-algebraic-effects.pdf` (read).
Swierstra 2008 is vendored under `docs/research/2026-09-02-web-standards-sources/papers/06-data-types-a-la-carte.pdf` (read).

### Recursive handlers

Literature marks: Xia et al. 2020 (`mrec`, audit P37).
Xia et al. 2020 is vendored under `docs/research/2026-09-02-web-standards-sources/papers/02-interaction-trees.pdf` (read).
The budget cut `mrecB` is tested in `docs/research/2026-10-13-proc5-probe/README.md`.

### Weakest preconditions

Literature marks: Dijkstra monads.
No Dijkstra monad text is vendored in `docs/research/2026-10-01-semantics/sources/`.
`docs/research/2026-10-07-packet-application-claims.md` section 3.4 marks the Dijkstra monad recalled, not read.
`docs/DESIGN-BASIS.md` marks the logic edge pending.

### Graduality

Literature marks: Carroll, Madhavapeddy, and Omar 2026 (*Gradual Type Slicing*); Omar et al. (*Hazelnut*).
Both papers are read in research notes:
- Carroll et al. 2026 in `docs/research/2026-10-06-seat-LATTICE-receipt.md`.
- Omar et al. in `docs/research/2026-10-06-seat-GAP-study.md`.

### Higher-order effects

Literature marks: Bach Poulsen and van der Rest 2023 (*Hefty Algebras*, corpus 14).
`docs/DESIGN-BASIS.md` marks Bach Poulsen and van der Rest 2023 read in lit-papers Q2.

### Simulation

Literature marks: Lynch and Vaandrager 1995 (audit C4); Leroy 2009 (audit C10); Plotkin 1977 (audit C23).
Lynch and Vaandrager 1995 is vendored under `docs/research/2026-10-01-semantics/sources/lynch-vaandrager-1995-forward-and-backward-simulations.pdf` (read).
Leroy 2009 is vendored under `docs/research/2026-10-01-semantics/sources/leroy-2009-formal-verification-of-a-realistic-compiler.pdf` (read).
Plotkin 1977 is not vendored (cited by name).

## 6. Questions for the owner

1. Should the address algebra laws land in a shared module before building graph edit operations?
   Recommendation: yes, land them in `src/Effect4/Program/Address.lean` so graph operations build on proved path laws.

2. Should `Tools.Session` accept an arbitrary `SigApp` and expand layer references during sketch checking per row 373 (7)?
   Recommendation: yes, update `Tools.Session` now to unblock authoring of real programs with host rows and services.

3. Should graph refactorings like extract and inline be split from syntactic reference rebasing?
   Recommendation: yes, keep syntactic tree rewrites separate from semantic refactorings that owe simulation proofs.

4. Should the release lowering claim ruled in row 373 (4) be entered as a planned goal in the semantics registry now?
   Recommendation: yes, record it under concept `translation-simulation` so lowering progress is tracked by `#plan_status`.

5. Should definition recursion in PROC-5 share the convergence laws of loops in `src/Effect4/Laws/Program/IterLimit.lean`?
   Recommendation: yes, reuse `Conv` and convergence uniqueness so loops and definition blocks share one recursion theory.
