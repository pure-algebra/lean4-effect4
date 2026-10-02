# Kripke semantics and the Effect4 proof architecture

Effect4 already uses a meaningful Kripke construction: facts about values and suspended computations survive specified extensions of the world. It deserves focused investigation because those extensions connect allocation, stored values, continuations and machine preservation. The highest-value work is to check those connections against actual transitions. This research found no reason to replace them with a general modal-logic framework.

Reviewed implementation: `codex/metaprogramming` at `26c7be34e6fea61fe2d13c4fa80d9bcd80d414d5`. This is a research snapshot, not a status claim about Claude's or Gemini's moving branches. Two GPT-6.1 Sol reviews cover the [code architecture](architecture-review.md) and [primary literature](literature-review.md). The isolated [Lean probe](KripkeProbe.lean) passed; its fifteen printed declarations remain within `[propext, Quot.sound]`. The [receipt](receipt.md) distinguishes freshly checked proofs, source inspection and proposed follow-up work.

## What “Kripke” means here

In modal semantics, a proposition is necessary at a world when it holds at every accessible world. The choice of accessibility matters. Here it is compatible extension of allocations, typing declarations and other stated information. It is not the machine's execution relation. A “future world” need not be a reachable state or an eventual state. Reflexivity and transitivity support ordinary box reasoning, but establish no termination, scheduling fairness or progress result. [Kripke 1963, §2, p. 68](https://www.filosoficas.unam.mx/~morado/Cursos/17Modal/Kripke1963I.pdf).

The phrase **unary Kripke logical predicate** fits `Fits`: it interprets a value at a type and world, with a theorem transporting membership along the world order. Ahmed explicitly defines unary Kripke relations with this persistence requirement. An arrow clause is not required for the terminology. Effect4's predicate is still different from a binary logical relation establishing contextual equivalence between programs. [Ahmed 2004, §2.2.5, pp. 33–35](https://www.ccs.neu.edu/home/amal/ahmedsthesis.pdf).

| Project construction | Exact role | Important limit |
| --- | --- | --- |
| `World` and `leHost` | Worlds contain allocations, declaration tables, stored values and fixed service types. Extension preserves old information, compatible cells and external-name spellings. | The relation does not require a valid destination machine state. |
| `Fits` and `fits_mono` | The same value keeps its type in an extended world. | Membership does not certify the entire store or prove that the value was produced by execution. |
| `TypedProg` and `typedProg_mono` | A request meets its present precondition; its continuation accepts each permitted answer in each permitted future world. | A handler still has to produce an answer satisfying that postcondition. |
| `FrameAccepts`, `StackAccepts`, `SavedOk` | Suspended work retains its contract as the world grows. | Shared intermediate types and appropriate declaredness premises must be preserved. |
| `WorldValid`, `MachineTyped`, `ConfigTyped` | These relate declarations, current code, stores, queues and machine support. | They are not automatically upward closed. Actual transitions must establish their new instances. |
| `StoreImplements`, `StepPreserves` | These connect a real operation or transition to its resulting world and maintained invariant. | They require their own proofs; transport alone does not discharge them. |

Code anchors: [world/order](/Users/pooks/.codex/worktrees/metaprogramming-audit/lean4-effect4/src/Effect4/Laws/Program/Typed/World.lean:52), [validity/host order](/Users/pooks/.codex/worktrees/metaprogramming-audit/lean4-effect4/src/Effect4/Laws/Program/Typed/Validity.lean:19), [membership](/Users/pooks/.codex/worktrees/metaprogramming-audit/lean4-effect4/src/Effect4/Laws/Program/Typed/Membership.lean:112), [residual typing](/Users/pooks/.codex/worktrees/metaprogramming-audit/lean4-effect4/src/Effect4/Laws/Program/Typed/Residual.lean:266), [stack contracts](/Users/pooks/.codex/worktrees/metaprogramming-audit/lean4-effect4/src/Effect4/Laws/Program/Typed/Contracts.lean:43), [handler fulfillment](/Users/pooks/.codex/worktrees/metaprogramming-audit/lean4-effect4/src/Effect4/Laws/Program/Typed/Adequacy.lean:51), [step preservation](/Users/pooks/.codex/worktrees/metaprogramming-audit/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean:444).

## Four boundaries checked in Lean

The probe introduces research-only notation:

```lean
Future P w := ∀ w', w.leHost w' → P w'
```

**1. The expected modal laws hold.** Reflexivity supplies `Future P w → P w`; transitivity supplies `Future P w → Future (Future P) w`; pointwise implication distributes through `Future`. These are the T, 4 and K principles for this interpretation. For persistent predicates, the probe proves `Future P w ↔ P w`, instantiated with the actual `Fits` and `TypedProg` theorems. This is not a formalization or completeness proof of the S4 calculus. Nor does it make future quantification on a continuation redundant: the set of permitted inputs can expand with the world.

**2. Extension alone permits an invalid store.** Starting with the real initial world and an initial machine satisfying `WorldValid`, with a well-formed store, the probe constructs a `leHost` extension containing a dangling reference. The destination store is not well formed. This confirms why validity must accompany a transition proof; it does not exhibit a reachable runtime fault. Existing `TypedWorldValidity` tests already document this boundary.

**3. Per-world existence is weaker than a shared witness.** Every future world has some number equal to its reference count, but no one number works for both the empty world and a one-reference extension. A constant-witness positive control also passes. This checks the quantifier distinction behind `HookLaws`: one intermediate type must work across future worlds. It is a logical control using the actual order, not another counterexample to the repaired hook contract. Existing `FramesNotKripke` tests exercise the program-specific version.

**4. A conditional continuation contract needs handler fulfillment.** Using the actual generic `Effects.Typed` judgment, an impossible postcondition admits a continuation returning the wrong boolean, because no answer can satisfy the premise. With an inhabited postcondition, the good continuation is admitted and the bad one is rejected. This is intentional conditional reasoning, not a new production defect. The generic judgment is distinct from `TypedProg`. Given a proof of `StoreImplements` for the operation and a typed input store, `storeStep_typed` obtains an actual answer satisfying the postcondition and applies the continuation. Both contracts are needed.

## What this explains about the proof architecture

The construction earns its place through existing consumers. `fits_map` exposes the small set of preservation facts needed by membership. `fits_mono` packages those facts through `leHost`; it does not use every component of that order. `typedProg_mono` composes world extensions for continuations. Stack transport similarly uses transitivity, while saved-code transport also needs program monotonicity. `popR_typed` uses the shared future-stable type supplied by `HookLaws`.

Machine preservation adds obligations that these lemmas cannot solve. `CellCompatible` assumes preservation of the old coarse cell-typing facts; it is not a proof that arbitrary writes are safe. New allocations require new declarations and contents to agree. New tokens can invalidate previously vacuous conditional claims. Bookkeeping proofs therefore sometimes require unchanged declaration tables or old-position declaredness. `StepPreserves` produces both an extended world and a newly typed configuration.

This is demonstrated proof reuse, not a measured speed improvement. No proof-search benchmark or broad rebuild was run. A useful experiment would refactor one representative proof without changing its statement and compare its explicit premises, remaining obligations and checking time under the same compiler settings.

## Literature and documentation refinements

The documentation can use the theory more precisely in three places:

1. **Name the implemented judgment before calling it a weakest precondition.** The current system map's §10.1 uses that term for `TypedProg`. The code establishes a protocol-typed predicate with special control clauses; it is not generally closed under bind. The literature comparison needs a specified execution interpretation and a connecting theorem before importing a stronger weakest-precondition claim. Hazel's protocol interpretation is a useful source for the request/reply discipline, but its separating resources, masks and execution-defined weakest precondition are additional constructions. Its protocol upward closure also concerns reply postconditions, not our world extension. [de Vilhena–Pottier 2021, §§3.3–4.1](https://cambium.inria.fr/~fpottier/publis/de-vilhena-pottier-sleh.pdf).
2. **Restrict the monotonicity statement to named predicates.** The same overview says every judgment on values, frames and stores is monotone. Its earlier table already says configuration typing is not upward closed. The probe confirms that unrestricted store validity also fails to persist. List `Fits`, residual typing and the closed stack predicates; give their side conditions. Treat state validity and transition preservation separately.
3. **Explain the current absence of step indexing structurally.** `Fits` recurses over finite types, worlds hold syntactic types, and reference clauses consult declarations rather than recursively interpreting stored contents. Those choices avoid the circularity addressed by step-indexed models here. “No arrows, therefore no step indexing” would be too broad. Recursive semantic invariants or richer type interpretations could change the requirement. Lean function continuations in the proof-side carrier alone do not force that change. Iris's guarded later modality addresses a different issue from our preorder's future-world closure. [Iris 2015, §§5–6](https://iris-project.org/pdfs/2015-popl-iris1-final.pdf).

Proposed prose for Gemini to reconcile, without adding another authority:

> Effect4 uses world-indexed membership and continuations whose contracts remain valid under compatible world extensions. This is a unary Kripke interpretation of the current value language and its effect protocols. World extension preserves specified information; it does not represent execution or guarantee a valid machine state. Actual handler and transition proofs establish the resulting state and its invariant. These obligations connect the typing model to execution.

The scope-producing posts now include scope membership, and current positive controls exercise allocation followed by fork or close. Assembly still contains historical text calling that counterexample open. Reconcile the prose with the existing register, keeping the distinct general scope-validity question visible. Do not reopen the repaired post as a new failure or count this review as closing M5–M7.

## Bounded next work

**First, reconcile the chapter contract.** Gemini can adopt or challenge the proposed paragraph and distinguish world persistence, protocol obligations and actual state preservation. Acceptance is one source-backed definition for each concept, with links to the existing judgments and no new status registry. The literature review gives precise locators and exclusions.

**Then investigate three existing transition proofs.** Choose one store restatement/write, one fresh allocation and one token/resume delivery. For each, identify which premises preserve old facts, which establish new facts, and which establish validity or code/queue correlation. Begin with existing `fits_map`, `leHost_restate`, `StoreImplements` and `StepPreserves` rather than defining another world model. Only propose a shared lemma when two real consumers need the same statement. Any false obligation keeps its original statement and receives a minimal counterexample for the coordinator.

Completion for that implementation-oriented investigation is a small premise map and one demonstrably improved proof at an unchanged statement and axiom ceiling. That would give the theoretical alignment a concrete payoff while Gemini completes the chapter organization.
