# Residual program typing

This page explains residual program typing in Effect4. It covers how effectful programs denote typed interactions and why sequencing relies on explicit compatibility lemmas rather than unrestricted bind.

## The runtime concept {#runtime-concept}

Effect programs structure asynchronous and stateful workflows by chaining operations, handling failures, and bracketing resource lifecycles. At runtime, these workflows yield control steps and await replies.

Effect4 separates stored program IR from semantic execution. First-order stored syntax denotes residual programs that formalize operational continuations.

Residual program typing certifies that every step of a residual program complies with protocol requirements and handles replies safely.

## Literature foundations {#literature}

The concept connects to effect systems in ATTAPL ch. 3 (Henglein, Makholm, Niss), which statically track computational effects and regions.

Protocol typing adapts the handler verification principles of de Vilhena and Pottier (2021). Continuations must accept all valid answers under extended worlds.

The representation draws an analogy to Interaction Trees (Xia et al. 2020), where monadic programs interact through typed operation nodes.

## What Effect4 keeps and what it cuts {#adaptations-and-cuts}

Effect4 keeps protocol-directed verification via the judgment `TypedProg` (`src/Effect4/Laws/Program/Typed/Residual.lean`). This inductive predicate types free-monad residual programs against worlds.

Operation clauses enforce that continuations remain well-typed for every permitted answer at any future world accessible by `World.leHost`.

Effect4 cuts stored closures from program syntax (decisions row 163). Function continuations exist solely in the semantic carrier `RProgram`, never in stored `Eff` trees.

Importantly, `TypedProg` is not closed under unrestricted monadic bind (decisions row 148, `E4-TYPED-CE-030`). Control bracket markers like `unguard` carry exit values directly, breaking general bind typing.

Effect4 replaces unrestricted bind with construct-specific compatibility lemmas such as `seq_typed` and `guardBind_typed` (`src/Effect4/Laws/Program/Typed/Seq.lean`).

## How to read the claims {#reading-claims}

The claims under this concept state that denotation produces well-typed residual programs and that control flow constructs compose without defect.

Key properties to inspect:
- [`denote-typed`](#claim:denote-typed): The denotation of an admitted program produces a well-typed residual program.
- [`seq-typed`](#claim:seq-typed): Sequential composition keeps residual typing when chaining valid success continuations.
- [`bind-closed`](#claim:bind-closed): Unrestricted bind closure is refuted by an explicit counterexample.

These claims show that certified program trees translate into valid operational models without assuming universal monadic composition.
