# Blaze: research note

## Source status

- Canonical repository: <https://github.com/DeVilhena-Paulo/blaze>
- Local study checkout: `.reference/clones/blaze`
- Resolved commit: [`76cf4cb0e7d68fc71f17eed539b411b194c9ca38`](https://github.com/DeVilhena-Paulo/blaze/commit/76cf4cb0e7d68fc71f17eed539b411b194c9ca38)
- Source Lock admission: **pending**. The commit above identifies the material inspected for this note, but no Source Lock receipt or estate admission is claimed.

This note is based only on primary files in that checkout. No dependency was installed, and the development was not built or executed.

## What Blaze is

Blaze is the Rocq formalisation accompanying *A Relational Separation Logic for Effect Handlers*. Its repository is organized around a purpose-built language (`lambda_blaze`), an Iris instantiation, two relational logics named `baze` and `blaze`, an adequacy argument, and paper case studies. ([README](../../../.reference/clones/blaze/README.md), [`opam`](../../../.reference/clones/blaze/opam))

The object language makes several effect-handler choices explicit: generative effect labels; `Effect`, `Do`, and `Handle` expressions; deep versus shallow handlers; one-shot versus multi-shot modes; and corresponding one-shot and multi-shot continuation values. It also includes heap operations and `Fork`, so the handler semantics are studied in a stateful, concurrent setting rather than as a pure core calculus. ([syntax](../../../.reference/clones/blaze/theories/syntax.v))

Operationally, a generated effect substitutes a fresh label; handling an operation captures either a one-shot or multi-shot continuation; and deep handling reinstalls the handler frame whereas shallow handling does not. One-shot invocation records consumption in the heap, while multi-shot invocation reuses its captured context. ([semantics](../../../.reference/clones/blaze/theories/semantics.v))

The logic layer is built in Iris. It defines relational theories (`iThy`), sums, an empty theory, a one-shot operator, label-indexed theory lists, and context traversal; `adequacy.v` then states bridges from `REL`/`BREL` judgments at an empty theory to `NotStuck` adequacy and matching termination of the specification side. These are statements present in the source, not independently checked results in this study pass. ([logic](../../../.reference/clones/blaze/theories/logic.v), [adequacy](../../../.reference/clones/blaze/theories/adequacy.v))

The repository declares `coq-blaze` under `LGPL-3.0-only` and pins Coq 8.20.1 plus a development snapshot of Iris HeapLang. The bundled license text is GNU LGPL version 3. ([package manifest](../../../.reference/clones/blaze/opam), [license](../../../.reference/clones/blaze/LICENSE))

## Relevance to the effects library

- The syntax and reduction rules provide concrete prior art for keeping handler depth, continuation multiplicity, effect identity, captured contexts, and resumption behavior as separate semantic dimensions rather than collapsing them into one handler operation. ([syntax](../../../.reference/clones/blaze/theories/syntax.v), [semantics](../../../.reference/clones/blaze/theories/semantics.v))
- The relational-theory layer is a useful design reference for reasoning about two handler-based implementations through effect protocols and evaluation contexts, rather than requiring syntactic identity. Its label-indexed theory lists and traversal operator are especially relevant when assessing how the library should represent scoped protocols and context-sensitive composition. ([logic](../../../.reference/clones/blaze/theories/logic.v))
- The adequacy file marks the kind of explicit bridge needed before an internal relational judgment can support an external behavioral claim. The effects library may reuse that separation of concerns as an architectural lesson, but any Lean judgment and theorem must be stated and proved locally. ([adequacy](../../../.reference/clones/blaze/theories/adequacy.v))
- The included case studies exercise state, exceptions, concurrency, `async`/`await`, and nondeterminism, making them candidates for future comparison scenarios once the relevant Foldlab contracts exist. ([README](../../../.reference/clones/blaze/README.md), [examples](../../../.reference/clones/blaze/theories/examples))

## Limits and non-claims

- This is study material, not an admitted dependency, a vendored implementation, or evidence that the Foldlab effects library satisfies any Blaze judgment.
- No Blaze theorem was replayed, no assumption set was audited, and no claim of soundness, equivalence, preservation, completeness, or verification is made here.
- Blaze is a Rocq/Iris formalisation of its own language and logic; it is not a Lean implementation, a TypeScript runtime, or a drop-in specification for this library. ([README](../../../.reference/clones/blaze/README.md), [`_CoqProject`](../../../.reference/clones/blaze/_CoqProject))
- Reusing code, rather than ideas described at this level, requires a separate licensing and provenance decision because the source declares `LGPL-3.0-only`. ([package manifest](../../../.reference/clones/blaze/opam), [license](../../../.reference/clones/blaze/LICENSE))
- The exact local commit is recorded above, but Source Lock admission remains pending.
