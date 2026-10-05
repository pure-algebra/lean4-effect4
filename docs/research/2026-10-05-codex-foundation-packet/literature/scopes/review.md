# Scope contracts from primary literature

Evidence status: source checked.
Proof role: design input and proposed obligation.
Scope: syntax for mask/restore, nested attempts, and posted program bodies.

## Sources

Wu, Schrijvers and Hinze, [Effect Handlers in Scope](https://people.cs.kuleuven.be/~tom.schrijvers/Research/papers/haskell2014.pdf), Haskell 2014.
Sections 8–10 distinguish a scoped program argument from the continuation after its scope.
Handler order changes state and exception interaction without changing that lexical boundary.
Section 11 gives a concrete fork counterexample.
Substituting the parent's continuation into both fork children duplicates its execution.
Its corrected syntax signature distinguishes the child program from the parent's continuation.
The example scheduler discards daemons when the master ends; that policy is not Effect4's scope contract.

Lindley et al., [Scoped Effects as Parameterized Algebraic Theories](https://www.cs.ox.ac.uk/people/samuel.staton/papers/esop2024.pdf), ESOP 2024.
Section 2.2 explains why catch does not commute with ordinary substitution.
Sections 2.2–2.3 separate scoped bodies from following computations and describe scope names.
Their well-formed terms close scopes once, in reverse opening order.
The paper supplies a framework and examples, not a theorem about Effect4.

## Adaptation proposed for this tree

Keep `Eff` as canonical first-order program data.
These papers' higher-order signatures describe scoped program arguments; they do not require storing Lean functions in Effect4 syntax.
Represent bodies, binders, saved mask references, and following code explicitly using the existing signature machinery.
Do not introduce a second program representation or plain begin/end markers without a formation judgment.

Distinguish three traversals before generalizing task bodies.
Renaming changes names under the declared binders.
Substitution respects those binders and the distinction between a scoped body and its following code.
Compilation carries the same distinction into captures and target syntax.
The existing generators should own these traversals.

Proposed obligation: `scoped_body_substitution_boundary`.
Concept: `residual-program-typing`, serving R4 and the M5–M6 path.
Proposed placement: the program-admission claim for the first new scoped constructor, not a separate algebra hierarchy.
Consumer: mask/restore or the first generalized posted body.
Premises: formed first-order syntax, explicit binder signature, typed captures, and an admitted lexical saved-state reference.
Observation: following code executes only after the declared scope; substitution cannot capture or duplicate it into child bodies.
Exclusions: no cancellation, scheduling, or target-agreement result follows from this syntax property.
Immediate prerequisite: freeze the child-body and continuation fields in the signature.

Use nested masks and a child that exits before its parent as acceptance cases.
Keep the actual masking rule in the task contract; ordered scope syntax alone does not establish it.

## Receipt

[downloads.json](downloads.json) records author URLs, retrieval times, file hashes, and successful text extraction.
The command uses the installed `pdftotext -layout` reader.
No reference implementation was executed.
