# Choose obligations from the claim

Use this reference to select the smallest adequate assurance route. The
project owns exact gates and terminology.

## Representation and admission

| Intended claim | Necessary distinction |
| --- | --- |
| An accepted raw program is well formed | Admission success implies the stated typing/reference/profile judgment |
| Every supported valid program is accepted | Completeness for the promised fragment; soundness alone permits always rejecting |
| Reification represents its source | A relation from each accepted source to the emitted program, naming the source semantics and observation |
| Every source export has a disposition | Exact source census joined to one owner/profile decision; constructor coverage alone is insufficient |
| Checked data can be erased | Define erasure and prove the required reconstruction or semantic relationship; proof erasure is not byte erasure |
| A syntax is canonical | State normalization, its domain, idempotence, and equivalence/identity relation; avoid equating all semantic equality with byte equality |

For fail-fast diagnostics, distinguish first-error correctness from rejection
of every invalid input. A first-error checker cannot report every violated
clause on every run. An accumulating diagnostic census is a different product.

## Laws and semantic connections

An interpreter characterized as a monad morphism can still implement the wrong
operations. Require both the necessary pure/bind preservation and agreement on
each supplied operation. Conversely, operation agreement alone does not
constrain interpretation of arbitrary composition.

State whether a map is an embedding, normal-form recognizer, lossy projection,
simulation, refinement, or equivalence. Write both directions when equivalence
is required. Pin the domain: an isomorphism on canonical admitted terms does not
extend automatically to arbitrary raw input or all semantically equivalent graphs.

For effectful observations record:

- where typed failure, defects, interruption, and unfinished execution appear;
- whether failure-side state and partial traces are visible;
- whether order, causality, multiplicity, or only an outcome set matters;
- which choices are universally quantified, existentially selected, or fixed;
- which termination and fairness claims are separate from safety.

## Graph or local receipt

Use a graph for the smallest stable owner of admission, operational meaning,
interpreter/handler laws, recursive invariants, semantic reification, generated
code relations, or source-retirement/cutover conditions. Dependencies can
contribute to that graph without receiving a new graph of their own.

Use local receipts for a passive nonrecursive finite alphabet or value record
with no independently owned semantic/admission/cutover claim. Record its
signature, constructor census, applicable separation or round-trip facts,
trust receipt, and parent link if any. Public visibility or easy automation
does not decide the route.

Escalate before a leaf begins controlling admission or behavior. Retain its
previous receipts as obligations or name an explicit supersession. A finite
two-case Boolean classifier is not a passive leaf merely because it is small.

## Source evidence versus ownership

A paper or upstream implementation can motivate a design without becoming its
canonical owner. Record the prior-art relation: reuse at a pin, adaptation with
new obligations, or pattern only. A differing toolchain, semantics, license,
or trust policy can rule out direct reuse while leaving the pattern useful.

Before source retirement, require the project's compatibility relations, exact
source declarations and bytes, downstream observations, and every required
target or trust receipt. A local implementation milestone is not a retirement
certificate.
