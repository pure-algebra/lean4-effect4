# Proof structure and trust

## Choose the proof carrier from the obligation

| Obligation | Useful proof structure |
| --- | --- |
| Raw admission establishes a local invariant | Follow the validator's decisions and establish a separately stated judgment |
| Recursive traversal covers every child | Induct through the actual mutual/nested recursor; prove constructor equations and reconstruction |
| Interpreter respects a free program | Structural induction plus operation agreement and the required target laws |
| Composition of stateful computations | Thread exact intermediate state, history, resource context, and outcome |
| Step machine refines a denotation | State relation, initial correspondence, matched steps/stuttering, final observations, and divergence conditions if claimed |
| Bounded execution approximates runs | Fuel-indexed adequacy, extension/coherence, and stable-result properties for the stated domain |
| Infinite behavior | An admitted coinduction/fixpoint framework or explicit infinite-run relation with its hypotheses |

Do not invent a generic proof framework when a finite passive leaf needs only
a census and a few local equations. Do not treat a short proof as evidence that
its semantic owner needs only leaf receipts.

## Lock meaning, not only a theorem name

Record referenced definitions, namespaces, implicit instances, imports, local
notation, and options that can affect elaboration or trust. An unchanged
printed theorem name can refer to a changed definition. A proof of a weaker
predicate with the old name does not preserve the contract.

Inspect the statement before changing tactics. Try a minimal counterexample
for suspect quantifiers, empty cases, impossible premises, or omitted outcomes.
When the statement is false, return its counterexample and the smallest
contract amendment; do not add an assumption through a hidden instance.

## Inspect compiled dependencies

At the pinned toolchain, collect dependencies for the exact public theorem
and any exported computational definitions relevant to the claim. Include
compiler-generated equality instances, auxiliaries, and private declarations
where they contribute. The prior Effect4 repair found a partial implementation
inside a derived equality and a choice dependency reached through string
rendering. Source text alone did not describe the trust boundary.

`#print axioms` reports transitive logical dependencies. A source scanner adds
different evidence about forbidden authored constructs; it must understand the
accepted lexical forms and fail on unexamined input. Neither check replaces
the other. Use the project's complete module/declaration census.

Standard axioms such as `Classical.choice`, `propext`, and `Quot.sound` can be
mathematically acceptable under a declared policy. They do not all have the
same computational consequences. Proof irrelevance/erasure, noncomputable
witness selection, and execution through a trusted compiler need separate
treatment. [Lean axioms reference](https://lean-lang.org/doc/reference/4.33.0/Axioms/).

Native proof-by-evaluation mechanisms and their axiom names vary by toolchain.
Inspect the actual declarations, rather than checking only a remembered name
such as `Lean.trustCompiler`. A bespoke native-evaluation axiom is still an
external computation dependency. This pack does not enlarge the project's
allowlist.

If an exception is authorized, give it the narrowest stable semantic scope and
record why it is needed. For private declarations, resolve identity with the
owning module and original private name and reject missing/ambiguous matches
when using that mechanism. Check stale exceptions. An output-text admission
does not admit a new semantic axiom in the same module.

## Models propose; checkers decide

Retrieve exact accessible declarations and keep local proof context. Generate
small candidate lemmas or invariants and test their initialization,
preservation, and usefulness for the actual target. A true but irrelevant
invariant is not progress on the obligation. Preserve checked proof portions
and repair the earliest failing portion before retrying the whole argument.

Use the available project toolchain first. Research systems and empirical
benchmarks can suggest search techniques, but do not require their installation
or assume their reported speedups transfer. Record timeout or exhaustion as
inconclusive. Final acceptance comes from the saved artifact and required
fresh checks, not a model's explanation or an old cached success.
