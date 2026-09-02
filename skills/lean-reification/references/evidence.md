# Evidence for a program connection

An evidence label describes one claim over one artifact and scope. These labels
are not a ladder on which more testing becomes a theorem.

| Evidence | What it establishes | Required record |
| --- | --- | --- |
| Proposed | A question, design, or candidate obligation | Intended meaning, owner, and unresolved choices |
| Refuted | A stated claim fails on an admitted witness | Exact claim, witness, assumptions, and reproducible result |
| Bounded survivor | No counterexample was found in a specified search | Bounds, domain, search/checker, options, and result |
| Checker accepted | A named checker accepted an exact artifact | Checker and artifact pins, checked scope, result, and checker trust |
| Lean proved | Lean accepted the stated theorem | Exact statement and definitions, toolchain, saved proof, transitive axiom receipt |
| Host tested | Particular runs matched a stated observation | Program bytes, runtime/packages, inputs/decisions, observer, cases, and results |
| Assumed | The claim depends on a supplied condition or external contract | Exact assumption, owner, rationale, and consequences if false |
| Open or inconclusive | Required evidence is absent or undecided | Gap, attempted checks, and next decisive action |

A kernel proof can establish a universal theorem about a bounded runner while
remaining silent about unbounded execution. A universal theorem about a model
can coexist with an open connection to a host. Record both the theorem's
quantification and what the modeled domain leaves out.

## The evidence unit

Use the project's existing record format; otherwise capture:

- claim ID, exact statement, direction, admitted domain, and observation;
- source and target artifact identities, definitions, toolchain and dependency
  versions, and any dirty-tree digest;
- witness or accepted artifact, command, exit result, and durable output;
- assumptions, bounds, exclusions, and trust boundary;
- owner, dependencies, status, and the evidence needed to close an open edge.

Missing evidence is not a negative result. A timeout, parse failure, unavailable
tool, unsynthesizable instance, or unfound proof is inconclusive unless the
contract specifically makes that outcome a refusal. Preserve the reason.

## Claim directions

For compiler-like work, spell out the behavior relation. If every target
behavior must satisfy a source safety property, the needed inclusion is
normally that each allowed target behavior corresponds to an allowed source
behavior, under the stated environment relation and safety assumptions.
Showing only that each source behavior has some target realization allows
additional bad target behaviors. Deterministic special cases may justify a
simpler theorem; retain the determinism and termination hypotheses.

For nondeterministic observations, state whether the claim concerns some run,
all compatible runs, one fixed decision tape, or only fair runs. For a quotient,
say exactly which distinctions it hides. Equivalence at a coarse observation
does not imply equality of stored syntax, causal topology, or finer traces.

## Trust is a separate dimension

The logical axioms accepted by a project, the implementation of a checker,
the compiler/runtime executing a test, and assumptions about the external
environment are different dependencies. Record them separately. A standard
classical axiom is not the same as unchecked native computation; neither is
automatically permitted by a particular project's policy.

An external solver or model may propose a result. If a checked certificate is
the assurance route, retain the certificate and acceptance theorem. A Boolean
answer without that connection is checker evidence under the checker's trust
statement. A language model contributes candidate text, not logical trust.

## Completion

Choose required obligations before reviewing their results. A semantic owner
closes only when each required edge has evidence of the needed kind. A passive
leaf closes through its declared local receipts and parent link. Mark an edge
inapplicable only with an authored reason; do not create empty graphs for leaves.

Use the current project gate and recorded scope. An excluded failing module
remains outside the compiled audit even if a self-test passes elsewhere. A
historical receipt remains historical until reproduced or explicitly reused
against identical relevant artifacts.
