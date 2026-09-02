---
name: lean-reification-audit
description: Review claims about reified programs across intent, representation, Lean proof trust, transformations, and host behavior. Use for correctness, equivalence, complete reification, or cutover reviews; keep the reviewed tree unchanged unless repairs are requested.
---

# Audit the claimed connection

State the claim and its scope before reviewing evidence. Pin the reviewed
files and inspect the project's live assurance rules. Default to a read-only
review; isolate any authorized counterexample or mutation run. Read
[evidence meanings](../lean-reification/references/evidence.md) and use the
existing project ledger rather than creating a competing completion authority.

## Audit each required link

| Link | Decisive questions |
| --- | --- |
| Intent to contract | Are source profile, environment assumptions, and observations the intended ones? Can the premises hold? Is there a positive witness? |
| Contract to representation | Does stored data retain required control, state, captures, distinctions, and all recursive/source cases? Are exclusions explicit? |
| Representation to meaning | Do admission, handlers, decisions, history, and outcome classes match the proposed semantics? Is any loss named? |
| Meaning to proof | Is this the frozen statement over the frozen definitions? Did Lean check it with the permitted transitive dependencies? |
| Model to generated artifact | Is each transformation related to its source, or merely deterministic and well-typed? Is the checked domain exact? |
| Artifact to execution | Were the intended bytes, files, version, runtime, observer, and cases actually exercised? What lies outside the formal model? |

For each link record proved, checked, tested, assumed, or open using the shared
definitions. A broad result cannot compensate for an absent required link.
Check actual theorem types and gate commands, not just names or green labels.

For EffHOL-related claims, read
[the adaptation boundary](../lean-reification/references/effhol.md). Verify the
chosen interpretation's obligations rather than importing a paper theorem as
a fact about Lean or Effect. For concurrency, distinguish all-runs safety,
possible behavior, fairness-dependent progress, and one selected execution.

## Attack acceptance

Inspect counterexamples, witnesses, and the deliberately wrong candidates
the gates reject. Ask whether an always-rejecting checker, a constant generator,
an omitted recursive child, or extra target behavior could still pass.
Use [Breaker](../lean-reification-breaker/SKILL.md) for a concrete new challenge.

Check the trust audit's complete scope: modules and declarations actually
loaded, compiler-generated dependencies, source scanner errors, exact
exceptions, and omitted files. A parser failure is not a clean audit, and an
upstream build failure is not evidence that a later detector rejected a mutant.
Treat scoped exclusion as a limit on the claim, never as whole-tree acceptance.

For finite leaves, require the local declared receipts and any parent link.
For semantic or cutover owners, inspect the applicable proof graph. Missing
edges remain open; an authored reason is needed for inapplicability. A passive
constructor count neither requires a large graph nor closes a semantic one.

## Independent review and verdict

When an independent reviewer is required, use a separate available agent or
process under the existing authorization. Give it the claim, raw artifacts,
authority files, and edit fence. Withhold the builder's desired verdict and
hidden evaluation answers. If independent review cannot be obtained, mark that
gate open; do not label a self-review independent.

Report findings as intent mismatch, representation/semantic defect, proof
debt, transformation gap, external assumption, or evidence failure. Each
finding names the exact artifact, decisive evidence, practical consequence,
smallest corrective action, and owner. Distinguish an established defect from
an unverified suspicion.

Finish with the strongest justified claim and required remaining work, using
[the audit record](assets/audit-record.md) if needed. Mark full acceptance only
when the project's required gates are satisfied. If fixes were requested,
carry authorized repairs through the appropriate stage and recheck affected
links; preserve the original finding and the evidence that resolves it.
