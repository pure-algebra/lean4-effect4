# Durable workflows: contract and model handoff

Saving the existing `Program` or a callback name does not yet define a durable workflow. Keep `Program` and its existing laws. Add an inspectable document for the admitted source language, then establish the connections from source to document, document to behavior, and behavior to the chosen runner.

This is a formation record, not a frozen declaration packet. The exercise supplies the existing laws as a premise; their exact statements, imports, source revision, and Lean version are not supplied or independently checked. No implementation, execution, or repository modification was performed.

## Contract and ownership

| Artifact | Role and retained information | Disposition |
| --- | --- | --- |
| Authoring input | Supported callback expressions, operations, bindings, loops, and cleanup regions | An explicitly admitted source profile; arbitrary Lean or JavaScript functions are not automatically inputs to a reifier |
| Raw workflow document | Versioned, finite blocks; operation tags; typed operands; entry point; successor arguments; captures; named-call descriptors; body and cleanup regions | New data view needed for storage; retain malformed references and duplicate definitions until admission has diagnosed them |
| Checked workflow document | The same content with typing, scope, reference, and profile evidence | Canonical durable content, not another free-program carrier; proof certificates do not participate in content identity |
| Existing `Program` | Existing operation tree and function-valued continuations | Reuse as the semantic/proof carrier wherever the document's behavior can be interpreted into it |
| Execution configuration | Current block, local environment, state, installed cleanup registrations, pending exit, and external decisions already consumed | Runtime state, separate from immutable program content; failure must retain what cleanup needs |
| Host runner and named-call registry | Implementation of document operations and any admitted foreign calls | External realization with explicit version, typing, capability, and behavioral obligations |

These are proposed roles, not newly published declarations. The smallest assurance record is one dependency graph for admission, reification, meaning, encoding, and execution. None is merely a passive finite label.

The terminal observation is either a returned value with state after cleanup or a typed failure with state after cleanup. Admission refusal, a pending service reply, and an unfinished loop are separate outcomes of different boundaries. There is no general termination promise. Defects and interruption need a later explicit policy if admitted; they are not silently identified with typed failure.

Stored equality initially means equality of canonical document content, including code definitions or exact named-code versions, capture data, and all retained blocks. Keep block names and dead closed blocks significant unless a later normalization contract deliberately removes them. This gives a useful structural comparison; it is not a decision procedure for equality of all observed behaviors. Digests may index documents, but digest equality alone needs its own collision assumption if used instead of comparing content.

## The smallest admitted model

Use named blocks with typed arguments and explicit capture layouts. For example, a read operation writes its natural-number answer into a slot and transfers to a block expecting that slot plus a declared threshold capture. Comparisons, addition, literals, bound variables, and named calls are the provisional callback profile. Evaluation is sequential and evaluates operands in a declared order. A named call resolves to either an admitted, checked definition or a versioned foreign boundary; a string or function pointer alone is insufficient.

Admission checks all stored blocks, including unreachable ones, for unique identities, valid references, operand and argument types, closed captures, and profile membership. It separately checks scope and cleanup references. Cycles are allowed for the requested loops; reference closure and typing do not establish termination. Unrecognized callback forms receive an explicit unsupported-profile result. The admission obligation includes accepting the promised valid profile, so an always-refusing checker cannot satisfy the product contract.

The mutable threshold has two legitimate meanings that must remain visible:

| Save policy | Required document and replay information | Source correspondence |
| --- | --- | --- |
| Snapshot | Store the threshold value at a defined capture time, together with the callback code | Represents callbacks whose captures are frozen by this policy; it does not reproduce arbitrary later mutation of the prototype's closure |
| Live cell | Store an explicit, typed cell reference with its aliasing policy; reads and writes are modeled state operations | Replaying requires the same initial cell state and the relevant subsequent changes or decisions; an ambient JavaScript object pointer is insufficient |

Recommend snapshot captures for a reproducible saved workflow, while retaining the live-cell alternative when following subsequent changes is intended. Do not quietly apply the recommendation as a semantics-preserving conversion of the current prototype.

Callback coverage beyond the small profile is a separate open product choice. A later richer profile can reify binders and closures as code plus checked environments. Alternatively, a named foreign call can remain an assumption with an exact contract. Neither alternative supplies serialization of arbitrary host closures, and the current profile must not claim to accept those closures.

An inductive operation tree with a continuation for every natural answer need not contain finitely many nodes: a single read followed by returning its answer already has infinitely many answer branches. Reading a natural number and then performing that many steps also permits unbounded branch depth, even though each selected branch terminates. Thus induction does not establish finite-document size. Conversely, a finite document with a back-edge can describe an endless loop. It cannot generally be unfolded into the existing well-founded `Program` as a total conversion without an already suitable recursion operation or another justified semantic connection.

Use a step/run relation over the finite document and configuration for cyclic behavior. Reuse `Program` for the well-founded fragment and applicable operation or composition proofs. The run relation is not a second free-program datatype. The exact loop connection remains open; no new free carrier is introduced to disguise it. A bounded runner may return a resumable frontier, but exhausting its allowance proves neither failure nor divergence.

Cleanup is an exit-aware operation. It receives the state and registrations left by the body, including when the body failed. On successful cleanup, keep the body's original value or typed error and expose the updated state. Ordinary error-short-circuiting bind cannot supply this behavior. The model retains a named cleanup region and its captured environment until unwinding, and consumes each registration once. For multiple registrations, order affects state and therefore requires an explicit rule; LIFO is a proposed rule, not an observed guarantee. Cleanup failure policy is also open. These choices do not block the useful single, terminating, nonfailing-cleanup contract. A cleanup that waits or loops does not justify a claim of eventual release.

Replay uses the same checked document, code registry, capture policy and values, initial state, and a compatible record of external answers and other nondeterministic choices. Replies still range over every natural number. A missing reply leaves a frontier; an incompatible recorded reply/request is a replay-input error, not the workflow's typed failure. Fixed decisions may support uniqueness after a local determinism proof. Rerunning live services without reproducing their replies does not. Foreign side effects need a corresponding state-transition or replay contract; recording a return value alone need not reproduce them.

## Distinguishing cases

These are deductions and proposed acceptance cases, not executed tests.

For the numerical examples, use this illustrative admitted workflow: read the natural number, register cleanup that increments state, set state to the reply, then raise `bad` when the reply exceeds the captured threshold and otherwise return the reply plus 1. On either body exit, invoke the registered cleanup.

| Case | Input and expected distinction |
| --- | --- |
| Inhabited profile | Read 4, use threshold 5, set state to the reply, return reply plus 1, then increment state in cleanup: return 5 with final state 5 |
| Failure cleanup | In the same workflow, reply 7 exceeds threshold 5 and raises `bad` after setting state to 7: cleanup must leave typed failure `bad` with final state 8 |
| Hidden capture | Keep the callback name and pointer unchanged but change the ambient threshold from 5 to 10. For reply 7, the proposed workflow changes from failure to returning 8. Equal callback names do not determine the stated observation |
| Malformed versus unsupported | An undeclared capture or dangling successor is invalid data; a host callback containing an unadmitted language form is unsupported source. Neither is an executed typed failure |
| Loop frontier | A valid self-edge remains a valid cyclic document. A finite evaluation allowance may stop at that edge without establishing a final outcome |
| Unbounded answer | A service answer greater than the exact integer range of a JavaScript number remains an admitted natural number. Any JavaScript realization needs an exact arbitrary-precision representation or an explicitly narrower source contract |

## Connections still required

All rows below are open. Owners are roles to assign before implementation; no names in this table assert that a theorem or checker already exists.

| ID and owner | Exact connection and its scope | Required evidence and consequence if absent |
| --- | --- | --- |
| D1 — admission owner | Successful raw-to-checked admission implies whole-document typing, closed references/captures, and membership in the chosen profile; every promised valid input is accepted | Local statements and proofs against the actual checker, plus inhabited valid and invalid controls. Without this, “checked” does not justify its advertised conditions |
| D2 — source/reifier owner | For every accepted source and its emitted document, under the selected capture and named-call contracts, the two have the same specified terminal observations for corresponding inputs and decisions | Source-to-document relation, typing and binding/capture arguments, and both required observational directions. Arbitrary host callbacks remain outside this claim |
| D3 — semantic owner | Interpretation of the well-founded document fragment agrees with the existing `Program` operations and composition; cyclic documents have the separately stated run meaning | Pin and reuse the existing equations, prove the new interpretation and substitution connections, and account for recursion explicitly. Monad laws alone establish none of the source, encoding, or host arrows |
| D4 — scope owner | On body success or typed failure, successful cleanup runs once from the body-left state, preserves the original exit, and returns the cleanup-left state | Local exit/state and registration invariants, with the failure-cleanup witness above. Further cleanup failures or interruption require their own chosen rules |
| D5 — codec owner | Decoding an encoding reconstructs the checked content. Encoding an accepted raw decoding yields its declared canonical spelling; arbitrary raw spelling is not promised to round-trip exactly | Codec relation, reconstruction and canonicalization laws, and deterministic byte checks at pinned inputs. Do not claim semantic equality from byte normalization |
| D6 — runner owner | Every bounded runner completion corresponds to a run with the same terminal observation; continuation from a frontier resumes its retained state. Under fixed compatible decisions, the selected deterministic fragment has at most one outcome | Runner-to-relation and determinism proofs. Loops, unanswered requests, and eventual cleanup still carry their separate progress obligations |
| D7 — target owner | For each permitted target run, corresponding source behavior has the same returned value or typed failure and final state; any replay-equivalence claim also needs the converse required by the contract | Explicit environment/decision relation and semantic proof or justified validation route; separately, bounded host comparisons over exact document, registry, runtime, and numeric-representation pins. Existence of one matching host run does not exclude extra bad runs |

Exact source, document schema, registry, encoder, and toolchain identities must be recorded before producing receipts. No source generator is part of this handoff, so there is no invented generated-code gate. Future checks should include independent expected observations for capture changes, failure-side state, large naturals, malformed nested references, and pending loops. Host tests would remain bounded evidence beside the unproved or proved semantic connections.

No user input is needed to deliver this design. The first decision requiring the user before choosing one frozen meaning is whether saving captures the threshold now or follows later changes to an explicit shared cell. Callback coverage beyond the stated profile can remain a declared alternative until implementation or a broader acceptance promise requires a choice. The present result is a usable restricted-profile design with named open connections, not an assertion that replay has been verified.

## Sources and work limits

The exercise and repository instructions were read from [case 01](/Users/pooks/Dev/lean4-effect4/skills/lean-reification/evaluations/cases/01-durable-workflow.md), [AGENTS.md](/Users/pooks/Dev/lean4-effect4/AGENTS.md), and [COORDINATION.md](/Users/pooks/Dev/lean4-effect4/COORDINATION.md). No live implementation or historical proof receipt was inspected.

Skill files used:

- [lean-reification](/Users/pooks/Dev/lean4-effect4/skills/lean-reification/SKILL.md), [evidence vocabulary](/Users/pooks/Dev/lean4-effect4/skills/lean-reification/references/evidence.md), and [project entry points](/Users/pooks/Dev/lean4-effect4/skills/lean-reification/references/projects.md).
- [lean-reification-contract](/Users/pooks/Dev/lean4-effect4/skills/lean-reification-contract/SKILL.md), [contract record](/Users/pooks/Dev/lean4-effect4/skills/lean-reification-contract/assets/contract-record.md), and [obligation selection](/Users/pooks/Dev/lean4-effect4/skills/lean-reification-contract/references/obligations.md).
- [lean-reification-model](/Users/pooks/Dev/lean4-effect4/skills/lean-reification-model/SKILL.md), [model record](/Users/pooks/Dev/lean4-effect4/skills/lean-reification-model/assets/model-record.md), [representation decisions](/Users/pooks/Dev/lean4-effect4/skills/lean-reification-model/references/representation.md), and [effects and logic](/Users/pooks/Dev/lean4-effect4/skills/lean-reification-model/references/effects-and-logic.md).
- [lean-reification-target](/Users/pooks/Dev/lean4-effect4/skills/lean-reification-target/SKILL.md) and [transformation boundaries](/Users/pooks/Dev/lean4-effect4/skills/lean-reification-target/references/boundaries.md).

No workflow ambiguity prevented a useful result. The project-entry reference points toward live implementation records; those were intentionally not followed because this exercise authorizes only a packet-based design. The mutable-capture and wider-language questions are product decisions retained in the design, not reasons to request permission or start implementation.
