# CX, module authoring, and live tooling: support packet

**The coordinator's first action:** implement option (e) with a guarded typing rule for closed code, including captured argument sites.
Checker independence alone cannot satisfy today's stack predicate for unused parameters.
The detailed path is E1–E6 in [PROOF-DAG.md](PROOF-DAG.md).

The owner selects option (e), followed by per-call layers, in Claude's repository session at `2026-10-10T14:31:02.543Z`.
The session's cwd is `/Users/pooks/Dev/lean4-effect4`.
This packet supports that selection and does not request another ruling on it.
The inspected tracked authority still lists the earlier options; the coordinator records the amendment with the implementation.

## Recommendations

1. Admit same-owner references and references to expanded targets that read no incoming program parameter.
   Identify an owner by its definition body, not by equality of parameter declarations.
   Keep one dependency fold for the checker, proofs, and authoring explanations.
2. Separate that repair from layer allocation.
   The nested-call control contains no reference and still shares the outer call's build.
   Per-call ownership must also specify exported closed targets and repeated constructor evaluation inside loops.
3. Give CX3 the first module-authoring design slot.
   Certify the existing captured-program interpretation, with the declared answer, error, and requirement bounds.
   Keep raw program syntax expansion behind a separate capture and inference contract.
4. Develop S1 independently on its sequential resource fragment.
   Keep original exits, changed stores, registration identities, and unfinished cleanup in the observation.
5. Build a shared paused-run view and revision-checked draft API.
   Derive each view from one recorded run and its checking context.
   Keep draft editing separate from migration of an already running program.

## Read the packet

| File | Content |
| --- | --- |
| [CX-DESIGN.md](CX-DESIGN.md) | Scope policy, shared dependency structure, memo identity, CX3/CX4 authoring contracts, and S1 priority |
| [PROOF-DAG.md](PROOF-DAG.md) | Dependency diagrams, statements, five-point placement, consumers, bounds, landing order, and planning ranges |
| [TOOLING-DESIGN.md](TOOLING-DESIGN.md) | Concrete editor, viewer, reply, replay, and MCP API improvements with remaining connectors |
| [PLAN.md](PLAN.md) | Placement and finish conditions for the host-wait and cleanup controls |
| [CX-PLAN.md](CX-PLAN.md) | Placement of scope, memo, and substitution controls |
| [verify.py](verify.py) | Sequential narrow verification and evidence collection |
| [verification.json](verification.json) | Exact commands, timestamps, source hashes, probe hashes, guard counts, and exit codes |

No proposed representation or theorem in the design documents is marked implemented.
No production proof, public API, or semantics registry changes in this packet.

## Review base and ownership

The review worktree starts at `8ce5e1c4fed3512077b7aabc207414effd569056`.
Its branch is `codex/review-host-frontier-features`.
The primary checkout is `a2b589deeb741bb246b6e85156e2c092bb1215a2` when inspected.
The intervening change only corrects the layer goal's docstring and its research note.

Claude's inspected work plans the option-(e) checker agreement from the existing signature-read algebra.
The primary checkout's `src/Effect4/Laws/Program/TyView.lean` belongs to another session and remains untouched.
The implementation session, production files, `lakefile.toml`, and owner registers remain unchanged by this review.
All new files stay inside this review packet.

The earlier cross-scope falsifier is retained byte-for-byte in [LayerContextControls.lean](LayerContextControls.lean).
Its original base and placement comments remain part of that evidence.
This packet reruns it at the new review base; it does not report the old finding as a new defect.

## Checked findings

| Observation | Evidence | Consequence and limit |
| --- | --- | --- |
| The original cross-scope program admits an impossible child error | Retained admitted-run controls in `LayerContextControls.lean` | The existing planned goal remains open; no goal-free theorem is refuted |
| Equal parameter lists do not identify one lexical body | `makeProgram` and `ownerAt` controls in `CXControls.lean` | Use body ownership for option (e); the probe reader still needs its general connector |
| Closed references remain usable under the proposed policy | `closedRefs` accepts the closed target and `closedInvoker` | A callee can use its own parameter; the caller-independent target need not be pure |
| The proposed rule rejects both bad and equal-declaration cross-owner targets | `closedRefs` negative controls | Finite policy checks establish no general stack or memo theorem |
| Nested calls reuse a layer even with no reference | `nestedProgram` returns `1`; explicit freshness and local memo return `2` | Visibility repair does not decide construction identity; no external Effect run occurs |
| Raw insertion can lose a capture across a layer boundary | `captured` returns `41`; `rawCaptured` is refused in `CX3Controls.lean` | CX3 needs existing captures or a lawful capture-materialization transformation |
| Raw insertion can change an invariant reference column | Invocation has `refOf (list nat)`; raw body infers `refOf (list never)` | Declared bounds matter; checked ascription repairs this finite answer-column example |
| Cleanup observes state produced before failure | `Controls.lean` waits on close request `2`, then finishes with the body error | Loop meaning and run agree on request, all stores, and remaining replies in the checked instances |
| Final error alone misses destructive cleanup | Resetting cleanup changes its close request to `0`, but retains the same final error | Resource agreement must observe retained state and cleanup interaction |
| Actual waits provide distinct addresses and reply types | Source-origin and checked-instance controls for fetch and cleanup | Supports the inspector proposal without proving expanded-reference address agreement |

There is one further source-level proof finding.
`LayerPointTyped` in `src/Effect4/Laws/Program/Typed/Admission.lean` requires every declared parameter through `StackTyped`.
An expanded target that never reads those parameters does not supply that premise after a cross-owner redirect.
The proposed closed-code branch must therefore cover argument sites as well as the initial layer point.
E4 places the required transport before proof work begins.

## Proof and verification evidence

Run the packet from the review root:

```sh
python3 docs/research/2026-10-10-cx-authoring-support/verify.py
```

The script sets `LEAN_NUM_THREADS=3` and runs one Lake process at a time.
It builds only these dependencies:

```text
Effect4.Laws.Api.SessionMeaningLoop
Test.Dogfood.Scenario
ProofGraph.AxiomAudit
ProofGraph.Plan
Effect4.Laws.Program.Typed.Commands.Clauses.All
```

It compiles four finite probe files and runs two cycle-aware audit files.
Every recorded command exits successfully.
The recorded probe files contain 98 `#guard` controls in total.
These include positive and negative controls, not 98 general theorems.

`Audit.lean` audits 690 declarations within `[propext, Quot.sound]`, with no planned goal dependency in that selected set.
It confirms these four statements are proved:

- `Effect4.Run.rows_loop_frontier`;
- `Effect4.Run.rows_loop_frontier_host`;
- `Effect4.Program.Agreement.localWaitC_to_rowsB`;
- `Effect4.Program.Agreement.localRunC_compileBO`.

`CXAudit.lean` audits 55 declarations in the CX probes within the same axiom ceiling.
Those probe declarations depend on no planned goal.
Its separate plan queries confirm `invoke_arm` and `param_arm` are proved.
They also confirm `crossScopeRef_builds` is a goal and `m7_proved` still depends on it.
This is not an audit of every declaration in the CX production graph.

The proof outputs are [audit.log](audit.log) and [cx-audit.log](cx-audit.log).
The other logs and [verification.json](verification.json) retain the exact reproducible checks.
No full sweep, TypeScript check, runtime comparison, merge, or push occurs.
The TypeScript source review names rc.112's implementation; it is not an executed conformance result.

## L4 review conclusion

The detailed waiting statements are stronger than the earlier coarse frontier result.
Under their premises, they identify the pending row, request, machine stores, and corresponding host state.
The arbitrary-host statement requires silence on the pending request as well as agreement on earlier answers.
The finite cleanup controls exercise those distinctions.

The reviewed fragment still excludes definitions, layers, `scoped`, acquisition, forks, and interruption.
There is no equality of unrelated budgets or proof that the host eventually answers.
A fuel cut remains a live frontier; it is not the failed exit that starts cleanup.

## Checkpoint for the next review

Reviewed executable base: `8ce5e1c4`.
Reviewed primary documentation correction: `a2b589de`.
Reviewed session change: owner selects option (e), then per-call layers; implementation is still being planned at the inspection point.

Outstanding work is E1–E6, the precise allocation policy, CX3/CX4 contracts, S1, and the named tooling connectors.
The previous layer failure remains open and unchanged at the reviewed source.
The newly reproduced CX3 controls and allocation controls constrain the proposed repairs.
The L4 detailed-frontier review is finished on its stated fragment and evidence set.

Review subsequent commits against this checkpoint.
Do not repeat unchanged findings or turn these finite controls into broader runtime claims.
