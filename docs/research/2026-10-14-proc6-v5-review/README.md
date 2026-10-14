# PROC-6: review of the proposed version-5 amendment

The amendment resolves F2, F3 and F4 as design issues. F1 still contains a false proof step.
Revise that step before freezing the plan or decisions row 379.

The remaining counterexample concerns the proposed invariant. It does not refute `H9Blocks` or demonstrate another scheduler-budget change.

## Reviewed material

- [Proposed version-5 amendment](inputs/proposed-v5.txt), supplied by the owner.
- [Version-4 plan snapshot](inputs/plan-v4.md), the plan still present on disk during this review.
- [Previous review](../2026-10-14-proc6-codex-review/README.md), including its retained counterexamples.
- Source commit `7c9bb76172400d2f885cf461f2f09db334d2495a`.

Three Sol 6.1 agents reviewed the reply boundary, the proof structure, and the consumer.
The parent independently repeated the decisive Lean and runtime probes.
The [manifest](manifest.json) records source and evidence hashes.

The review changes no implementation, plan, decision or registry entry.
The probe obligations serve `rows-block-host`, concept `translation-simulation`, requirement R6.
They are review controls, not landed theorem claims.

## Disposition of the previous findings

| Finding | Amendment assessment | Evidence and remaining obligation |
| --- | --- | --- |
| F1: scheduler budget and reply boundary | Partly resolved; rework remains | Keeping local relations general is coherent. The proposed membership-to-recursive-safety implication is false. |
| F2: small scheduler budgets | Resolved as a design correction | The thresholds distinguish resumption from positive progress. Finished-run agreement retains its receipt premises. |
| F3: shared service captures a request recorder | Resolved for Stage 5 | Stage 5 retains a fresh service per request. The shared proxy and persistent replay remain explicit future work. |
| F4: body proof does not reach the block root | Resolved as a proposed contract | The root wrapper supplies the missing connection. Its implementation and proof remain open. |

## N1 — major: defects defeat the proposed recursive safety implication

The amendment says that `.die` carries no `Val`. That is false in this tree.

`Defect.error` carries `Err`, and `Err.payload` carries `Payload.val`.
`Payload` requires a handle-free record. It does not require a context-free record.
These declarations are in [Machine/Alphabets.lean](/Users/pooks/Dev/lean4-effect4/src/Effect4/Machine/Alphabets.lean).

`reasonAdmits` accepts a defect at every error type, including `never`.
Its definition is in [Program/ErrorImage.lean](/Users/pooks/Dev/lean4-effect4/src/Effect4/Program/ErrorImage.lean).
`Val.hasTy` uses that check for reified causes and exits in [Program/Typed.lean](/Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Typed.lean).

The retained witness contains:

```text
context: maxOpsKey maps to nat 1
payload: record { hidden: context }
defect: die (error (payload ...))
value: the reified failure containing that defect
```

The proposed filter accepts `causeOf never` and `exitOf unit never`.
The witness inhabits both types, while its value tree contains the forbidden context.
Thus `ContextFreeTy ty → Val.hasTy v ty → BudgetSafeVal v` fails for the specified whole-tree predicate.

### Checked success reply

The [agent probe](evidence/context-scheduler/Bridge.lean) constructs a closed external row with answer type `exitOf unit never`.
Signature admission and program admission both accept it.
The checked session applies a successful reply containing the witness value.

The independently repeated [output](evidence/parent/bridge-parent.log) establishes these observations:

```text
Val.hasTy at causeOf never: true; forbidden context found: true
Val.hasTy at exitOf unit never: true; forbidden context found: true
signature admission: ok
program admission: true
checked run: some (0, true, [2048])
```

The final tuple means no outstanding call, the forbidden descendant in the completed success, and scheduler budget 2048.
The diagnostic searches this finite value tree to depth 100. It is not a universal safety checker.

### Checked outer failure, with ordinary reply columns

Excluding `causeOf` and `exitOf` answer types would not repair the proposed implication.
An outer host failure can carry the same defect at any error column.

The parent's [second probe](evidence/parent/OuterFailure.lean) uses:

```text
row: request unit, answer unit, error never
root: a definition block with no definitions
main: exit (perform external-row unit)
host reply: failure containing the same defect
```

The signature and block program are admitted.
The body passes `LoopedDataRows`, so it lies inside the body fragment the amendment extends.
The session applies the failure, and `exit` returns its reified value.
The [output](evidence/parent/outer-failure.log) is again `some (0, true, [2048])`.
Here the second field checks equality with the expected reified exit, rather than repeating the descendant search.

This also exposes an internal inconsistency in the proposed predicates.
`BudgetSafeExit` skips defect payloads, but reifying that exit makes `BudgetSafeVal` inspect them.
The specified property therefore fails to pass through an allowed `exit` node.

### Required correction

Keep the general context and host quantification on the local relations.
Replace the false value-safety implication before placing its proof obligation.

The least disruptive candidate keeps defect contents opaque to the program.
Source inspection found no current term operation that extracts a defect payload.
`Reason.error?` skips defects, and `queryError` extracts typed failures only.
Record and list operations cannot open the reified failure's constructor shell.
See [Machine/Term.lean](/Users/pooks/Dev/lean4-effect4/src/Effect4/Machine/Term.lean) and [Machine/Cause.lean](/Users/pooks/Dev/lean4-effect4/src/Effect4/Machine/Cause.lean).

This supports an accessibility-based invariant as a candidate. It does not prove that invariant.
The replacement must cover values a supported operation can extract and eventually pass to `provideContext`.
Its closure obligations include terms, cause queries, reification, native stores, service values, captured environments and restoration frames.
The [consumer receipt](evidence/consumer-build/review.md) records the inspected access paths and limits.

Two other routes remain possible:

- Check actual reply values, including defect payloads, under an explicitly restricted session contract.
- Generalize the scheduler relation to contexts that change the budget.

The first route changes the admitted scope. Existing `preflight` does not provide that guarantee.
The second route requires the larger scheduler proof already discussed in the previous review.
Do not present either route as established by the proposed column filter.

The machine proof also needs the corresponding value invariant on reachable stores, environments and saved contexts.
`DefaultBudgetCtx` constrains the current context's keys and caches. It alone says nothing about a context hidden in another service value.
This is a required reachability-proof component, not an additional checked runtime counterexample.

## N2 — minor: state the call-instance equation with normalization

The amendment claims that a closed row gives `c.answer = row.answer` and `c.error = row.error`.
Call instances contain normalized columns.

`checkRow_rowBindings` states the exact equation:

```lean
t.answer = (row.answer.instantiate bindings).normalize
t.error = (row.error.instantiate bindings).normalize
```

Its declaration is in [Laws/Program/Typing/Call.lean](/Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typing/Call.lean).

The [parent probe](evidence/parent/TypeClosure.lean) uses an admitted closed row with answer `union nat nat`.
Its checked call answers at `nat`.
The [output](evidence/parent/type-closure.log) gives:

```text
signature admission: ok
program admission: true
call answer equals raw row answer: false
call answer equals normalized row answer: true
```

Use the normalized equation in the proposed admission connector.
Transport membership across normalization using the existing `hasTy_normalize` law where appropriate.

Also specify every recursive child of `ContextFreeTy`.
The attachment lists most composites but omits nominal arguments and the children of `refOf`, `deferredOf` and `fiberOf`.
`Ty.instantiate` traverses all of them in [Program/Ty.lean](/Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Ty.lean).
The probe confirms that instantiation changes `app Foreign [var 0]`.
Use the generated type algebra for an exhaustive definition.
This correction does not repair N1.

## F2 and F4: corrections confirmed

The scheduler thresholds now distinguish two claims:

- `1 < budget` permits delivery of the resumed yield continuation.
- `2 < budget` permits a positive local-step bound after that delivery.

The earlier scheduler controls remain applicable at the unchanged source pin.
The amendment correctly retains receipt-conditioned `flush_Myield` for finished-session agreement.
No proof of general progress follows from that receipt.

The proposed `compilesBlk_root` supplies the missing root connection.
`Point.child` preserves the environment and parameter stack, appends the child address, and decreases fuel.
The wrapper therefore needs no additional empty-environment premise.

Correct the helper name `compileEff_zero` to `compileEff_at_zero`.
State Stage 2's empty-context specialization, then generalize it in Stage 4 with the other local relations.
Keep `ParamsAgree` at the invocation's current context, as the amendment intends.

The [proof-structure receipt](evidence/block-meaning/report.txt) records this source review.
The new wrapper and context-general proofs are proposed, not compiled declarations.

## F3: retain the lifetime correction and make acceptance explicit

Stage 5's per-request service lifetime resolves the earlier recorder-capture issue.
The deferred server-lifetime design names both required changes: a shared row proxy and persistent replay with a session-composition goal.
Those deferred changes do not block the per-request Stage 5.

Describe `H9Blocks` coverage as prospective.
The current checker still reaches the bare-entry builder through `Todo.builtAt`.
Stage 5 must connect the new consumer builder before claiming that the checker runs the service consumer.

Add the complete cache sequence to the existing behavior check with a matching Lean consumer:

```text
list, list, add, list
repository calls: all, insert, all
```

The TypeScript `cachedListAfterAdd` runs that sequence.
The current Lean `listAddList` omits the repeated read, and the host runner does not select the TypeScript composite.
This is an acceptance-detail correction, not another lifetime defect.

The [retained runtime probe](evidence/consumer-build/consumer-probe.ts) executes the actual composite against the pinned generated service.
It returns two empty lists, the inserted item, and a final list containing that item.
The calls are exactly `all`, `insert`, `all`.
This is a finite Bun 1.4.2 / Effect 4.0.0-rc.112 result, not a Lean agreement theorem or a TypeScript typecheck.

All four concrete to-do external rows pass the proposed column restriction.
The [table probe](evidence/consumer-build/table-probe.py) checks only constructors present in that table and refuses an unexpected constructor.
Apply the restriction to the external `RowTable`. Native Ref templates are outside that table.

## Verification and reproduction

Run the Lean probes from `/Users/pooks/Dev/lean4-effect4`:

```sh
LEAN_NUM_THREADS=3 LAKE_CACHE_DIR=/tmp/proc6-v5-review/lake-cache lake env lean -DwarningAsError=true docs/research/2026-10-14-proc6-v5-review/evidence/context-scheduler/Bridge.lean
LEAN_NUM_THREADS=3 LAKE_CACHE_DIR=/tmp/proc6-v5-review/lake-cache lake env lean -DwarningAsError=true docs/research/2026-10-14-proc6-v5-review/evidence/parent/OuterFailure.lean
LEAN_NUM_THREADS=3 LAKE_CACHE_DIR=/tmp/proc6-v5-review/lake-cache lake env lean -DwarningAsError=true docs/research/2026-10-14-proc6-v5-review/evidence/parent/TypeClosure.lean
bun docs/research/2026-10-14-proc6-v5-review/evidence/consumer-build/consumer-probe.ts
python3 docs/research/2026-10-14-proc6-v5-review/evidence/consumer-build/table-probe.py
```

The retained runtime directory links `node_modules` to the application's installed dependencies.
The generated service bytes are unchanged. Only the scratch consumer's import paths are adapted.
An initial retained-directory run resolved an unrelated Effect 4.0.4 package and failed.
The explicit dependency link corrected that test environment; the repeated probe produced the recorded rc.112 result.

The Lean probes use existing compiled imports at the reviewed source pin.
No production implementation changed, so no new whole-tree build or behavior-gate sweep ran.
No new universal proof or whole-tree axiom audit is claimed.

The plan and source hashes remained unchanged during the review.
The only reported Git status entry remained the pre-existing untracked `tools/view/make_videos.py`.

**Verdict: rework.** Replace F1's false recursive-safety bridge, correct the normalized column equation, and retain the accepted F2–F4 revisions.
