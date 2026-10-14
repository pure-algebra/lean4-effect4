# PROC-6 scheduler and context review

The coordinator must distinguish conditional agreement from progress. Small budgets can prevent a terminating local program from completing on the machine. This does not refute H9Blocks, which assumes an at-rest run with an exit.

## Pins and scope

- HEAD: 9ccb94e2b8349f72dae884328e84cf25582c95c4.
- Branch: refactor/phase1-phase3.
- Read-only repository review. Temporary probes only in this directory.
- Placement: refutation probes serve proposed rows-block-host / translation-simulation / R6, specifically the proposed context and scheduler extension. No production lemma was introduced.
- The scout changed during review: the initial read required arbitrary budgets; the later fourth version replaces that with a proved default-budget invariant and context-source restrictions. The coordinator must pin the final reviewed bytes.

## Checked finite probes

Command: LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.Agreement.Machine
Result: Build completed successfully (353 jobs). This validates import freshness for Probe.lean.

Command: LEAN_NUM_THREADS=3 lake env lean /tmp/proc6-review-20261014/context-scheduler/Probe.lean
Result: accepted, no errors. Output: probe.log.

The probe starts the actual frame evaluator at success unit, empty stack, op count zero. After initial drive and twenty flush rounds:

- budget 0: no completed exit; flush receipt false; stack length 21.
- budget 1: no completed exit; flush receipt false; stack length 21.
- budget 2: one completed exit; flush receipt true; empty stack.

The positive control at budget 2 starts fresh. It does not show progress after an existing yield.

`iteration` first counts the operation, then calls `injectYield` (Machine/Fibers.lean, iteration and countOp). At budgets zero and one, yield interrupts the success delivery that should pop the previous injected continuation. Every round can add another saved continuation.

`preventYield = true` suppresses injection at budget zero in the same finite iteration probe.

## Q4: arithmetic and scope

Source: src/Effect4/Laws/Program/Agreement/Machine.lean, fire_Myield; src/Effect4/Laws/Program/Agreement/Segment.lean, flushAll_Myield and replay_Mexit_of_localRun.

1. fire_Myield needs the resume answer to pass without reinjection: 1 < budget.
2. Strict original-program progress after that resume needs 2 < budget. A new segment starts at count one. At budget two, its first counted checkpoint is already a yield. Therefore l=0 satisfies budget <= 1+l+1. The pasted review's inference from 2 <= budget to 1 <= l is invalid.
3. Budget 0/1 finite starvation does not refute proposed H9Blocks: that statement assumes funded, atRest, hostDriven and an actual exit. Preserve those conditions. It does refute an unrestricted local-exit-to-finite-replay theorem.
4. preventYield removes scheduler cuts. Segment termination bounds must then follow the supplied local-step bound or receipt, rather than a fixed scheduler budget. No liveness claim follows from the flag alone.

The default-budget recommendation is a scope change from the initial plan. It becomes valid only after closing every context source. SigApp.serviceTy refuses reserved names, but raw BlockRows has no checker premise. Also ServicesFit only constrains values at declared keys and requires every value to be live. It does not itself exclude reserved keys. The finite probe confirms that adding Env.maxOpsKey -> nat 1 gives budget (1,false), while SigApp.serviceTy {} Env.maxOpsKey = none.

The fourth scout now explicitly restricts reserved service operations and context-bearing host replies. This closes the obvious missing-source argument in the pasted review, but requires a real fragment rule and structural proof over nested answer types. It is not a three-line provideService preservation lemma.

The fourth scout still says ParamsAgree and CompilesBlk quantify every context. DefaultBudgetCtx cannot be inferred for arbitrary starting contexts. Either keep local relations general and apply the invariant only to reachable hosted states, or constrain precisely the machine-side lemmas that use it. Proving an invariant from emptyCtx does not prove it for an arbitrary ctx.

## Q3: context state, defaults, and frame masks

Source: Machine.lean fiberAt / M / parkedAt / Myield; Agreement.lean localStep and step_ofExit_pass_setInterruptible; Compile.lean updateContextAt / updateThenK / contAOf bodyThen / actionAt / finalizerProgram.

Context must survive each host-call and scheduler boundary. setContext changes the fiber context and cached budget fields. restoreCtx reads the captured previous context after the body. A read-only argument cannot represent these transitions.

Trailing default parameters can preserve the elaboration of old empty-context call sites. They do not generalize any theorem. In particular, fiberAt currently takes only fr and k; M takes fr,s,k,tr,nt. The pasted review's sample M root ... is not the current declaration. Old proofs remain proofs about the default context unless their quantified statement and result forms are changed. The fourth scout correctly acknowledges this.

The physical mask finding is correct. The finite probe checks PlainFrame (setInterruptible false) = false and checks that masking followed by interruptibleRegion produces stack [setInterruptible false, setInterruptible true]. Frames.lean uninterruptible, setFiberInterruptible and interruptibleRegion implement this explicitly.

The full context-region stack follows Compile.lean's bodyThen and restoreRegion source route:
setInterruptible false :: onExit _ (restoreCtx previous) false :: setInterruptible true :: K.

Changing the mask case alone is insufficient. PlainCode / PlainFrame must also admit restoreCtx finalizers, restoreRegion thunk bodies and the new continuation names. Existing plainFrame_onExit and plainCode_onExit conclude n = fin p, so they must be restated or split. The specific exit-pass lemma lives in Agreement.lean, not at the pasted review's cited Machine.lean location; it currently hard-codes true. Its success/failure helper lemmas also specialize true and must be generalized consistently.

The pasted review invokes a predicate Plain with interruptedCause = none. No such named Plain predicate appears in the current Agreement sources. fiberOf builds a cleared frame directly; use that actual invariant rather than an unlocated predicate.

## Q6: what is proved

Source: src/Effect4/Laws/Program/Typed/Context.lean.

- checked_context_arm requires the exact source node and checker action result, equality of service tables, and Row.Subset keys available. It establishes AmbientProg; it does not assert an unconditional reachable-fiber invariant.
- native_context_answer requires ServicesFit w f.context.services, f.context.services.Satisfies available and ambientFiberPre. Its conclusion gives the actual getter answer and ambientFiberPost.
- ambient_captured_context extracts ServicesFit and the guaranteed service row from a supplied typed completion.

Source: Typed/Membership.lean ServicesFit and fits_context_inv. Fits at Ty.context requires ServicesFit; this condition includes liveness for entries even at undeclared keys. A dangling handle in any service value need not fit.

Source: Typed/Commands/Clauses/All.lean reachable_typed. Reachable typing requires a checked program, a closed root requirement row and AdmittedTape. It concerns the reference replay; the native connection is through the named simulation/equal-observation relation and its scope. Source: Typed/Assembly.lean machine typing reads the fiber context's ServicesFit through its owner predicate.

Verdict: the conditional getter result is present. 'Every context the fiber can hold' is too broad unless the statement explicitly means contexts of reachable typed runs under these premises. Raw block-host agreement alone supplies none of these typing assumptions. Q6 is not evidence that arbitrary context payloads or host answers preserve typedness, scheduler defaults, or native M5 initialization.

## Minimal corrections

- Keep H9Blocks receipt-conditioned; state any separate progress theorem with an adequate scheduler premise and test budgets 0,1,2 and preventYield.
- If adopting the fourth scout's default-budget route, make its fragment/reply exclusions explicit and recursive. Prove the invariant from emptyCtx, including provided contexts and restoration. Do not claim it at all contexts.
- Keep the context in the hosted state and outcome forms; defaults only ease old call sites.
- Generalize both mask flags and every context finalizer/continuation closure lemma together.
- Restate Q6 with ServicesFit, coverage and reachable-typing premises; keep its host boundary separate.

## Fourth-version snapshot and host-choice follow-up

The intended snapshot is /tmp/proc6-review-20261014/scout-current-snapshot.md, SHA256 f100b80cdbcbcfe0237dd63d8309e64f48fc8fc6ebff352a56c07af542689705. Stage 4 already proposes refusing reserved-key service operations and either excluding context-capable row answers or filtering replies. The assessment above does not treat these proposed corrections as absent.

The new owner attachment confirms this version is the intended review. Its claim that the invariant is exact remains proposed until its context sources and scope are proved.

A second finite probe starts on an already-yielded fiber at budget two. Twenty flush rounds give zero exits and a false receipt, retaining one saved frame. This strengthens the arithmetic finding: budget two allows the scheduler resume to complete, but never gives the original program a counted checkpoint.

The finite probe also checks externalValue Ty.context [] (Val.context poisonedCtx) is present, while externalValue Ty.nat [] on that value is absent. poisonedCtx binds the reserved maxOps key to nat one and has matching cached budget fields.

Source: Program/Admit.lean admitAnswer performs externalValue at the row's answer type before mintedIn. Program/Typed.lean Val.hasTy accepts every value at unknown; context and contextOf inspect context shape and required keys, without banning scheduler service entries. Thus current reply admission does not prevent an admitted context-bearing reply from setting the budget.

Source: Laws/Program/DenoteRows.lean Column.carrier deliberately maps every reply column to ExitV. The docstring explicitly assigns membership to a protocol, not the carrier. Consequently an arbitrary Effects.Comodel (RowSig table) can return a context at a row declared nat. Excluding context-capable declared row types cannot alone prove a context-source invariant against every raw Comodel.

Source: Laws/Run.lean Run.Reached permits only opening and checked row playback. Run.Basic Rows.answer routes completions through bind, submit and apply. HostSession checks operational reply admission. This provides a route to derive actual applied-reply constraints for final H9Blocks. It does not make raw intermediate Comodels protocol-typed automatically.

Recommendation on the fourth version's open host choice: do not impose a new global reply refusal merely to preserve an agreement proof's fixed budget. Keep either an explicit restricted fragment whose reachable applied replies are proved context-free, or an explicit budget-safe admitted-host condition in the applicable relations. If broader contexts are intended, generalize the scheduler model and retain actual yield/frontier behavior. Any chosen reply filter must appear in the block meaning as well as the executable session, and its compatibility law must be placed before proof work. A type-only exclusion needs recursive capability analysis, including unknown and nested records/lists/unions, plus use of actual admission at the call instance.

## Checkout movement

HEAD moved externally to 7c9bb76172400d2f885cf461f2f09db334d2495a during review. The narrow build ran before this movement. git diff --name-only between the two commits contains no Machine/Fibers.lean, Machine/Frames.lean, Program/Compile.lean, Program/Typed.lean or Laws/Program/Agreement/Machine.lean. The probe exercises these unchanged declarations. No whole-tree freshness or build claim is made for the moved checkout.

Current decisive source hashes:
- Machine/Fibers.lean: d407c4ac87b017fce1d9d00205662b8b4b67653c6a8fd1f9ba8037ba49686410.
- Machine/Frames.lean: 000e664e27e6bde515f14928bd473bbbdbb7d95181b06326efb9a24d3c11153c.
- Program/Compile.lean: 2ea5f8cdb249e2ace29615ee43e027605cb3bb50271f37e12c553b0910026de1.
- Laws/Program/Agreement/Machine.lean: 309b0e82a8c96d48de38117c2d50de039e4946817855e8f524efe1c4516e557f.

## Final scheduler route sanity check

The parent's proposed general-context route is consistent with conditional H9: holds_flush / flush_Myield can recurse on a successful finite round receipt without asserting positive local progress. Keep flushAll_Myield's completion bound as a default-budget corollary.

A zero-local-step yield case alone does not complete the generalization at budgets zero and one. fire_Myield no longer normalizes to the original instruction at count one. The machine accumulates injected onSuccessConst continuation frames before the prior frame can pop. The segment and settled relations must represent or erase these scheduler administrative frames explicitly. At budget two the normal resume completes, then the original program takes zero steps before yielding again. Both cases are permitted stuttering; neither proves eventual completion.

Final finite output appended to probe.log:
- already-yielded budget two: (0 completed exits, false, some (1 stack frame, 3 operations)).
- externalValue at context for scheduler-changing context: true.
- externalValue at nat for that context: false.

No repository source edits, no commits and no whole-tree build were performed.

## Essential admission-scope correction

The externalValue Ty.context probe is a value-function test only. It does NOT show a legal application row with answer Ty.context. Program/SigApp.lean rowChecks rejects internal handles recursively through findInternalHandle, including context and contextOf. dataRow itself rejects a top-level handle, and Ty.context is a handle alias. Retract any reading of the earlier wording as evidence of an admitted explicit context-typed row.

Checker.provideContext (Program/Checker.lean) requires the supplied term's normalized type to be contextOf keys. A context carried under unknown cannot directly feed that rule. Therefore accepted unknown payloads alone do not establish a typed reachable scheduler change.

A separate polymorphic path remains to be checked before declaring the typed fragment safe: a legal external row with request var 0 and answer var 0 can instantiate at contextOf empty when called with the result of Effect.context. The raw answer column var 0 contains no internal handle, is inhabited under admitRowColumn, and is nonallocating. Program/Admit.lean admitInstance checks the instantiated answer's Val.hasTy and absence of handles. It performs no recursive internal-handle or reserved-context-key scan at the instance. The context payload used by the value-function probe has no handles. If the checker accepts that call instance, its reply can carry the reserved scheduler entry and its contextOf result can feed provideContext. This route is source-grounded but not yet compiled as a whole admitted-program witness; do not report it as an established reachable counterexample until tested.

The raw BlockRows/arbitrary-Comodel concern is independent: its RowSig answer carrier is ExitV without membership, so the raw universal theorem needs its own explicit host protocol or a general scheduler relation. Checked H9's Run.Reached premise supplies operational admission, but one must analyze instantiated polymorphic replies as well as raw row types.

## Decisive admitted polymorphic counterexample

The previously suspected polymorphic path is now checked as an actual admitted session. AdmissionBoundary.lean imports Effect4.Run, Effect4.Api.Author and Effect4.Program.Typing.Call.

Witness:
- legal external identity row: request var 0, answer var 0, error never;
- program reads Effect.context empty;
- calls the identity row with that context;
- supplies the returned context to provideContext around sync unit;
- host replies with a context containing maxOpsKey -> nat 1.

Results, in admission.log:
Except.ok ()       -- signature admission
true               -- program has an inferred type
true               -- admitProgram accepts
true               -- actual call instance answers contextOf empty
some (0, 19, [(1, false, 1)]) -- checked session: no outstanding call, fiber and context budgets become 1

The program uses no reserved-key service operation. The raw row columns contain no internal handle. The actual call instance supplies contextOf empty. Api.Author.Internal.finishBuild constructs Api.Built from admission; Run.open/control starts it; Run.answer goes through checked bind/submit/apply. The resulting actual fiber and context both hold maxOpsBeforeYield one.

Freshness at HEAD 7c9bb76172400d2f885cf461f2f09db334d2495a:
LEAN_NUM_THREADS=3 lake build Effect4.Run Effect4.Api.Author Effect4.Program.Typing.Call
Build completed successfully (169 jobs).
LEAN_NUM_THREADS=3 lake env lean /tmp/proc6-review-20261014/context-scheduler/AdmissionBoundary.lean
Accepted, no errors, output above.

This refutes the broad fourth-version premise that admitted programs cannot change the scheduler budget. It also demonstrates that the host clause is necessary even for checked reached sessions, beyond the raw Comodel concern. An answer-column exclusion must account for template variables and actual call instances. A semantic filter on actual supplied contexts or a general scheduler model avoids silently banning every generic row.

No claim is made that this checked run exits, or that it violates typed-state preservation. It demonstrates only the failure of DefaultBudgetCtx in an admitted reached run. The receipt-conditioned H9Blocks statement remains unrefuted.
