# Queue composition proof scout

## Result

Keep the six step goals. Add one atomic-operation connector, then reuse existing sequencing and loop machinery at their stated boundaries.

The smallest authoring improvement is a Queue-private `untilSome` helper using `iterateWith` and `selectOption`.
Its local termination law makes the impossible option arm reviewable without changing syntax or claiming termination.

A source-linear caller of `Queue.take` is not in the current `Straight` fragment.
The expansion uses masking, posting, waiting and iteration, which those fragment theorems exclude.

Evidence status: source review only. Proposed statement shapes below are uncompiled and unproved.
No compiler, runtime, generator or Lean command ran.

## Reviewed state

Main advanced from `6acbf7909eceb253d3bec2e713a5fd2d514846e6` to `09d35eafd4e68ef86916dced39d003fd4cf8fbd3` during review.
The final commit records row 255 and the five approved proposals.
The tree was clean immediately after that commit.
The coordinator began the model relocation before this report finished; those working edits are not accepted here.

The reviewed plan is `docs/research/2026-10-05-claude-lead/queue-readiness/queue-steps-design.md`.
The brief is `docs/research/2026-10-05-claude-lead/briefs/seat-qsteps-brief.md`.
`QueueSteps.lean` beside the design remains a Nat-message research program.
The generic module is planned; this report does not assess it as implemented.

The profile restrictions and ordered notification comparison already have corrections.
This report treats them as premises and proposes no repeated repair.
The abstract model and profile reside under `Test/Program` at the reviewed commit.
The active relocation places them under `src/Effect4/Laws/Modules/Queue`; source hashes distinguish both observations.
Row 255 approves their move into the law graph.

## 1. Connect each term agreement to one actual atomic operation

Proof role: helper for the six step goals and their wrapper consumer.
Concept: `translation-simulation`, R10, proposed `queue-expansion-agrees`.
Typing support: `store-typing`, R4.

Consumer: each wrapper attempt, including attempts inside an iterative caller.
Prerequisite: the step's exact term evaluation goal, its cell relation and its admitted request relation.

Use the relation already planned in the brief.
Let `CellRel enc model cell` relate the abstract state to the whole concrete cell.
Let `StepReplyRel enc reply signals value` cover the reply and every ordered notification.
These names are schematic, not new requested public types.

Proposed statement shape:

```lean
-- Schematic, uncompiled; use the planned relation's actual names.
CellRel enc s cell → FirstProfile s → Requested s op →
refPeek stores.refs q = some cell →
let out := modelStep s op
∃ enc' cell' reply,
  syncOpStep (.refModify q term captured) stores =
    some ({ stores with refs := refPoke stores.refs q cell' }, reply) ∧
  CellRel enc' out.state cell' ∧
  StepReplyRel enc' out.reply out.signals reply ∧
  FirstProfile out.state
```

The model relation must carry the planned injective identity map and current hint map.
It also needs a message-payload relation: the current abstract model stores Nat messages, while the proposed cell admits any supported `A`.
State its mapping from model messages to concrete values, preserving order and multiplicity, with `Fits w value A`.
The Nat-message proof alone does not establish the arbitrary-message theorem.
Fresh requests extend that map; a repeated take replaces its hint and frames other entries.
The term's free inputs must match `captured`, including binder order and the current cell input.
Signals refer to the post-step map, as the design already requires.

Reuse `refStep_modify` in `src/Effect4/Machine/Stores.lean` for the concrete operation equation.
It takes exactly the successful term evaluation into `[reply, newCell]`.
It needs no new store semantics.

Reuse `refModify_typed_step` through `ListFoldRules.step` in `src/Effect4/Laws/Program/Typed/ListFold.lean` for membership.
Its premises are native atoms, a typed captured environment, typed callback, existing cell and fitting current value.
Its conclusion includes evaluation, the actual operation equation, and membership of both result and new cell.

For an arbitrary continuation, reuse `refModify_implements` and `storeStep_typed` in `src/Effect4/Laws/Program/Typed/Adequacy.lean`.
They supply the later world and typed continuation after the actual store operation.
`termMaps_of_typed` in `Typed/Denotation.lean` already handles later worlds and captured environments.

The exact store-update equation frames every non-reference store component.
The existing `refPoke` semantics supplies the other-cell behaviour when the consumer needs that observation.
No new store representation or Queue-specific preservation framework is needed.

Observation: whole Queue cell, exact reply, ordered notifications and the complete concrete store update.
Exclusions: posting, Deferred delivery, mask restoration, cleanup, arbitrary scheduler traces and progress.
A successful atomic operation does not establish any wrapper's delivery budget.

## 2. Hide the option-loop plumbing in a Queue-private helper

Proof role: local helper for normal return of `Queue.take`.
Concept: `translation-simulation`, R10, as a part of `queue-expansion-agrees`.
Cursor-membership support belongs to `store-typing`, R4.

Consumer: `Queue.take`'s retry loop after the saved-mask prerequisites land.
Prerequisite: each successful attempt returns an option of the message type.
The helper must preserve the enclosing cleanup region and restore only the intended wait.

The existing expansion starts at `none`, repeats while `not (isSome cursor)`, and replaces the cursor with the body's answer.
It then selects the present message and retains a defensive defect arm for `none`.

Proposed helper shape, without new syntax:

```lean
-- Schematic authoring API, not implementation.
untilSome (A : Ty) (attempt : Src NativeOp) : Src NativeOp
-- iterateWith none:
--   cursorTy = some (option A)
--   while = not ∘ isSome
--   body = attempt
--   step = body answer
--   result = cursor
-- followed by selectOption of the final cursor
```

Keep it Queue-private until another concrete module needs the same operation.
The public API should answer `A`; authors should not repeat the impossible arm.
The internal arm remains ordinary existing syntax.
Do not introduce a total option extractor, an axiom, or a new binding form.

The first proof is small and local:

```lean
-- Schematic, uncompiled.
Fits w cursor (.option A) →
(NativeAtom.eval .isSome [cursor]).bind
  (fun value => NativeAtom.eval .boolNot [value]) =
    some (Val.bool false) →
∃ value, cursor = Store.Val.some value ∧ Fits w value A
```

Use `fits_option_inv` in `src/Effect4/Laws/Program/Typed/Membership.lean`.
Both atom equations are explicit in `src/Effect4/Machine/Term.lean`.
The `none` case contradicts the false test; the `some` case retains payload membership.

Then connect the law to a normal loop finish at the actual source point.
Use `loopNextRAt`, `loopFinishRAt` and `loopResumeRAt` in `src/Effect4/Laws/Program/InterpR.lean`.
The proof must identify the real loop node and its exact test, step and result terms.
A generic typed loop only proves an option result, not a present result.

The proposed normal-finish conclusion is:

```lean
-- Under the helper's exact loop-node and typed-cursor premises:
loopNextRAt root point cursor = .finish (.pure (.success result)) →
∃ value, result = Store.Val.some value ∧ Fits w value A
```

The point premise must exclude a missing node and tie `result` to the cursor variable.
For a whole-run corollary, use the checked loop-frame invariant to transport cursor membership through resumptions.
Do not substitute the local hook law for the missing whole-run connector.

Reuse `iterateWith_scoped` in `src/Effect4/Laws/Program/Authoring/Loops.lean` for scope.
Reuse `LoopFrameTyped`, `loopEnter_typed`, `loopFrameTyped_mono` and `loopFrameTyped_closed` in `Typed/Commands/Clauses/Loop.lean`.
Those laws cover later worlds and admitted answers without assuming that a loop finishes.

Observation: any normal successful loop exit contains a message, so the following empty arm is unreachable there.
Failures remain failures; a parked wait or exhausted budget remains a frontier.
No theorem here promises eventual success, fairness, resource release or a finite retry count.

Useful eventual controls: initial ready message; one empty attempt before success; failure before success; permanently empty attempts at exhausted fuel.
The latter must remain unfinished, not become the helper's defect.
These are proposed controls, not executions from this review.

## 3. Reuse the existing composition laws on the part they actually cover

Proof role: consumer connectors for atomic scripts; later scheduled wrapper obligation stays open.
Concept: `translation-simulation`, R10, serving `queue-expansion-agrees`; R8 provides existing runtime agreement.

The pure step term runs inside one synchronous `Ref.modify`.
A script consisting of those synchronous attempts can lie in `Straight`.
A bounded script repeating those attempts can lie in `Looped`.
That classification requires checking the actual expanded program, not the source API's name.

`Straight` in `src/Effect4/Program/Fragment.lean` rejects masks, forks, awaits and iteration.
`Looped` in `src/Effect4/Laws/Program/DenoteB.lean` adds iteration but keeps those other exclusions.
The research Queue wrapper contains `uninterruptible`, `withFiber`, parked Deferred operations and iteration.
Consequently, neither `run_eq_meaning` nor `loopAgreement` proves that wrapper's behaviour today.

For admitted atomic scripts, use these existing consumers:

| Existing declaration | Path | Relevant scope |
| --- | --- | --- |
| `runP_bind` | `src/Effect4/Laws/Program/DenoteB.lean` | Sequence from the stores left by the first computation |
| `runP_thenB_none`, `runP_thenB_some` | same | Preserve unfinished status and stored state |
| `iter_congr`, `iter_uniform` | `src/Effect4/Laws/Program/Iter.lean` | Equal free programs, with an explicit cursor map for uniformity |
| `iter_soundB` | `src/Effect4/Laws/Program/LoopSound.lean` | Per-round equality after the store handler, later worlds and a cursor invariant |
| `run_eq_meaning` | `src/Effect4/Laws/Program/Agreement/Machine.lean` | Straight root, empty initial store, sufficient structural fuel, exit and stores |
| `loopAgreement` | `src/Effect4/Laws/Program/Agreement/Loop.lean` | Looped root whose budgeted meaning finishes; sufficient eventual fuel |
| `denoteB_mono_le`, `meaningB_unique` | `src/Effect4/Laws/Program/DenoteB.lean` | Finished meaning stable at larger budgets; exit and stores |

Do not apply `iter_congr` directly to abstract model transitions and concrete Ref operations.
They are not equal free programs and do not share the same state representation.
First establish the planned encoding relation through one operation and its successor state.
A finite script proof then inducts over the script, using `first_profile_closed` after each admitted request.
Use `runP_bind` to connect each concrete store transition.

For a genuinely Looped concrete consumer, `iter_soundB` accepts a stronger per-round invariant.
That invariant should include typed captures, typed cursor, cell relation and the first-profile/request conditions.
Its equal-run premise still concerns the same interpreted concrete store.
It does not by itself compare a separate abstract Queue state to that store.

`StraightEq` in `src/Effect4/Laws/Program/MeaningEq.lean` quantifies over every environment and store.
The planned Queue relation holds only under profile and encoding premises.
Therefore those premises cannot be dropped to package the relation as `StraightEq`.
Use its bind/select/onExit congruences only for an actual unconditional rewrite between admitted straight programs.

The smallest script statement is schematic:

```lean
-- Every prefix supplies an admitted request at the state that prefix reaches.
CellRel enc initial cell → FirstProfile initial →
ScriptRequested initial operations →
ConcreteAtomicScript operations stores = (replies, stores') →
∃ enc' final,
  ModelScript operations initial = (modelReplies, final) ∧
  CellRel enc' final (queueCell stores') ∧
  RepliesRel enc' modelReplies replies
```

Retain every emitted notification as data in this script observation.
This script does not exercise their delivery.
The initial concrete store must contain the related Queue cell and its declared identities.
An `Api.run` corollary must include actual initialization or use an existing local-state theorem with its premises.

Immediate prerequisite: exact six step contracts, the profile closure law and concrete relation.
Observation: ordered operation replies, full cell and whole stores after success or failure.
Exclusions: notification delivery, arbitrary host replies, scheduling, cancellation races and target-language execution.

## 4. Use nested handle freshness for Queue records

Proof role: small helper for fresh request enrollment and the identity-map extension.
Concept: `store-typing`, R4; serves `queue-expansion-agrees`, R10.
Consumer: enrolling a new taker or offerer while retaining every earlier registration.
Prerequisite: allocation of the fresh identity and membership of the pre-allocation cell.

The design cites `HandleIdentityLaws.notMemberDeferred`.
Its underlying `fresh_promise_not_member` accepts a list whose elements are directly Deferred handles.
Queue waiter lists contain records, so that exact lemma does not apply directly to the cell list.

Use `HandleIdentityLaws.freshDeferred`, backed by `sameHandle_fresh_promise`, for nested records.
Its premise is raw-handle membership anywhere inside a value fitting the earlier world.
Alternatively, prove membership of the projected identity list once, then use `notMemberDeferred`.
The nested route avoids building another list solely for a proof.

Proposed local conclusion:

```lean
CellsTyped oldWorld →
syncOpStep .deferredMake oldWorld.state = some (newStores, Val.promise fresh) →
Fits oldWorld oldCell (Queue.cellTy A) →
oldIdentity occurs in Store.Val.handles oldCell →
NativeAtom.eval .sameHandle [Val.promise fresh, oldIdentity] ≠ some (Val.bool true)
```

The handle-shaped `oldIdentity` and its raw pair representation must match the existing theorem's parameters.
Typed record projection gives the stronger exact `false` equation when the comparison needs it.
Use `deferredMake_fresh`, `sameHandle_total_deferred` and `sameHandle_fresh_promise` from `Typed/ListFold.lean`.

Keep freshness relative to the world before allocation.
The new world declares the identity, so the old-world freshness hypothesis cannot be asserted there.
Use `fits_mono` to retain earlier values afterward.

Observation: the new request identity differs from every earlier stored identity.
Exclusions: host-object identity, signal delivery, progress and arbitrary untyped handle data.

## 5. Preserve the existing cleanup and budget boundary

This is a dependency check, not a new repair request.
The current plan already separates step commit, reply delivery, continuation entry and fiber exit.
The step connector above must not erase those distinctions.

The wrapper's delivered-exit observation should reuse `Exit.restoreAfterFinalizer` in `src/Effect4/Machine/Exit.lean`.
`restoreAfterFinalizer_success_finalizer` preserves the full prior exit.
`restoreAfterFinalizer_failure_failure` retains the existing cause combination rule.
A successful cleanup must not reconstruct an interrupt and lose its interruptor.

The planned `waiting-request-obligation-preserved` claim covers the selected request's obligation and stale notifications.
The saved-mask law supplies restoration at region boundaries.
Neither follows from typed atomic steps or the local `untilSome` law.

The delivery budget includes reached receiver continuations, cleanup and pending commands.
The count of posted signals alone cannot supply that bound.
`waiting-design.md` F7 already states this and notes that `straight_sufficient` covers a fresh run only.
Do not import that fresh-run bound as a dispatch-drain bound.

For dogfooding, retain one linear caller and one iterative caller of the same Queue operation contract.
Use the existing scheduled observation for those wrappers, keeping commit, operation exit, continuation entry and final exit separate.
The linear caller tests API composition; it does not certify membership in `Straight`.
A longer receiver continuation with the same Queue state is the existing budget falsifier.

## 6. Specialize acceptance through the existing first-profile closed form

Proof role: implementation simplification justified by an existing model helper.
Concept: `translation-simulation`, R10, within the same take and poll step goals.
Consumer: `takeStep` and `pollStep` after a consuming operation frees capacity.
Prerequisite: every pending offer is nonbatch with exactly one remaining message.

`acceptLoop_single` already proves:

```lean
-- Exact model definition, using its current Nat message carrier.
entered room msgs offers =
  (msgs ++ (offers.take (fit room offers.length)).flatMap (·.rest),
   offers.drop (fit room offers.length),
   (offers.take (fit room offers.length)).map fun o => ⟨o.id, .offered true⟩)
```

For finite `room`, the accepted count is `min room offers.length`.
The proposed source term can derive accepted offers with `take` and pending offers with `drop`.
Only appending their singleton payload lists needs a fold.
The notification decoder can read the accepted entries in order, as the step contract already requires.

The current research `accept` term carries room, messages, kept offers, accepted offers and a stopped flag.
Its consumers read only the messages, kept offers and accepted offers fields.
They re-expand that whole computation at each field use.
A first-profile specialization can avoid reconstructing kept and accepted lists with repeated `snoc`.
It can also avoid the partial-batch and stopped-flag branches in that term.

Keep the six step statements unchanged.
Prove the specialized message/kept/accepted outputs against `entered`, then use `acceptLoop_single`.
There is no need to equate unused accumulator fields or introduce a local-binding constructor.
This follows row 255's existing restriction: repeated pure expressions remain permitted.

The message-append fold must infer its accumulator from the existing typed message list.
Use `take msgs 0` when an empty list is required, as the current reader-domain design already does.
The theorem needs the payload mapping for arbitrary message type `A`; the current model theorem uses Nat messages.

Observation: same cell messages, pending suffix and exact ordered notifications for the first profile.
Exclusions: partial batches, rendezvous, other strategies, terminal operations and wrapper delivery.
No AST count or execution-time measurement ran for this candidate.
Smaller syntax and fewer traversals are hypotheses until the owning seat measures the actual emitted term.

## Landing order

1. Land the approved model relocation and six term goals under the coordinator's ownership.
2. Connect each successful term result to the actual atomic operation using the existing store theorems.
3. Consider the first-profile acceptance specialization while proving those unchanged step statements.
4. Prove the small normal-finish option law when the retry helper has its concrete consumer.
5. Keep the helper private until another reached module needs it.
6. Add the finite atomic-script connector using the existing profile closure and sequencing laws.
7. Keep scheduled wrapper agreement, saved masks and delivery budgets as separately measured obligations.

No broad abstraction, new loop syntax, or general theorem framework is required by these findings.
