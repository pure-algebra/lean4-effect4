# Probe of deferring the five Queue typing goals

Recommendation: permit a wrapper with explicit checked typing evidence, while retaining all five original goals.
Do not make their universal proofs a prerequisite for a concrete application or a wrapper theorem conditional on exact certificates.
Require those proofs before promising that every `MessageTy` receives a typed wrapper without further checking or refusal.
This is a source review at `368e0314031cdc2376c38d5738bcb3cde4d099e0`, not a new Lean proof.

## What the existing consumer requires

`step_keeps_cell` in `src/Effect4/Laws/Modules/Queue/Steps.lean` requires this exact equality:

```lean
termTy sig (capturedTypes ++ [cellType]) body =
  some (.prod replyType cellType)
```

The equality concerns the actual elaborated body, signature, captured type environment, cell type, and reply type.
The consumer also requires `sig.atomOf = nativeAtomTy`, a typed captured value environment, a cell lookup, cell membership, and the actual evaluation.
A typing certificate discharges only the equality premise.
The existing `refModify_typed_step` in `Laws/Program/Typed/ListFold.lean` additionally supplies successful evaluation from typing and membership.
Use that theorem when the wrapper needs totality of this one synchronous store step.
Neither theorem proves scheduler progress or notification delivery.

The five planned goals provide that equality indirectly through `typeAt`, for fixed argument-name environments.
`typeAt` also checks source elaboration.
A small connector can recover the elaborated term, its elaboration equation, and its typing equation from a successful `typeAt` result.
Reuse `Option.bind_eq_some_iff` and the existing source result; do not introduce another checker.

## Where the proposed argument can fail

1. A successful `#guard` is not a named proof that a wrapper theorem can consume.
   The existing battery checks 27 types, but it exports no certificate for each checked body.
2. A proof for one type and canonical scope does not automatically type the actual wrapper body.
   A loop can supply an expression over its counter where the original goal uses a named variable.
   Extra bindings and renamed arguments also change elaboration.
3. `termTy_weaken` in `Program/Typing/Rules.lean` transports the actual weakened term.
   It does not prove that arbitrary source re-elaboration produces that term, nor does it substitute arbitrary caller expressions.
4. `Signature.termTy_congr` in `Laws/Program/Signature.lean` requires equality of both `atomOf` and `constAtom`.
   A native certificate alone does not establish the original goal for every signature satisfying only the atom premise.
   Queue's canonical bodies contain no direct string literals, so a specialized independence proof may close that gap.
   This review does not refute the original goals.
5. `MessageTy A` does not supply one of the five typing conclusions.
   A certificate factory may check an arbitrary runtime `A` and return proof on success.
   Without the universal proof, it may refuse; its total success for every `MessageTy` remains unproved.
6. Core term typing is not program admission.
   The 27-type list includes `.int`, while `admitProgram` separately enforces the application's integer restriction.
   Preserve formation, profile, world membership, and whole-program admission as distinct requirements.

## Smallest useful certificate route

Keep the existing equality as the wrapper law's proof parameter, indexed by the actual body and context.
For a closed application, prove the exact checker equation with `by decide`, then pass that proof.
This uses kernel reduction and does not need the universal Queue goal.
It still needs an actual build, axiom output, and goal-dependency check; none was run here.

For dynamically supplied type data, a dependent match or `if h : checkerResult = expected` retains the proof in the successful branch.
This is already the pattern of `checkTypedProgram` in `Program/CheckedTyping.lean` and `admitProgram` in `Program/Admission.lean`.
Use the existing whole-program certificate from `Api.Author.build` for the application.
Only add a local body-evidence adapter if the Queue invariant needs that exact body judgment.
Do not create another public typing representation or a second admission path merely to postpone the goals.

`candidate.lean` shows this shape and a concrete positive and refusing example.
It is explicitly uncompiled and establishes no new theorem.
The prototype indexes the evidence by the original term; the source-to-term connection remains separate and explicit.

## Shared route to the general proofs

The remaining work is compositional checker calculation, rather than a missing semantic soundness theorem.
Use these small dependencies instead of five full expansions:

| Step | Existing reuse | Small remaining result and consumer |
| --- | --- | --- |
| Canonical record shapes | `offerTy_normal`, `cellTy_normal`, `cellFields_normal`, `cell_msgsTy`, `MessageTy` | Field-type and same-field overwrite equations for the Queue cell, taker, and offer; used by every pass |
| Native calls | `NativeAtom.Scheme.apply`, `Ty.matchTemplateArgs`, `termTy_app`, `Ty.sub_refl`, `Ty.subN_refl`, `Ty.join_self` | Typed equations for the actual list, option, pair, Boolean, and identity calls used by the steps |
| Checker composition | `argsTy_cons`, `termTy_record_inv`, `termTy_fold_inv`, existing checker definitions | Introduction equations for record construction, field/update, and folds; current fold rule is inversion, so it does not construct a successful check |
| Binders and contexts | `termTy_weaken`, minted-variable reading, `Authoring.foldWith` scope laws | One typed fold-builder connector, preserving outer terms under both new binders; distinguish weakening from arbitrary substitution |
| Queue passes | The same helpers used by `Reading.lean` and the actual Queue builders | Type `removeTaker`, `removeOffer`, `renewHint`, and `gained` once; compose them into the five original statements |

Keep these helpers under `store-typing`, R4.
Each names its original Queue typing goal and its concrete consumer.
Use the existing rule banks only when an actual second proof consumes the rule.
No new generic proof framework is required.
For arbitrary source callbacks, retain a typed capture premise under both fold binders.
Alternatively, prove the canonical Queue bodies directly; neither route may assume arbitrary callback stability.

## Acceptance controls for the certificate route

| Control | Required observation |
| --- | --- |
| Actual native `.nat` wrapper body | Certificate exists; the wrapper's local safety proof uses it without an open Queue goal |
| A union or named-record message type | Certificate belongs to that exact type and body; reuse of the `.nat` proof must not type-check |
| Request identity changed to `.nat` | No body typing certificate |
| Offer hint given the taker's answer type | No body typing certificate |
| Offer message changed from `.nat` to `.string` in a natural-number cell | No body typing certificate |
| Noncanonical or malformed declaration | Preserve the existing refusal or normalized result; do not certify the original requested type |
| Added prefix binder or loop-counter expression | Check the actual body, or provide the exact weakening/elaboration connector |
| Changed body or reply type after certification | The old certificate cannot inhabit the new indexed proposition |
| Wrapper calls a planned typing goal | Dependency output exposes that goal; the result cannot be reported as independent of the deferral |

The wrong identity, hint, message, noncanonical, and malformed cases already have finite counterparts in `Test/Program/QueueSteps.lean`.
New certificate controls must retain actual proof terms and verify their dependencies.
The proposed controls above were not executed in this review.

## Retained evidence and status

`Test/Program/QueueSteps.lean` is byte-identical to its checked `777d831e` version.
Its source declares 27 message types and guards all six typing checks over that list.
The retained `build-t1.log` records that module building and the 949-job default build succeeding.
The retained ToolResult also reports exit zero.
The log keeps semantic and test axioms within `[propext, Quot.sound]`.
This validates the reported finite battery, not the proposed certificate definitions or the five universal statements.

At this cut, `queue-steps-agree` is proved under `translation-simulation`, R10.
The five typing declarations remain R4 planned goals in the existing generated report.
`queue-expansion-agrees` remains an open part of R10.
A conditional wrapper proof may be proved without using the goals, but its certificate premise must stay visible in its claim's scope.
A concrete application may then discharge that premise with a closed proof.
Do not erase the five goals, turn them into assumptions, or rename a conditional result as their completion.

## Decision

Proceed with exact evidence for the first real wrapper application, while building the shared typing connectors alongside it.
Freeze the wrapper's accepted scope explicitly: checked applications, or every `MessageTy` without refusal.
Only the latter requires the five universal guarantees before that public promise is made.
