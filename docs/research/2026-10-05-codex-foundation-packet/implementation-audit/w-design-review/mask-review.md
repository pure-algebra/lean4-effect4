# Review of the saved-mask proposal

Accept the saved Boolean as a possible mask expansion. Specify its profile support and TypeScript printing design before dispatch.
The representation does not itself require an amendment to row 227.
Supporting a restore that outlives its mask does require that amendment.
The source supports that amendment for recognized restore uses; escape itself does not invalidate the Boolean encoding.

Proof role: contract and implementation-design review.
Evidence status: source inspection; no build, runtime probe, or proof.
Scope: waiting-design F4, its F3/F5 waiting claims, decision 227, and the current program printer and reader.
Reviewed commit: `27ea7cb246191ccdec20ca4819446b2546084118`.
Also inspected the live draft changes made during review; they explicitly request the escape amendment.

## 1. The Boolean can represent the dynamic activation

The proposed getter runs at mask entry and supplies the existing `bind` environment.
Each execution therefore receives its own saved value; the value is not a compile-time choice.
`Decision.bool` binds no extra argument and selects its first arm on true.
Thus the proposed restore chooses `interruptible e` for an interruptible caller and `e` for a masked caller.
This matches the two wrappers selected by rc.112's `uninterruptibleMask`.

Existing `FrameFiber.uninterruptible`, `interruptibleRegion`, and `Prim.ensure` in `src/Effect4/Machine/Frames.lean` supply the relevant restoring frames.
`actionAt` in `src/Effect4/Program/Compile.lean` compiles the existing mask constructors through those actions.
The getter, its Boolean answer, and the new form still need their typing and semantic connections.

Nested masks must resolve the saved variable by lexical binder, not by the nearest active mask.
Repeated execution must read again at each entry.
The admitted form must keep its following continuation outside `uninterruptible body`.
The existing binder signature supports that arrangement: `bind` binds only in its second argument.

The source basis is `uninterruptibleMask`, `uninterruptible`, `interruptible`, and `setInterruptible` in `vendor/effect-4.0.0-rc.112/src/internal/effect.ts`.
The installed 4.0.1 `src/internal/effect.ts` selects the same identity-or-interruptible wrapper.
This inspection supports the wrapper choice; it does not establish equal observations under arbitrary schedules or equal step counts.

## 2. Escape refusal is feasible, but ordinary Boolean typing cannot provide it

The live F4 correctly acknowledges that a fork can retain the saved value after the enclosing mask exits.
A Boolean remains valid data there. That fact does not satisfy the ratified restriction on restore lifetime.
The latest proposal explicitly requests an owner amendment; it is not an undisclosed contract change.

Without an amendment, use a checked, restricted form with these rules:

1. Recognize the entire getter-binding and masked-body expansion.
2. Allow the saved variable only in recognized `select saved .bool (interruptible e) e` restore sites.
3. Reject returning, storing, aliasing, or passing that variable through other operations.
4. Reject its use in a fork or retained body that may run after the enclosing mask exits.
5. Track nested saved variables by their lexical levels through every profile-supported binder.

The branch equality in rule 2 is program syntax equality, checked under the same environment.
A plain `onExit` body need not be refused merely because it is a child field.
A stored scope finalizer or fork needs its own lifetime justification before capturing the saved variable.
For an initial checker, conservatively refuse such captures rather than infer termination or joining behavior.
Noncapturing forks need not be refused by this particular rule.

This gives an exact checker for an explicitly restricted syntactic profile.
It does not decide every program whose restore happens to stay within the mask at runtime.
Apply the checker at admission of the canonical `Eff`, not only in the convenient authoring function.
Otherwise direct construction, decoding, or another expansion could bypass it.

Escape is semantically plausible for a stronger reason than Boolean memory safety.
Both inspected releases select `identity` or the global `interruptible` combinator at entry.
That chosen function does not retain a parent-fiber activation to consult when called later.
An escaped call therefore applies the selected wrapper to the fiber executing that call.
A child retaining the saved Boolean selects that same wrapper on its own execution.

Recommendation: permit recognized escaped restore if the owner accepts the stated amendment.
Do not retain the lifetime refusal solely for the printer. TypeScript can capture the lexical restore callback in a child body.
Keep the restriction against arbitrary saved-Boolean uses; those have no public mask-callback spelling.
The implementation must carry the saved value through the existing child capture relation, not substitute the child's entry flag.
Until that relation covers the new form, the checked profile may conservatively refuse the unsupported capture.
The Queue sketch needs only local restore, so this additional profile need not delay its first path.

This is source-supported wrapper agreement, not a proof of whole-program agreement or arbitrary retained-code support.
Parent exit, child mask changes, nested masks, and both saved values belong in the capture acceptance cases.

## 3. A form-table row does not yet supply the proposed public spelling

F4 says the form table prints the expansion as `Effect.uninterruptibleMask((restore) => ...)`.
That route does not exist in the current code.

`Forms.Template.expand` in `src/Effect4/Codegen/Forms.lean` expands authoring and foreign forms into core `Eff`.
It does not recognize a core expansion while printing it.
Its present template alphabet also lacks the proposed getter, mask, and selection cases.

`print` in `src/Effect4/Codegen/Print.lean` uses the constructor table in `src/Effect4/Codegen/Templates.lean`.
`Row.selects` classifies the current constructor; it does not match a multi-node mask expansion.
The printer visits the `bind` child and would encounter the refused getter before any proposed fusion.
The current reader reverses those same constructor rows.

Specify a checked recognition and rendering route before calling this one small form addition.
That route must replace only recognized restore selections with calls to the callback's restore parameter.
Printing the saved Boolean as that function parameter and keeping the ordinary Boolean conditional would be wrong.
An arbitrary Boolean use has no corresponding public callback argument and must be refused in this route.

Keep exactness explicit:

- Either read the public spelling back to exactly the profile-supported expansion.
- Or declare the normalizer and prove the new reader/printer equations modulo that normalizer.

Do not silently weaken `read_print` or `read_exact` in `src/Effect4/Laws/Codegen/ReadPrint.lean` and `src/Effect4/Laws/Codegen/Read.lean`.
Nested masks, outer-restore use inside an inner mask, and binders inside each branch are required cases.
The scope literature motivates these boundaries; it does not require two additional core constructors.

The extra getter and selection also add executable steps.
A native public mask spelling erases those steps.
The target relation therefore needs its observation and scheduling premises; syntactic round trips alone cannot supply it.
Pending interruption, an automatic-yield boundary before masking, and a small work budget remain acceptance cases.

## 4. The wait is interruptible only under the incoming-mask premise

F3 says a receiver stays in an interruptible wait until its task runs.
F5's cancellation table repeats that guarantee.
Under an already-masked caller, F4 deliberately selects identity, so this guarantee does not follow.
The await can remain masked; an interruption request need not withdraw the Queue request.

Use this wording:

> For an interruptible incoming caller, restore makes the await interruptible. Cancellation withdraws the request if withdrawal wins before consumption.

Keep the already-masked case separate.
It may remain waiting despite an interruption request, or consume after a later signal while interruption remains pending.
This is a source-derived case to cover, not a new executed counterexample.
The later F5 caveat about pending interruption improves the draft but does not qualify its unconditional waiting sentence.

## Placement before implementation

| Obligation | Placement and consumer | Premises and observation | Exclusions and prerequisite |
| --- | --- | --- | --- |
| Saved-state restoration | Existing proposed `saved-mask-restoration`; scope-lifetime-finalization, R11; waiting wrapper and protected permit | Admitted lexical form, dynamic environment, all exits; interruptibility, pending cause, and continuation | No progress or Queue atomicity result; settle escape profile first |
| Captured restore, if admitted | A clause of saved-mask-restoration and the R10 form agreement; compiler capture connection, then forked clients | Owner-amended profile, recognized restore uses, unchanged lexical saved value, existing admitted fork; wrapper chosen and executing fiber's mask observed after parent exit | No arbitrary retained code, services, or liveness; first specify capture admission and the printer route |
| Scoped boundary | Existing `scoped-body-substitution-boundary`; residual-program-typing, R4; form elaboration and compilation | Binder signature and checked capture positions; following code stays outside the mask | No scheduling agreement; freeze recognized expansion and capture checker |
| Public spelling | R8 reading/printing claims and R10 form behavior; printed Queue consumer | Recognized form, exact expansion or named normalizer; syntax equation separate from runtime observation | No arbitrary getter profile support; specify printer/reader route and step relation |
| Cancellation premise | `waiting-request-obligation-preserved`; reactive-scheduling, R11–R12; Queue wait | Incoming interruptibility and winning withdrawal; commitment and return remain separate | No cancellation of masked waits or eventual progress; qualify F3/F5 and retain masked-caller control |

## Verification

Read the mask implementation, existing frames, binder signature, form expander, printer table, reader, and their exactness statements.
Reused the retained scope and task literature notes; performed no new literature search.
The companion receipt hashes the pinned inputs and the live draft and records the source assertions.
Initial lookups used several obsolete paths and returned exit 2; the reads above use paths found by `rg --files`.
No builds, generators, installs, runtime probes, or active-repository edits ran.
