# Two Queue decisions, probed

Recommend the narrow target-helper repair and checked evidence for the first real wrapper applications.
Keep the five general typing goals open.
Automate the repeated evidence work through the existing compiler and authoring tools.
These are recommendations, not a recorded owner ruling on either policy.

The source review freezes main at `368e0314`.
The compiler probes use tsgo `7.0.0-dev.20260629.1` and Effect `4.0.0-rc.112`.
No active repository changes, Lean commands, application execution, generators, or installations occur.

## 1. TypeScript primitive slots

The current helper can make an ordinary Boolean choice too narrow:

```typescript
ite(flag, pair(true, 0), pair(false, 0))
```

The pinned compiler requires the second pair to have the first pair's type, `[true, 0]`.
It refuses `[false, 0]`.
The fold control similarly fixes its accumulator at `[0, false]`, then refuses the intended updated number and Boolean.

Widen the immediate numeric and Boolean slots of `pair` and `tuple`.
Keep string literals and every non-primitive argument's existing type.
Do not recursively rewrite records, lists, nested supplied tuples, or handles.
This aligns those target slots with the represented numeric and Boolean types.
It introduces no new Lean literal type.

| Parent compiler probe | Observation |
| --- | --- |
| Current helpers, exposed registered differences, retained real Queue take | Refused at the named conflicts |
| Selective primitive widening with revised expectations | Accepted |
| Only outer callback result annotations | Refused at the same conflicts |
| Widen string slots too | Refused by string-tag controls |
| Small pair-choice and fold controls before repair | Refused |
| The same controls after repair | Accepted |

The direct-slot policy also widens numeric and Boolean brands and variables.
Boolean tuple discriminants lose their correlation.
String tags, readonly positions, and the tested invariant Ref and Deferred parameters retain their distinctions.
Do not advertise arbitrary TypeScript refinement preservation for these generated helpers.

The agent's emitted helper JavaScript is byte-identical before and after the type change.
The parent independently compares those bytes.
That observation concerns the two helpers, not application execution or compiler correctness.

Keep `NativeAtom.row` as the implementation owner.
Generate the prelude through its existing route after a policy ruling.
The shared conditional type needs one owner.
Direct construction-local assertions compile; an intermediate `as unknown as` escape is unnecessary for the tested helpers.

Update six existing expectations: three tuple constructors and their dependent `first`, `third`, and `nested` projections.
Keep the small fold control and the full retained Queue take expression.
Retain the string-tag, readonly, and handle-refusal controls.

Evidence: [literal review](literals/review.md), [agent receipt](literals/receipt.json), and [parent compiler receipt](parent-compiler/receipt.json).
These are finite target-typing observations for the existing TypeScript face under R8.

## 2. Five general typing proofs

The existing `step_keeps_cell` already proves the useful conditional result.
It lives in `src/Effect4/Laws/Modules/Queue/Steps.lean` and serves store-typing, R4.
It consumes the exact callback's typing equation, alongside typed captured values and cell membership.

A concrete checker certificate covers every runtime value admitted by that concrete type.
It is stronger than running examples with sample values.
But the current 27-type `#guard` battery does not export the certificate a theorem needs.
The owning seat must retain and check an actual proof for the chosen application.

The certificate must identify the actual callback, signature, captured type environment, reply type, and cell type.
A proof for the canonical argument names cannot silently cover arbitrary re-elaboration inside a larger loop or callback.
Check the actual body, or prove the exact context connector.

Use `checkTypedProgram`, `admitProgram`, and `Api.Author.build` where their existing certificates suffice.
Add only a local body-evidence connector when the Queue invariant needs that exact judgment.
Do not add a second public checker or make application authors supply unnamed assumptions.

A successful dependent checker branch can retain its equality proof even when the message type arrives as data.
The guarantee that every `MessageTy` succeeds without refusal remains the general unfinished theorem.
Keep all five original goals in place.
Passing one of those goals as evidence makes the resulting proof depend on it again.
Report that dependency rather than describing the application as independent of the deferred proof.

Before using this route for the public path, retain one actual wrapper application and its measured proof dependencies.
Include a nested or structured message type and a wrong-context or wrong-result refusal.
The scratch certificate sketch remains uncompiled.
No new wrapper theorem is proved by this review.

For the general proofs, share checker rules for records, native atoms, and fold binders.
Type the shared Queue passes once, then compose the five original statements.
The existing semantic preservation infrastructure does not need replacement.

Evidence: [typing review](typing/review.md), [retained proof receipt](typing/receipt.json), and [independent review](independent/review.md).
Whole-program admission, the admission gap, scheduling, cancellation, notification delivery, and host agreement keep their existing obligations.

## Guidance requested by the owner

The owner asks to reduce repetitive confirmations and hand-authored evidence work.
The earlier compiler-client research supplies a concrete route: reuse `tools/target/oracle.ts` and `checker.ts` for pinned project checks.
Keep exact source/configuration identities, expected diagnostics, and positive/refusal controls together.
Retain successful typing evidence automatically through the existing authoring and admission path.

Use the actual Queue and rate-limiter cases as the first consumers.
Generate routine wrappers and their scope laws from existing declaration owners.
Reserve owner questions for changes in meaning, supported scope, or representation.
Do not re-ask routine integration choices already authorized by the recorded policy.

This recommends no compiler upgrade, broad macro framework, new gate, or competing implementation seat.
The coordinator owns implementation order and build allocation.
