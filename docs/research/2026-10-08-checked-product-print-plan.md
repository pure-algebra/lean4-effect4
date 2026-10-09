# Checked product target printing: bounded slice

Base: `d58d8d9d` on `codex/checked-product-print`.
The old `codex/stream-array` branch stays intact.

A two-slot product of union-valued terms exposes target inference outside the ordinary tuple helper's result.
A global distributive function type breaks callback inference.
Retain ordinary function types and select the checked function type by distinct generic arity.

## Scope

Change the pair and tuple prelude strings in `Machine.Term` and the generated prelude.
Add one shared product result type in the existing prelude generator.
Extend the existing typed term fold, its absence detector, and its named term erasure.
Repair their existing reconstruction proofs and focused controls.
Add no program constructor, stored type, author annotation or public API.

The checked tuple overload takes two generic slot arguments.
The ordinary tuple overload keeps one generic slot list.
The checked pair overload takes one readonly tuple of slot arguments.
The ordinary pair overload keeps two generic slot arguments.
Build that readonly target tuple from the two slot projections directly.
Do not normalize it as a stored two-slot Ty before projection.

Annotate exactly two runtime arguments when a checked slot has a proper union.
Use the existing argument typing rule and literal flag.
An Option type remains one factor in Lean; ordinary Option-valued callback calls keep their inference.
The overloads retain the existing return operations and assertions.
Their declaration wrapper changes the generated JavaScript text.
They add no target cast or widening to any or unknown.

## Proof placement before work

| Field | Placement |
| --- | --- |
| Concept and property | exact-codecs; reconstruct a typed print through the named erasure |
| Questions and roles | existing compatibility claims `typed-print-connector`, `typed-print-erasure`, `typed-print-read` |
| Pointers and consumers | `Program.printTyped_eq_print`, `Codegen.eraseJoinArgs_printTyped`, `Codegen.readTyped_printTyped`; term helpers serve these existing statements |
| Reach | exact approved term heads and generic/runtime arities; checked slot environments; existing readable fragment and lawful spelling for whole-expression reconstruction |
| Exclusions | no raw annotated-source admission, target typing theorem, allocation, codec, runtime or whole-module agreement |
| Unlock | R8; the connected term stage needed before checked module production |

Helpers for the two local inverse equations serve `EraseTermTypes.term_app_certificate` and `eraseTerm_printTerm`.
The updated absence detector serves `Program.printTyped_eq_print`.
Keep existing statement hypotheses and the raw reader's annotated-term refusal.
No proof starts outside these consumer paths.

## Evidence and stages

The retained design experiment changes the helper and one call in the already emitted catalogue packet.
Pinned tsgo accepts all twelve callers, and finite execution matches their retained expected observations.
Separate callback and wrong-payload controls pass.
This experiment is not automatic emitted production.

1. Land marker-free opt-in helper function types and the connected typed term fold, inverse and proofs.
2. The coordinator connects declarations, definitions and layers to checked typed printing under the module certificate.
3. The coordinator runs the public catalogue through that facade and records target results.

The present slice performs stage one only.
`Api.emitModule` and `ModuleEmission.generated` keep the ordinary `Program.printEntry` route.
The public catalogue remains blocked on the tuple failure until stage two.
The frozen Ref header profile remains unchanged throughout this slice.

Done means: focused helper type controls, term erasure/read controls, narrow builds and axiom checks pass.
Retain exact finite sources, compiler settings, observations and input hashes.
No whole build, owner document change or push occurs.
