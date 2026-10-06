# Independent decision review

Frozen main: `368e0314`. Evidence: source inspection and the retained T5 receipt. No compiler, Lean or runtime probe runs here.

## 1. Keep the literal decision at the target boundary

Lean already types every natural-number literal as `nat` and every Boolean literal as `bool`.
Only a direct string literal retains its literal type under a const-generic atom.
`litArgTy` in `src/Effect4/Program/Typing/Rules.lean` states this rule explicitly.

The target helpers differ. `pair` and `tuple` use const type parameters in `src/Effect4/Machine/Term.lean`.
The generated prelude therefore retains additional numeric and Boolean distinctions.
This is a target inference mismatch, not evidence that the core representation needs numeric or Boolean singleton types.

The retained T5 receipt reports that changing these two helper signatures repairs the refused Queue steps and the rate-limiter request.
It reports that changing `ite` alone repairs the request but not the refused Queue steps.
Those are seat-reported compiler results. This review does not independently repeat them.

**Recommendation:** prefer the two-helper repair if the parent's fresh controls confirm its exact domain.
Keep string literals, tuple positions, readonly structure and existing values unchanged.
Do not broaden the ruling into a global change to TypeScript literals, Lean types, foreign admission or runtime values.
The helper signatures are compatibility surface: update the affected inference pins and document their new contract.

## 2. The annotation alternative costs more than one annotation

An explicit type argument at a conflicting generic call is a valid alternative to investigate.
For example, `ite<readonly [boolean, Cell]>(flag, pair(true, cell), pair(false, cell))` states a common result type.
This sketch is unexecuted. It makes no claim about the full Queue expression.

An outer callback annotation is not an established repair for inner `ite` and fold inference.
The annotated result may still leave an inner generic application without the required common type.

It is also outside today's exact reader image.
`Codegen.Read.functionAnnotation` in `src/Effect4/Codegen/Read.lean` deliberately refuses parameter and return annotations on term-row callbacks.
`Codegen.Print.print` in `src/Effect4/Codegen/Print.lean` prints without a local typing environment.
Adding checked callback annotations therefore needs coordinated printer, reader, context and roundtrip work.
Erasing arbitrary annotations in the reader would discard the contract that prompted the repair.

The existing core `Term` remains sufficient for either approach. No new stored binding or second program representation follows from this problem.

| Unexecuted control sketch | Required result | Consumer |
| --- | --- | --- |
| Actual Queue take and rate-limiter outputs, before and after the helper change | The intended compiler errors disappear on the full emitted modules | Existing T5 target acceptance |
| Current helpers with only an outer callback return annotation | Record the actual verdict, including any inner-call error | Compare the annotation alternative fairly |
| Current helpers with explicit common types at each failing generic call | Check typing and exact reading, not typing alone | Assess a context-directed printer alternative |
| `pair("Tag", 7)`, mixed tuple, nested tuple and tuple projection | Preserve string tags and positions while applying the stated primitive policy | Existing tuple controls |
| A numeric subtype passed as a variable | State whether it retains its subtype | Bound any claim that a conditional helper widens only literals |

The last control matters when a proposed conditional type tests `A extends number`.
That condition also matches numeric subtypes, not only fresh literal expressions.
It must not be described as a literal-only transformation without inspecting the actual signature.
No such defect in the unseen scratch implementation is asserted here.

## 3. Conditional wrapper proofs can proceed honestly

`step_keeps_cell` in `src/Effect4/Laws/Modules/Queue/Steps.lean` already provides the useful conditional result.
Its hypotheses include a typed captured environment, the actual term-typing equation, cell membership and the successful evaluation.
It concludes membership of both the reply and the next cell value.
It reuses `fold_typed_atomic_update` and the existing term-mapping infrastructure.

It does not import `Queue/Typing.lean` or invoke its five planned goals.
`step_updates` separately connects the evaluated pair to one atomic store update.
The six model-agreement proofs use `Queue/Reading.lean` and are independent of those typing goals.
Their proved status does not establish the missing checker equations.

A wrapper theorem can accept actual admission or term-typing evidence and use these proved connectors.
That theorem can avoid transitive planned-goal dependencies.
Passing `takeStep_typed` or another planned goal as the evidence makes the assembled theorem depend on that goal again.
Turning the evidence into an unnamed assumption does not establish universal usability.

**Recommendation:** permit conditional wrapper work, with the five existing goals retained in their current locations.
Name successful admission or the exact typing equations in the wrapper's public proof contract.
Keep the unconditional claim that every supported message type builds open.
The 27 evaluated types are finite controls, not a proof for arbitrary `MessageTy A`.

`MessageTy` in `src/Effect4/Laws/Modules/Queue/Typing.lean` already names the proper arbitrary-type domain: canonical types with the required formed declarations.
Do not narrow that domain to the tested examples or to numbers merely to remove proof dependencies.
Do not replace the goals with hypotheses and then mark their requirement finished.

| Unexecuted proof control sketch | Required observation |
| --- | --- |
| A wrapper helper taking a concrete typing equation, using `step_keeps_cell` | Measured dependencies contain no Queue typing goal |
| The same helper instantiated with `takeStep_typed` | Measured dependencies report that planned goal |
| One admitted nested-handle message type through the actual wrapper builder | Retain its checked instance and the general usability gap separately |
| A wrong reply type or wrong next-cell type | The checked premise fails instead of being supplied through a cast or goal |

## Placement and exclusions

Literal controls serve target typing and the printed-module relation under `translation-simulation`, with Queue's R10 consumer.
Any changed canonical reading also serves the existing printing and reading claims.
The five checker equations serve `store-typing`, R4, through the wrapper and `step_keeps_cell`.
These controls establish no host agreement, whole-run store preservation, cancellation, delivery or liveness.
The immediate prerequisites are the parent's actual compiler comparison and the owning seat's measured proof dependencies.
