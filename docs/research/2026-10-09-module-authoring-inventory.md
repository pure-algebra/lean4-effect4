# Module authoring and compiler-stage inventory

The smallest next improvements reuse declared operation columns and existing checked packages.
No finding here requires another program representation.
This inventory records observations and proposals, not owner rulings or compatibility grades.

Base: `7334f1197cf5b535541ce1dfc7789a5082c07115`.
The Pull receipt is `docs/research/2026-10-09-pull-protocol-receipt.md`.
The Channel slice starts from `9d489341525ea4a55bb9da512ae35809c0175093` on `codex/channel-transforms`.
Its plan is `docs/research/2026-10-09-channel-transforms-plan.md`.
This update records its named declarations, source adapter and transform controls.
The following authoring slice repairs TypeScript boolean branch printing through the shared template.
Its plan is `docs/research/2026-10-09-authoring-branches-plan.md`.
Its checked receipt is `docs/research/2026-10-09-authoring-branches-receipt.md`.
The existing module survey reads latest (Effect 4.0.1), under decisions rows 331 and 335.
`tools/ModuleSurvey/README.md` states its commands and limits.
A dependency edge identifies implementation candidates, not shared meaning or a proof obligation.

## Alignment with the active visual work

The primary checkout advances independently to `beee8ccc` during this slice.
Its owner ruling is `git:beee8ccc:docs/core/decisions.md`, row 336.
Agents edit graphs through session operations; TypeScript remains an output and a view.
Stored pieces use content addresses at every depth.
The module work continues to construct ordinary core programs that those operations can inspect and reuse.
No proposal here makes arbitrary TypeScript text the authoring authority.
The visual work owns rendering and interaction; this inventory leaves those files unchanged.

## Existing compilation stages

```mermaid
flowchart LR
  A[Authoring terms and module declarations] --> E[One core Eff program]
  F[Forms and templates] --> E
  E --> C[Checked program and module]
  C --> R[Admitted run with its table]
  C --> M[Checked TypeScript module emission]
  M --> T[Target compiler check]
  T --> H[Finite host observation]
  C --> P[Named semantic claims]
  P --> H
```

The final arrow does not identify a Lean theorem with a host observation.
A comparison needs its own observation, assumptions and retained evidence.

| Stage | Existing data and owner | Evidence and limit | Useful next change |
| --- | --- | --- | --- |
| Authoring | `TermSrc`, `Src`, `DefSrc`; `src/Effect4/Program/Authoring.lean` | Source functions elaborate to stored data; they are not stored closures | Keep author helpers here |
| Declared operations | `Def.of`, `eff_module`; `src/Effect4/Program/Authoring/Defs.lean` and `Module.lean` | Named `definitions` fields and ordered `defs` derive from one declaration list | Reuse these fields for adapters and tooling |
| Form expansion | `Forms.Form`, `Template.expand`; `src/Effect4/Codegen/Forms.lean` | Foreign spellings expand into the existing core | Add a Forms row only when admitting that spelling is required |
| Stored program | `Eff`; `src/Effect4/Program/Eff.lean` | Binders and calls remain first-order data | Reuse bind, selection and cause matching for Pull and Channel |
| Type checking | `TypedProgram`; `src/Effect4/Program/CheckedTyping.lean` | Its certificate names one program and signature | Keep expected columns available at source composition boundaries |
| Execution admission | `Api.Built`; `src/Effect4/Api/Built.lean` | The program retains its table, admission certificate and row names | Reuse the package for runtime consumers |
| Target production | `ModuleEmission`; `src/Effect4/Codegen/Checked.lean` | Exact generated declarations retain formation and typing; imports remain separate | Expose projections from this package instead of introducing another checked carrier |
| Source reading | `ModuleReading`; `src/Effect4/Codegen/Admit.lean` | Reading and source admission remain separate from production | Retain located refusals and source binding evidence |
| Target checking and execution | Existing tsgo 7 and host harnesses; `docs/GENERATED.md` | Printing, target acceptance and finite execution are different observations | Record each stage's command and result |
| Evidence reporting | `Reach`, `PartReach`; `Test/Dogfood/Stage.lean` | Existing reports already distinguish admission, output, printing and reading | Extend projections and receipts when a consumer needs them |

## TypeScript reader consolidation

The shared selection plan is `docs/research/2026-10-09-ingest-form-selection-plan.md`.
Its checked receipt is `docs/research/2026-10-09-ingest-form-selection-receipt.md`.
The implementation deepens `expandForm` in `ts/eff/ingest/forms.ts`.
Each reader supplies a recognized head, ordered argument classes and the existing argument readers.
The generated `forms` table chooses the expansion and owns its inserted binders.
The argument-class type projects that table instead of repeating an enumeration.
The interface replaces the former string-identifier entrypoint.
It introduces no program representation or foreign spelling.

CK and OXC share the parser under decisions row 168.
Their separate walks remain in `ts/eff/ingest/ck.ts` and `ts/eff/ingest/oxc.ts`.
Their agreement compares walks, not independent parsers.
The before-and-after comparison retains each reader's full verdict, including its source positions and refusal details.
Existing independent expected trees check the shared expansion at several binder depths.

| Responsibility | Current owner | Consolidation or next scoped change |
| --- | --- | --- |
| Recognize source and captures | Each reader's existing walk | Keep TypeScript syntax checks and refusal ordering local |
| Select and expand a derived form | `expandForm` and `expandTemplate` in `ts/eff/ingest/forms.ts` | Select through generated heads and argument classes; remove reader-owned variant names |
| Construct canonical expressions | `exprForms` in `ts/eff/ingest/oxc.ts` | A future writer can consume `ts/eff/templates.gen.ts` instead of repeating canonical spellings |
| Construct output records | Each `recognizeSource` and `ts/eff/ingest/contract.ts` | Consider one result constructor for wire bytes and generated refusal details; leave refusal selection with each reader |
| Read printed selection forms | `CompilerReader` and the generated canonical reader in `ts/eff/read.ts` | Repair CK's missing option and tag heads through a named printed-image contract |

The retained `canonical-gaps.ts` probe uses printed-source entrypoints only.
Its directory is `docs/research/2026-10-09-ingest-form-selection-evidence/`.
CK refuses `optionCase` and `caseTag`; OXC and the canonical reader recover the same trees.
The neighboring branch and payload controls pass through all three readers.
This finite observation uses closed expressions and an empty row table.
It establishes no typing or execution claim.
Adding those heads widens CK's printed-image domain and requires a separate source reader slice.
It leaves the foreign source domain unchanged.

## Observed authoring gaps

| Observation | Kind and evidence | Smallest useful response |
| --- | --- | --- |
| A lone Chunk has no End type member | Helper gap; `Decision.arms` and `Ty.payloadTy` reject the End selection | For inline sources, use the existing `ascribe` at `Program.Stream.pulledTy` |
| An always-failing inline source has no successful protocol column | Checker-context limit; the Pull battery retains the rejection | Invoke an operation with a declared answer column; investigate expected-type propagation only for a concrete inline consumer |
| Declared operations avoid both workarounds | Existing capability; `ProtocolDefinitions` in `Test/Program/Pull.lean` | Prefer one `eff_module` declaration list over repeated annotations |
| Source metadata no longer needs hand repetition on the declared path | `Source.fromDefinitions` derives its types and invocations from supplied operation declarations | Use generated `definitions` fields; keep the raw Source as an explicit authoring boundary |
| Supplied declarations can differ from an independently installed block | `copiedMetadata` in `Test/Program/Channel.lean` retains that acceptance with a conflicting copied column | A future module-relative adapter can resolve and compare the existing installed declarations; no second program representation is needed |
| Boolean branches previously lost target inference across distinct columns | Repaired by the shared `ifCase` template; the original `TS2375` packet remains retained | Keep authors on ordinary `ifElse`; infer separate branch columns and defer the condition and both branches |
| Printed handle request headers remain unreadable | The Channel packet retains `ReadRefusal.shape "definition"`; existing Queue and Semaphore controls expect the same refusal | Extend the existing type reader and its exact reconstruction contract in a separate slice |
| A raw tag selector accepts another declared union | Protocol premise; `other` in `Test/Program/Pull.lean` types and runs outside the Pull protocol | Offer a protocol-checked entry only when raw callers need admission; generic typing is not protocol admission |
| Empty batches inhabit the list type | Data-language limit; `pulled?` rejects the empty batch that generic typing admits | Keep the producer's nonempty premise explicit; do not introduce a refinement type without its consumers and lowering plan |
| Generic handler proofs need errors and requirements | Proof-helper gap; `Answers` covers empty columns, while `Has` covers full effect types | Add consumed `Has` rules for cause and tag matching before generic Channel typing proofs |
| Semantic proofs expose minted scopes | Proof-helper gap; `matchEffect_protocol` composes `Reads` and `reads_minted_last` | Reuse `TypedScope`, `Kept` and capture laws; package repeated binder reasoning only after another consumer appears |
| Stored declarations have closed types | Language limit; `DefDecl.formed` owns admission | Continue author-time specialization; record polymorphic stored-definition requirements separately |
| Printed syntax is not a target compatibility grade | Evidence boundary; `ModuleEmission` certifies production | Keep source reading, tsgo acceptance, runtime comparison and simulation separate |

A protocol-typed literal helper remains a candidate for inline authoring.
The declared-operation example removes those annotations from its single-outcome bodies.
Boolean branches now use the shared printer and need neither branch annotation.
The same reader laws apply to the new canonical image.
The scoped receipt records the compiler, reconstruction and finite host evidence.
Do not add another public protocol record solely to carry the same two type columns.

## Concrete authoring example

`ProtocolDefinitions` in `Test/Program/Pull.lean` compiles this shape through the shared module command:

```lean
eff_module ProtocolDefinitions where
  emit (items : .list .nat) : protocolTy := succeed (Pull.chunkValue items);
  finish (leftover : .nat) : protocolTy := succeed (Pull.endValue leftover);
  reject (message : .string) : protocolTy error .string := fail message
```

The caller supplies the success, completion and failure handlers to `Pull.matchEffect`.
The declarations own the answer column; the helpers own the tag layout and branch selection.
A handler's failure escapes without entering another handler.
The battery also consumes stored array operations through the same interface.

## Channel authoring surface

The compiled example is `Test/Program/Channel.lean`.
The upstream declaration owns its operation name and columns.
A downstream declaration gives its new columns once:

```lean
eff_module Mapped where
  pull (receiver : stateTy) : protocolTy :=
    Channel.map base.definitions.pull receiver (fun _ => listOf [nat 10, nat 20]);
  done (receiver : stateTy) : protocolTy :=
    Channel.mapDone base.definitions.pull receiver (fun value => app "add" [value, nat 1])
```

`Channel.mapEffect` and `Channel.mapDoneEffect` accept effectful source builders at the same seam.
`Source.fromDefinitions base.definitions.opened mapped.definitions.pull base.definitions.close [receiver]` assembles the source.
It derives element and completion columns, checks state relationships, and returns a located authoring refusal on mismatch.
The caller still installs every referenced module.
Generated operation names cannot shadow the metadata type.
Direct record construction uses `definitions`; `defs` is its ordered projection.
The machine controls exercise composition, captured requests, full failures, retained writes and exactly one close.
The semantic laws concern conditional dispatch and supplied declarations, with no stored-call or whole-stream simulation claim.

The new helpers store no callback and introduce no machine operation.
The repeated binder reasoning stays in the shared Pull and Channel laws.
The next whole-run statement must consume those laws and the definition-aware machine behavior explicitly.

## Useful next module slices

| Slice | Existing building blocks | Required behavior before a broader claim |
| --- | --- | --- |
| Stateful Channel transformations | The four new maps, Pull handlers, declared calls and existing loops | Define empty-result filtering, early stopping, repeated pulls, index state and ownership before adding filter or take |
| SynchronizedRef effectful modification | Ref, Semaphore and the existing protected-acquisition helper | Connect successful client completion to the write; account for interruption, cleanup and failed clients |
| PartitionedSemaphore waiting | Existing scalar bookkeeping, identity tables and waiter helpers | Model keyed waiter identity, partial reservation, ordered selection, cancellation and protected execution |
| PubSub waiting and lifetime | Existing capacity-one, replay-zero steps and shared wait machinery | State subscription identity, delivery, backpressure, cancellation and scoped lifetime |
| Stream and Sink combinations | Pull, Channel and the existing Stream source/consumer interface | Connect repeated pulls, leftovers and finalization to an independent whole-run observation |

Queue, Semaphore, Pool, Latch and Ref already supply substantial shared operation machinery.
Their existing bounded claims do not establish every wrapper, schedule or host behavior.
The current PartitionedSemaphore and PubSub profiles remain narrower than their full vendor modules.
Pull selection adds no new machine primitive or new stored data type.
