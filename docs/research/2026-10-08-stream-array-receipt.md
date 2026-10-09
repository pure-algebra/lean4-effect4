# Stream arrays: the receipt

The coordinator must add the roots, semantics registry and architecture entries before integration.
The public source is `Stream.fromArray`.
The module exposes `ArrayDefinitions`, but no helper that asks the caller to repeat its element type.

Status: a production slice with narrow checks and finite machine controls.
Base: `08431c4e`.
Implementation head: `2dfbf9059b20e288041121c092b8d32e09add4fb`.
Branch: `codex/stream-array`.
The plan and retained audit belong to that implementation commit.
This receipt also corrects the plan's missing Effect 4.0.1 qualifier.

## The capability

`fromArray` opens a Ref containing the stored list.
One atomic extraction returns the batch and clears the pending list.
The first pull emits a nonempty batch, or ends for an empty array.
Every later pull ends with `unit`.
Two openings have independent pending state.

The source uses `Program.Stream.pulledTy`, in `src/Effect4/Program/Stream.lean`.
Its end is a value under decisions row 331.
Effect 4.0.1's `Stream.fromArray` calls `Channel.succeed` for a nonempty array.
`Channel.fromEffect` emits once and then returns `Cause.Done`.
The exact source anchors are recorded in `ArrayModel.lean` and `ArrayOps.lean`.

| File | Declarations |
| --- | --- |
| `src/Effect4/Library/Stream/ArrayModel.lean` | `ArrayModel.pull`, the independent batch and pending-state transition |
| `src/Effect4/Library/Stream/ArraySteps.lean` | `arrayStep`, `arrayCaptures`, existing Step data and callback inputs |
| `src/Effect4/Library/Stream/ArrayOps.lean` | `arrayBuildingBlocks`, `arrayOpen`, `arrayBatch`, `arrayPull`, `arrayClose`, `fromArray` |
| `src/Effect4/Library/Stream/ArrayDefs.lean` | `arrayHandleTy`, `ArrayDefinitions`, generated operation definitions and invocations |
| `src/Effect4/Laws/Library/Stream/Array.lean` | `arrayStep_eval`, `arrayStep_agrees`, `arrayBatch_answers` |
| `Test/Program/StreamArray.lean` | public callers, concrete readers and finite controls |

The building-block data names `Effect` and `Ref`, as this implementation uses them.
The existing Stream consumer supplies scope orchestration.
No generic Pull or Channel representation is added.

## The proof connection

The plan records the five placement fields before proof work.
The coordinator registers `stream-array-step-agreement` before its proof starts.
Its pointer is `Effect4.Stream.arrayStep_agrees`, in `src/Effect4/Laws/Library/Stream/Array.lean`.
Its role is simulation, its concept is `translation-simulation`, and its requirement is R10.
The observation contains the extracted batch and cleared allocated backing cell.
Its premises retain scope alignment, receiver reading and the previous cell image.
It establishes no whole pull, run, schedule, finalization, host, codec or allocation correspondence.

`arrayStep_eval` supplies the independent value equation to `Ref.modify_callback_agrees`.
That shared law is in `src/Effect4/Laws/Library/Ref/Callback.lean`.
`arrayBatch_answers` uses `Ref.modify_callback_answers` from the same file.
It serves `step-language-typed`, concept `store-typing`, requirement R4.
It requires a formed normal list type and a typed cell receiver.
The array step discharges its own structural facts.

The retained audit reports only `propext` and `Quot.sound` among the checked dependencies.
The report measures reuse at 66%, through the two Ref callback connectors.
It measures no registered root for these laws in this branch's imported semantics registry.
The coordinator's registered claim lives in the integration worktree.
These measured values belong to the retained audit's imported environment.

## The checks

| Command | Result |
| --- | --- |
| `LEAN_NUM_THREADS=3 lake build Effect4.Library.Stream.ArrayDefs Effect4.Laws.Library.Stream.Array Test.Program.StreamArray Tools.LoadPaths` | exit 0; 942 jobs |
| `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-08-stream-array-audit.lean` | exit 0; retained output in the matching `.log` |
| `rg -c '^#guard' Test/Program/StreamArray.lean` | 19 guard commands |
| `git diff --check` | exit 0 |

The controls collect empty and nonempty arrays through inline and stored-definition sources.
They inspect repeated pulls, clean ends and the cleared pending cell.
They check independent openings and five caller names that overlap internal names.
They refuse missing definitions, incorrect elements, incorrect handles and an incorrect declared answer.
Concrete readers apply the agreement and typing laws at the numeric carrier.

The first builds find reserved-name and term-parenthesization mistakes.
Later checks find missing concrete carrier annotations and test projection spacing.
The final build passes after those corrections.
No TypeScript compiler or whole battery runs in this seat.
The coordinator owns focused generated-target checks.

## The measured authoring gap

The generated record retains `defs` and raw invocation functions.
It retains no per-operation typed descriptor or module element-type field.
An initial source helper therefore requires the caller to repeat `A`.
The slice removes that helper.
The concrete battery constructs its definition-backed source with `.nat` once.

The existing `Source` metadata remains authoring data.
Collection rejects a manually conflicting element field because its accumulator uses that field.
`runForEach` accepts the same metadata mismatch and uses the actual inferred numeric payload.
The battery retains both observations as finite controls.
This is no claim that a falsely labelled source is validated.
The program checker still checks the actual payload and body types.

The next G2 improvement retains typed operation descriptors or module parameter metadata in `eff_module`.
It should own the source connection once, rather than repeat type metadata in a new wrapper.
Generic upstream definition references, pullLoop G1, scope wrapper G7 and module-run agreement G10 remain open.
The older stream-run obligations remain open too.

## Integration

Import `ArrayDefs` from the module library root.
Import the law module from `Effect4.Laws`.
Import the battery from `Test.All`.
The coordinator owns those files, the semantics registry and architecture entries.
The slice changes no owner document, primary checkout or editor work.
It performs no push.
