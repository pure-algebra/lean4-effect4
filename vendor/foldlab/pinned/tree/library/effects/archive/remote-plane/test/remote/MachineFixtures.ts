import { Effect, HashMap, HashSet, Schema } from "effect"
import {
  entitledToCache,
  initialMachineState,
  overBudget,
  step,
  type MInput,
  type MResult,
  type Params,
  type TaggedCommand,
  type TaggedDecision,
} from "../../src/internal/remoteMachine.ts"
import {
  loadFamily,
  ManifestModel,
  type RemoteBytes,
  type RemoteKey,
  type RemoteStepShape,
} from "../conformance/harness.ts"

const ByteSchema = Schema.Int.check(Schema.isBetween({ minimum: 0, maximum: 0xff }))
const BytesSchema = Schema.Array(ByteSchema)
const KeySchema = BytesSchema.check(Schema.isLengthBetween(32, 32))

const LoadSchema = Schema.Struct({ _tag: Schema.Literal("Load"), key: KeySchema })
const UploadSchema = Schema.Struct({
  _tag: Schema.Literal("Upload"),
  bytes: BytesSchema,
  key: KeySchema,
})
const OperationSchema = Schema.Union([LoadSchema, UploadSchema])
const CommandSchema = OperationSchema

const FindMissingSchema = Schema.Struct({
  _tag: Schema.Literal("FindMissing"),
  keys: Schema.Array(KeySchema),
})
const PublishRootSchema = Schema.Struct({
  _tag: Schema.Literal("PublishRoot"),
  closure: Schema.Array(KeySchema),
  key: KeySchema,
})
const PublishRootCommandSchema = Schema.Struct({
  _tag: Schema.Literal("PublishRoot"),
  key: KeySchema,
})
const AttestSchema = Schema.Struct({
  _tag: Schema.Literal("Attest"),
  bytes: BytesSchema,
  key: KeySchema,
})
const R3OperationSchema = Schema.Union([
  LoadSchema,
  FindMissingSchema,
  UploadSchema,
  PublishRootSchema,
  AttestSchema,
])
const R3CommandSchema = Schema.Union([
  LoadSchema,
  FindMissingSchema,
  UploadSchema,
  PublishRootCommandSchema,
])

const EventSchema = Schema.Union([
  Schema.Struct({ _tag: Schema.Literal("Ok"), bytes: BytesSchema, declared: Schema.Number }),
  Schema.Struct({ _tag: Schema.Literal("Absent") }),
  Schema.Struct({ _tag: Schema.Literal("IntegrityMismatch") }),
])

const KeyStatusSchema = Schema.Union([
  Schema.Struct({ _tag: Schema.Literal("Found"), bytes: BytesSchema, key: KeySchema }),
  Schema.Struct({ _tag: Schema.Literal("Missing"), key: KeySchema }),
  Schema.Struct({ _tag: Schema.Literal("Failed"), key: KeySchema }),
])

const R3EventSchema = Schema.Union([
  Schema.Struct({ _tag: Schema.Literal("Ok"), bytes: BytesSchema, declared: Schema.Number }),
  Schema.Struct({ _tag: Schema.Literal("Absent") }),
  Schema.Struct({ _tag: Schema.Literal("IntegrityMismatch") }),
  Schema.Struct({ _tag: Schema.Literal("BatchResult"), results: Schema.Array(KeyStatusSchema) }),
  Schema.Struct({ _tag: Schema.Literal("Interrupted") }),
])

const DecisionSchema = Schema.Union([
  Schema.Struct({ _tag: Schema.Literal("Issued"), command: CommandSchema }),
  Schema.Struct({ _tag: Schema.Literal("Verified"), key: KeySchema }),
  Schema.Struct({ _tag: Schema.Literal("Cached"), key: KeySchema }),
  Schema.Struct({ _tag: Schema.Literal("Returned"), key: KeySchema }),
  Schema.Struct({ _tag: Schema.Literal("BudgetRejected"), key: KeySchema }),
  Schema.Struct({ _tag: Schema.Literal("IntegrityRejected"), key: KeySchema }),
  Schema.Struct({ _tag: Schema.Literal("RepeatRefused"), key: KeySchema }),
  Schema.Struct({ _tag: Schema.Literal("GaveUp"), key: KeySchema }),
])

const ResultSchema = Schema.Union([
  Schema.Struct({ _tag: Schema.Literal("Commanded") }),
  Schema.Struct({ _tag: Schema.Literal("Delivered"), bytes: BytesSchema, key: KeySchema }),
  Schema.Struct({ _tag: Schema.Literal("Uploaded"), key: KeySchema }),
  Schema.Struct({ _tag: Schema.Literal("NotFound"), key: KeySchema }),
  Schema.Struct({ _tag: Schema.Literal("BudgetRejected"), key: KeySchema }),
  Schema.Struct({ _tag: Schema.Literal("IntegrityRejected"), key: KeySchema }),
  Schema.Struct({ _tag: Schema.Literal("RepeatRefused"), key: KeySchema }),
])

const R3DecisionSchema = Schema.Union([
  Schema.Struct({ _tag: Schema.Literal("Issued"), command: R3CommandSchema }),
  Schema.Struct({ _tag: Schema.Literal("Verified"), key: KeySchema }),
  Schema.Struct({ _tag: Schema.Literal("Cached"), key: KeySchema }),
  Schema.Struct({ _tag: Schema.Literal("Returned"), key: KeySchema }),
  Schema.Struct({ _tag: Schema.Literal("BudgetRejected"), key: KeySchema }),
  Schema.Struct({ _tag: Schema.Literal("IntegrityRejected"), key: KeySchema }),
  Schema.Struct({ _tag: Schema.Literal("RepeatRefused"), key: KeySchema }),
  Schema.Struct({ _tag: Schema.Literal("GaveUp"), key: KeySchema }),
  Schema.Struct({
    _tag: Schema.Literal("PresenceNoted"),
    found: Schema.Array(KeySchema),
    missing: Schema.Array(KeySchema),
  }),
  Schema.Struct({ _tag: Schema.Literal("BatchRejected") }),
  Schema.Struct({ _tag: Schema.Literal("BatchGaveUp") }),
  Schema.Struct({ _tag: Schema.Literal("Published"), key: KeySchema }),
  Schema.Struct({ _tag: Schema.Literal("OrderingRefused"), key: KeySchema }),
  Schema.Struct({ _tag: Schema.Literal("ConfirmedByAttestation"), key: KeySchema }),
  Schema.Struct({ _tag: Schema.Literal("AttestationRefused"), key: KeySchema }),
])

const R3ResultSchema = Schema.Union([
  Schema.Struct({ _tag: Schema.Literal("Commanded") }),
  Schema.Struct({ _tag: Schema.Literal("Delivered"), bytes: BytesSchema, key: KeySchema }),
  Schema.Struct({ _tag: Schema.Literal("Uploaded"), key: KeySchema }),
  Schema.Struct({ _tag: Schema.Literal("NotFound"), key: KeySchema }),
  Schema.Struct({ _tag: Schema.Literal("BudgetRejected"), key: KeySchema }),
  Schema.Struct({ _tag: Schema.Literal("IntegrityRejected"), key: KeySchema }),
  Schema.Struct({ _tag: Schema.Literal("RepeatRefused"), key: KeySchema }),
  Schema.Struct({ _tag: Schema.Literal("TransportFailed"), key: KeySchema }),
  Schema.Struct({ _tag: Schema.Literal("AuthFailed"), key: KeySchema }),
  Schema.Struct({ _tag: Schema.Literal("DuplicateId") }),
  Schema.Struct({ _tag: Schema.Literal("Absorbed") }),
  Schema.Struct({
    _tag: Schema.Literal("BatchAnswered"),
    found: Schema.Array(KeySchema),
    missing: Schema.Array(KeySchema),
  }),
  Schema.Struct({ _tag: Schema.Literal("BatchRejected") }),
  Schema.Struct({ _tag: Schema.Literal("BatchFailed") }),
  Schema.Struct({ _tag: Schema.Literal("KeyBudgetRejected") }),
  Schema.Struct({ _tag: Schema.Literal("Published"), key: KeySchema }),
  Schema.Struct({ _tag: Schema.Literal("OrderingRefused"), key: KeySchema }),
  Schema.Struct({ _tag: Schema.Literal("PublishFailed"), key: KeySchema }),
  Schema.Struct({ _tag: Schema.Literal("Attested"), key: KeySchema }),
  Schema.Struct({ _tag: Schema.Literal("AttestRefused"), key: KeySchema }),
])

const TaggedCommandSchema = Schema.Struct({ command: CommandSchema, op: Schema.Number })
const TaggedDecisionSchema = Schema.Struct({ decision: DecisionSchema, op: Schema.Number })
const SequenceItemSchema = Schema.Union([
  Schema.Struct({ _tag: Schema.Literal("OpRef"), index: Schema.Number }),
  Schema.Struct({ _tag: Schema.Literal("EventRef"), index: Schema.Number }),
])

export const RemoteRowSchema = Schema.Struct({
  case: Schema.String,
  expect: Schema.Struct({
    commands: Schema.Array(TaggedCommandSchema),
    decisions: Schema.Array(TaggedDecisionSchema),
    results: Schema.Array(ResultSchema),
    state: Schema.Struct({
      cacheSize: Schema.Number,
      inFlightSize: Schema.Number,
      rejectedSize: Schema.Number,
    }),
  }),
  input: Schema.Struct({
    ops: Schema.Array(Schema.Struct({ id: Schema.Number, op: OperationSchema })),
    schedule: Schema.Array(Schema.Struct({ answers: Schema.Number, event: EventSchema })),
    sequence: Schema.Array(SequenceItemSchema),
  }),
})
export type RemoteRow = typeof RemoteRowSchema.Type

export const RemoteR3RowSchema = Schema.Struct({
  case: Schema.String,
  expect: Schema.Struct({
    commands: Schema.Array(Schema.Struct({ command: R3CommandSchema, op: Schema.Number })),
    decisions: Schema.Array(Schema.Struct({ decision: R3DecisionSchema, op: Schema.Number })),
    results: Schema.Array(R3ResultSchema),
    state: Schema.Struct({
      cacheSize: Schema.Number,
      confirmedSize: Schema.Number,
      inFlightSize: Schema.Number,
      publishedSize: Schema.Number,
      rejectedSize: Schema.Number,
      reportedMissingSize: Schema.Number,
      reportedPresentSize: Schema.Number,
    }),
  }),
  input: Schema.Struct({
    ops: Schema.Array(Schema.Struct({ id: Schema.Number, op: R3OperationSchema })),
    schedule: Schema.Array(Schema.Struct({ answers: Schema.Number, event: R3EventSchema })),
    sequence: Schema.Array(SequenceItemSchema),
  }),
})
export type RemoteR3Row = typeof RemoteR3RowSchema.Type

export type RemoteFamily = "RMT-001" | "RMT-002" | "RMT-003" | "RMT-004" | "RMT-015"
export type RemoteR3Family = "RMT-005" | "RMT-006" | "RMT-007" | "RMT-008" | "RMT-017"

export const RemoteOracle = "Keys are 32-byte addresses computed by a declared toy digest (a 32-lane byte fold, not cryptographic) over canonical admitted-node encodings from the ratified CAS codec; verification recomputes the digest over received bytes. The full pre-image discipline and the tie to CAS admission arrive with the R2 semantic adapter."

export const remoteBinding = <Family extends RemoteFamily>(family: Family) => ({
  family,
  model: ManifestModel,
  row: RemoteRowSchema,
  hasOracle: true as const,
  oracle: RemoteOracle,
})

export const remoteR3Binding = <Family extends RemoteR3Family>(family: Family) => ({
  family,
  model: ManifestModel,
  row: RemoteR3RowSchema,
  hasOracle: true as const,
  oracle: RemoteOracle,
})

/** The manifest-declared 32-lane toy digest. Test-side only. */
export const toyAddr = (bytes: RemoteBytes): RemoteKey => Array.from({ length: 32 }, (_, lane) => {
  let accumulator = lane + bytes.length
  for (const byte of bytes) accumulator += byte * (lane + 3)
  return accumulator % 256
})

export const remoteParams: Params<RemoteKey, RemoteBytes> = {
  budgets: { maxBytes: 40, maxKeys: 4 },
  size: (bytes) => bytes.length,
  verify: (key, bytes) => key.length === 32
    && toyAddr(bytes).every((byte, index) => key[index] === byte),
}

const deriveFixtureInputs = (
  row: RemoteRow | RemoteR3Row,
): Effect.Effect<ReadonlyArray<MInput<RemoteKey, RemoteBytes>>> =>
  Effect.gen(function* () {
    const inputs: Array<MInput<RemoteKey, RemoteBytes>> = []
    // Lean's fixture derivation uses filterMap. The TypeScript harness dies
    // loudly instead so a malformed committed index cannot silently vanish.
    for (const item of row.input.sequence) {
      if (item._tag === "OpRef") {
        const operation = row.input.ops[item.index]
        if (operation === undefined) {
          return yield* Effect.die(new Error(`${row.case}: unknown operation index`))
        }
        inputs.push({ _tag: "Request", id: operation.id, op: operation.op })
      } else {
        const scheduled = row.input.schedule[item.index]
        if (scheduled === undefined) {
          return yield* Effect.die(new Error(`${row.case}: unknown event index`))
        }
        inputs.push({ _tag: "FromWire", id: scheduled.answers, event: scheduled.event })
      }
    }
    return inputs
  })

export const deriveInputs = (
  row: RemoteRow,
): Effect.Effect<ReadonlyArray<MInput<RemoteKey, RemoteBytes>>> => deriveFixtureInputs(row)

export const deriveR3Inputs = (
  row: RemoteR3Row,
): Effect.Effect<ReadonlyArray<MInput<RemoteKey, RemoteBytes>>> => deriveFixtureInputs(row)

const runInputs = (
  sut: RemoteStepShape,
  inputs: ReadonlyArray<MInput<RemoteKey, RemoteBytes>>,
) => {
  let state = initialMachineState<RemoteKey, RemoteBytes>()
  const commands: Array<TaggedCommand<RemoteKey, RemoteBytes>> = []
  const decisions: Array<TaggedDecision<RemoteKey, RemoteBytes>> = []
  const results: Array<MResult<RemoteKey, RemoteBytes>> = []
  for (const input of inputs) {
    const output = sut.step(remoteParams, state, input)
    state = output.state
    commands.push(...output.commands)
    decisions.push(...output.decisions)
    results.push(output.result)
  }
  return { commands, decisions, results, state }
}

export const runRemoteRow = (
  sut: RemoteStepShape,
  row: RemoteRow,
) => Effect.gen(function* () {
  const inputs = yield* deriveInputs(row)
  const { commands, decisions, results, state } = runInputs(sut, inputs)
  return {
    commands,
    decisions,
    results,
    state: {
      cacheSize: HashSet.size(state.cache),
      inFlightSize: HashMap.size(state.inFlight),
      rejectedSize: HashSet.size(state.rejected),
    },
  }
})

export const runRemoteR3Row = (
  sut: RemoteStepShape,
  row: RemoteR3Row,
) => Effect.gen(function* () {
  const inputs = yield* deriveR3Inputs(row)
  const { commands, decisions, results, state } = runInputs(sut, inputs)
  return {
    commands,
    decisions,
    results,
    state: {
      cacheSize: HashSet.size(state.cache),
      confirmedSize: HashSet.size(state.confirmed),
      inFlightSize: HashMap.size(state.inFlight),
      publishedSize: HashSet.size(state.published),
      rejectedSize: HashSet.size(state.rejected),
      reportedMissingSize: HashSet.size(state.reportedMissing),
      reportedPresentSize: HashSet.size(state.reportedPresent),
    },
  }
})

const assertInputGuards = (
  caseName: string,
  inputs: ReadonlyArray<MInput<RemoteKey, RemoteBytes>>,
) => Effect.gen(function* () {
    let state = initialMachineState<RemoteKey, RemoteBytes>()
    for (const input of inputs) {
      const entitled = entitledToCache(remoteParams, state, input)
      const budgeted = overBudget(remoteParams, state, input)
      const output = step(remoteParams, state, input)
      const cachedOrReturned = output.decisions.some(({ decision }) =>
        decision._tag === "Cached" || decision._tag === "Returned")
      if (!entitled && cachedOrReturned) {
        return yield* Effect.die(new Error(`${caseName}: unentitled input cached or returned`))
      }
      if (budgeted && output.result._tag !== "BudgetRejected") {
        return yield* Effect.die(new Error(`${caseName}: over-budget input was not rejected`))
      }
      state = output.state
    }
})

export const assertRemoteGuards = (
  family: RemoteFamily | RemoteR3Family,
) => Effect.gen(function* () {
  if (family === "RMT-005" || family === "RMT-006"
    || family === "RMT-007" || family === "RMT-008" || family === "RMT-017") {
    const manifest = yield* loadFamily(remoteR3Binding(family))
    for (const row of manifest.rows) {
      yield* assertInputGuards(row.case, yield* deriveR3Inputs(row))
    }
    return
  }
  const manifest = yield* loadFamily(remoteBinding(family))
  for (const row of manifest.rows) {
    yield* assertInputGuards(row.case, yield* deriveInputs(row))
  }
})
