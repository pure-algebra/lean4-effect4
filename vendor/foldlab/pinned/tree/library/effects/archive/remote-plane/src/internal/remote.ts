/** Verified semantic adapter between CasStore and the untrusted transport. */
import {
  Channel,
  Context,
  Crypto,
  Duration,
  Effect,
  HashMap,
  HashSet,
  Layer,
  Option,
  Predicate,
  Pull,
  Ref,
  Stream,
  SynchronizedRef,
} from "effect"
import {
  AddressMismatch,
  CasNodeInput,
  ContentNotFound,
  DanglingReference,
  RemoteFailure,
  StoreFailure,
  UnknownKind,
  WrongKindReference,
  type CasError,
  type ContentId,
} from "../cas/Node.ts"
import {
  RemoteBudgetError,
  DefaultDecisionTranscriptCapacity,
  RemoteIntegrityError,
  RemotePolicyError,
  RemoteProtocolError,
  RemoteUnavailableError,
  type CasPresence,
  type CasPushReport,
  type CasRemoteConfig,
  type CasRemoteError,
} from "../cas/Remote.ts"
import { CasTransfer, type CasTransferShape, type PutStreamOptions, type UploadSource } from "../cas/Transfer.ts"
import {
  CasSchemeVersion,
  CasStore,
  decodeCasNode,
  encodeCasNode,
  makeMemoryCasStore,
  makeSha256Address,
  type CasAddress,
  type CasStoreShape,
} from "../cas/Store.ts"
import {
  initialMachineState,
  step,
  type Event,
  type KeyStatus,
  type MInput,
  type MachineState,
  type MResult,
  type RDecision,
  type StepOut,
  type Command,
} from "./remoteMachine.ts"
import type {
  CompletionWitness,
  RemoteCasTransport,
  RemoteIssue,
  RemoteTransportFailure,
  RemoteWireEvent,
} from "./remoteTransport.ts"
import {
  decodeCapabilityDocument,
  decodePresenceDocument,
  keyListDocumentEncodedLength,
} from "./remoteControl.ts"
import { bytesEqual } from "./bytes.ts"
import { makeRemoteHttp } from "./remoteHttp.ts"

type TranscriptCommand =
  | Exclude<Command<ContentId, Uint8Array>, { readonly _tag: "Upload" }>
  | { readonly _tag: "Upload"; readonly key: ContentId; readonly byteLength: number }

type TranscriptDecision =
  | Exclude<RDecision<ContentId, Uint8Array>, { readonly _tag: "Issued" }>
  | { readonly _tag: "Issued"; readonly command: TranscriptCommand }

export interface TaggedTranscriptDecision {
  readonly op: number
  readonly decision: TranscriptDecision
}

interface DecisionTranscript {
  readonly buffer: Array<TaggedTranscriptDecision | undefined>
  head: number
  length: number
  dropped: number
}

interface MachineRuntime {
  readonly machine: MachineState<ContentId, Uint8Array>
  readonly transcript: DecisionTranscript
}

const wrapRemoteFailure = (error: CasError | CasRemoteError): CasError => {
  switch (error._tag) {
    case "CasRemoteError/Integrity":
    case "CasRemoteError/Budget":
    case "CasRemoteError/Protocol":
    case "CasRemoteError/Unavailable":
    case "CasRemoteError/Policy":
      return new RemoteFailure({ cause: error })
    default:
      return error
  }
}

export interface RemoteMachineSnapshot {
  readonly decisions: ReadonlyArray<TaggedTranscriptDecision>
  readonly droppedDecisions: number
  readonly cacheSize: number
  readonly confirmedSize: number
  readonly inFlightSize: number
  readonly publishedSize: number
  readonly rejectedSize: number
  readonly reportedMissingSize: number
  readonly reportedPresentSize: number
}

export interface RemoteAdapter {
  readonly store: CasStoreShape
  readonly transfer: CasTransferShape
  readonly snapshot: Effect.Effect<RemoteMachineSnapshot>
}

export interface RemoteAdapterOptions {
  /** Internal source mirror. Production construction uses a fresh memory
   * store; integration fixtures may supply a pre-populated mirror. */
  readonly localStore?: CasStoreShape
}

interface Verification {
  readonly key: ContentId
  readonly bytes: Uint8Array
  readonly valid: boolean
}

interface Exchange {
  readonly event: Event<ContentId, Uint8Array>
  readonly protocolCode?: Extract<RemoteWireEvent, { readonly _tag: "Event" }>["protocolCode"]
  readonly presence?: CasPresence
  readonly witness: CompletionWitness
}

const joinChunks = (chunks: ReadonlyArray<Uint8Array>, length: number): Uint8Array => {
  const output = new Uint8Array(length)
  let offset = 0
  for (const chunk of chunks) {
    output.set(chunk, offset)
    offset += chunk.length
  }
  return output
}

type Pulled =
  | { readonly _tag: "Element"; readonly event: RemoteWireEvent }
  | { readonly _tag: "Done"; readonly witness: CompletionWitness }

type BudgetResult = Extract<MResult<ContentId, Uint8Array>, {
  readonly _tag: "BudgetRejected" | "KeyBudgetRejected"
}>
type NonBudgetResult = Exclude<MResult<ContentId, Uint8Array>, BudgetResult>
type BudgetEvidence = {
  readonly stage: RemoteBudgetError["stage"]
  readonly observed: number
  readonly bound: number
}

const hasBudgetRejectionTag = Predicate.or(
  Predicate.isTagged("BudgetRejected"),
  Predicate.isTagged("KeyBudgetRejected"),
)

const isBudgetResult = (
  result: MResult<ContentId, Uint8Array>,
): result is BudgetResult => hasBudgetRejectionTag(result)

const hasRetryableFailureTag = Predicate.or(
  Predicate.isTagged("CasRemoteError/Protocol"),
  Predicate.isTagged("CasRemoteError/Unavailable"),
)

const isRetryableUploadFailure = (
  error: CasError | CasRemoteError,
): error is RemoteProtocolError | RemoteUnavailableError => hasRetryableFailureTag(error)

/** Construct the once-per-adapter capabilities cache: infinite TTL, the
 * cached probe invalidated on interrupt and on retryable unavailability.
 * Cache state is created here exactly once, at adapter construction. */
const makeCapabilitiesCache = <A>(
  probe: Effect.Effect<A, CasRemoteError>,
) =>
  Effect.cachedInvalidateWithTTL(
    probe,
    Duration.infinity,
  ).pipe(Effect.map(([cached, invalidate]) => cached.pipe(
    Effect.onInterrupt(() => invalidate),
    Effect.tapError((error) => error._tag === "CasRemoteError/Unavailable"
        && error.code !== "unauthenticated"
        && error.code !== "denied"
      ? invalidate
      : Effect.void),
  )))

/** Construct one shared adapter build. */
export const makeRemoteAdapter = Effect.fn("RemoteAdapter.make")(function* (
  config: CasRemoteConfig,
  transport: RemoteCasTransport,
  address: CasAddress,
  options: RemoteAdapterOptions = {},
): Effect.fn.Return<RemoteAdapter, CasRemoteError> {
  const localStore = options.localStore ?? (yield* makeMemoryCasStore(address))
  const decisionCapacity = config.decisionTranscriptCapacity
    ?? DefaultDecisionTranscriptCapacity
  const runtime = yield* SynchronizedRef.make<MachineRuntime>({
    machine: initialMachineState(),
    transcript: {
      buffer: Array.from<TaggedTranscriptDecision | undefined>({
        length: decisionCapacity,
      }),
      head: 0,
      length: 0,
      dropped: 0,
    },
  })
  const nextOpId = yield* Ref.make(1)

  const allocateOpId = Ref.getAndUpdate(nextOpId, (id) => id + 1)

  const remoteIntegrity = (
    opId: number,
    code: RemoteIntegrityError["code"],
    receivedBytes: number,
    stage: RemoteIntegrityError["stage"] = "admission",
    attemptId?: number,
  ): RemoteIntegrityError => {
    let props: ConstructorParameters<typeof RemoteIntegrityError>[0] = {
      opId,
      stage,
      authority: config.authority,
      code,
      receivedBytes,
    }
    if (attemptId !== undefined) props = { ...props, attemptId }
    return new RemoteIntegrityError(props)
  }

  const remoteBudget = (
    opId: number | undefined,
    stage: RemoteBudgetError["stage"],
    observed: number,
    bound: number,
    attemptId?: number,
  ): RemoteBudgetError => {
    let props: ConstructorParameters<typeof RemoteBudgetError>[0] = {
      stage,
      authority: config.authority,
      observed,
      bound,
    }
    if (opId !== undefined) props = { ...props, opId }
    if (attemptId !== undefined) props = { ...props, attemptId }
    return new RemoteBudgetError(props)
  }

  const remoteProtocol = (
    opId: number,
    code: RemoteProtocolError["code"],
    witness: CompletionWitness,
    attemptId?: number,
  ): RemoteProtocolError => {
    let props: ConstructorParameters<typeof RemoteProtocolError>[0] = {
      opId,
      stage: "response",
      authority: config.authority,
      code,
      completion: "possiblyProcessed",
      receivedBytes: witness.receivedBytes,
      sentBytes: witness.sentBytes,
    }
    if (attemptId !== undefined) props = { ...props, attemptId }
    return new RemoteProtocolError(props)
  }

  const remoteUnavailable = (
    opId: number,
    code: RemoteUnavailableError["code"],
    completion: RemoteUnavailableError["completion"],
    receivedBytes: number,
    sentBytes: number,
    attemptId?: number,
    retryAfter?: number,
  ): RemoteUnavailableError => {
    let props: ConstructorParameters<typeof RemoteUnavailableError>[0] = {
      opId,
      stage: "response",
      authority: config.authority,
      code,
      completion,
      receivedBytes,
      sentBytes,
    }
    if (attemptId !== undefined) props = { ...props, attemptId }
    if (retryAfter !== undefined) props = { ...props, retryAfter }
    return new RemoteUnavailableError(props)
  }

  const remotePolicy = (
    opId: number,
    code: RemotePolicyError["code"],
    completion: RemotePolicyError["completion"] = "knownUnprocessed",
    attemptId?: number,
    cause?: RemoteProtocolError | RemoteUnavailableError,
    exchange?: Exchange,
  ): RemotePolicyError => {
    const receivedBytes = exchange?.witness.receivedBytes ?? cause?.receivedBytes ?? 0
    const sentBytes = exchange?.witness.sentBytes ?? cause?.sentBytes ?? 0
    let props: ConstructorParameters<typeof RemotePolicyError>[0] = {
      opId,
      stage: exchange === undefined && cause === undefined ? "request" : "response",
      authority: config.authority,
      code,
      completion,
      receivedBytes,
      sentBytes,
    }
    if (attemptId !== undefined) props = { ...props, attemptId }
    if (cause !== undefined) props = { ...props, cause }
    return new RemotePolicyError(props)
  }

  const unavailableFromTransport = (
    opId: number,
    attemptId: number,
    failure: RemoteTransportFailure,
  ): RemoteUnavailableError => remoteUnavailable(
    opId,
    failure.code,
    failure.completion,
    failure.receivedBytes,
    failure.sentBytes,
    attemptId,
  )

  const machineStep = (
    input: MInput<ContentId, Uint8Array>,
    verification: Verification | undefined,
    maxBytes: number,
    maxKeys = Number.MAX_SAFE_INTEGER,
  ): Effect.Effect<StepOut<ContentId, Uint8Array>> =>
    SynchronizedRef.modify(runtime, (
      current,
    ): readonly [StepOut<ContentId, Uint8Array>, MachineRuntime] => {
      const output = step({
        budgets: { maxBytes, maxKeys },
        size: (bytes) => bytes.length,
        verify: (key, bytes) => verification !== undefined
          && verification.valid
          && key === verification.key
          && bytesEqual(bytes, verification.bytes),
      }, current.machine, input)
      const transcript = current.transcript
      for (const decision of output.decisions) {
        const transcriptDecision: TaggedTranscriptDecision = decision.decision._tag === "Issued"
          ? decision.decision.command._tag === "Upload"
            ? {
              op: decision.op,
              decision: {
                _tag: "Issued",
                command: {
                  _tag: "Upload",
                  key: decision.decision.command.key,
                  byteLength: decision.decision.command.bytes.length,
                },
              },
            }
            : {
              op: decision.op,
              decision: { _tag: "Issued", command: decision.decision.command },
            }
          : { op: decision.op, decision: decision.decision }
        if (decisionCapacity === 0) {
          transcript.dropped += 1
        } else if (transcript.length < decisionCapacity) {
          transcript.buffer[(transcript.head + transcript.length) % decisionCapacity] = transcriptDecision
          transcript.length += 1
        } else {
          transcript.buffer[transcript.head] = transcriptDecision
          transcript.head = (transcript.head + 1) % decisionCapacity
          transcript.dropped += 1
        }
      }
      return [output, {
        machine: output.state,
        transcript,
      }]
    })

  const clearInFlight = (
    opId: number,
    event: Event<ContentId, Uint8Array>,
    maxBytes: number,
  ) => machineStep({ _tag: "FromWire", id: opId, event }, undefined, maxBytes)

  const consumeExchange = Effect.fn("RemoteAdapter.consumeExchange")(function* (
    opId: number,
    attemptId: number,
    issue: RemoteIssue,
  ): Effect.fn.Return<Exchange, CasRemoteError> {
    const receivedRef = yield* Ref.make(0)
    const command = issue.command
    const preparedSentBytes = issue._tag === "Publish"
      ? Option.getOrThrow(keyListDocumentEncodedLength(issue.closure.length))
      : command._tag === "Upload"
      ? command.bytes.length
      : command._tag === "FindMissing"
      ? Option.getOrThrow(keyListDocumentEncodedLength(command.keys.length))
      : 0
    const exchangeLoop = Effect.fn("RemoteAdapter.consumeExchange.loop")(function* () {
    const scope = yield* Effect.scope
    const pull = yield* Channel.toPullScoped(
      transport.issue(opId, attemptId, issue),
      scope,
    )
    const chunks: Array<Uint8Array> = []
    let received = 0
    let declared: number | undefined
    let direct: Extract<RemoteWireEvent, { readonly _tag: "Event" }> | undefined
    const controlExpected = command._tag === "ProbeCapabilities"
      ? 8
      : command._tag === "FindMissing"
      ? command.keys.length
      : undefined
    while (true) {
      const pulled = yield* Pull.catchDone(
        pull.pipe(Effect.map((event): Pulled => ({ _tag: "Element", event }))),
        (witness) => Effect.succeed<Pulled>({ _tag: "Done", witness }),
      ).pipe(Effect.result)
      if (pulled._tag === "Failure") {
        const observedReceivedBytes = yield* Ref.get(receivedRef)
        yield* clearInFlight(
          opId,
          { _tag: "Reset" },
          command._tag === "Upload" ? config.maxEncodedBytes : config.maxDecodedBytes,
        )
        return yield* unavailableFromTransport(
          opId,
          attemptId,
          {
            ...pulled.failure,
            receivedBytes: Math.max(observedReceivedBytes, pulled.failure.receivedBytes),
          },
        )
      }
      const next = pulled.success

      if (next._tag === "Done") {
        const witness = next.witness
        if (direct !== undefined) {
          if (direct.protocolCode === undefined) {
            return { event: direct.event, witness }
          }
          return { event: direct.event, protocolCode: direct.protocolCode, witness }
        }

        if (witness.terminalFraming !== "complete") {
          const event: Event<ContentId, Uint8Array> = witness.terminalFraming === "truncated"
            ? { _tag: "Truncated" }
            : { _tag: "Reset" }
          const protocolCode: NonNullable<Exchange["protocolCode"]> =
            witness.terminalFraming === "truncated" ? "truncatedBody" : "invalidFraming"
          return {
            event,
            protocolCode,
            witness,
          }
        }
        if (declared !== undefined && declared !== received) {
          const event: Event<ContentId, Uint8Array> = { _tag: "Truncated" }
          const protocolCode: NonNullable<Exchange["protocolCode"]> = "invalidFraming"
          return {
            event,
            protocolCode,
            witness,
          }
        }
        const bytes = joinChunks(chunks, received)
        if (command._tag === "Load") {
          const event: Event<ContentId, Uint8Array> = {
            _tag: "Ok",
            declared: declared ?? received,
            bytes,
          }
          return {
            event,
            witness,
          }
        }
        if (command._tag === "ProbeCapabilities") {
          const limits = decodeCapabilityDocument(bytes)
          if (Option.isNone(limits)) {
            const event: Event<ContentId, Uint8Array> = { _tag: "Truncated" }
            const protocolCode: NonNullable<Exchange["protocolCode"]> = "invalidFraming"
            return { event, protocolCode, witness }
          }
          const event: Event<ContentId, Uint8Array> = {
            _tag: "Capabilities",
            limits: limits.value,
          }
          return { event, witness }
        }
        if (command._tag === "FindMissing") {
          const decoded = decodePresenceDocument(command.keys, bytes)
          if (Option.isNone(decoded)) {
            const event: Event<ContentId, Uint8Array> = { _tag: "Truncated" }
            const protocolCode: NonNullable<Exchange["protocolCode"]> = "invalidFraming"
            return { event, protocolCode, witness }
          }
          const results = command.keys.map((key, index): KeyStatus<ContentId, Uint8Array> => {
            switch (decoded.value.statuses[index]) {
              case "missing":
                return { _tag: "Missing", key }
              case "present":
                return { _tag: "Found", key, bytes: new Uint8Array() }
              default:
                return { _tag: "Failed", key }
            }
          })
          const event: Event<ContentId, Uint8Array> = { _tag: "BatchResult", results }
          return { event, presence: decoded.value.presence, witness }
        }
        yield* clearInFlight(opId, { _tag: "Reset" }, config.maxEncodedBytes)
        return yield* remoteProtocol(opId, "invalidAcknowledgement", witness, attemptId)
      }

      const wire = next.event
      switch (wire._tag) {
        case "ResponseStarted": {
          declared = wire.declared
          if (controlExpected !== undefined
            && declared !== undefined
            && declared !== controlExpected) {
            yield* clearInFlight(opId, { _tag: "Truncated" }, config.maxDecodedBytes)
            return yield* remoteProtocol(opId, "invalidFraming", {
              receivedBytes: 0,
              sentBytes: preparedSentBytes,
              terminalFraming: "reset",
            }, attemptId)
          }
          if (controlExpected === undefined
            && declared !== undefined
            && declared > config.maxDecodedBytes) {
            yield* clearInFlight(opId, {
              _tag: "Ok",
              declared,
              bytes: new Uint8Array(),
            }, config.maxDecodedBytes)
            return yield* remoteBudget(
              opId,
              "decoded",
              declared,
              config.maxDecodedBytes,
              attemptId,
            )
          }
          break
        }
        case "BodyChunk": {
          const buffered = received + wire.bytes.length
          if (controlExpected !== undefined) {
            if (buffered > controlExpected) {
              yield* clearInFlight(opId, { _tag: "Truncated" }, config.maxDecodedBytes)
              return yield* remoteProtocol(opId, "invalidFraming", {
                receivedBytes: buffered,
                sentBytes: preparedSentBytes,
                terminalFraming: "reset",
              }, attemptId)
            }
            received = buffered
            yield* Ref.set(receivedRef, received)
            chunks.push(wire.bytes.slice())
            break
          }
          if (buffered > config.maxQueuedBytes) {
            yield* clearInFlight(opId, { _tag: "Interrupted" }, config.maxDecodedBytes)
            return yield* remoteBudget(
              opId,
              "queued",
              buffered,
              config.maxQueuedBytes,
              attemptId,
            )
          }
          if (buffered > config.maxDecodedBytes) {
            yield* clearInFlight(opId, {
              _tag: "Ok",
              declared: buffered,
              bytes: new Uint8Array(),
            }, config.maxDecodedBytes)
            return yield* remoteBudget(
              opId,
              "decoded",
              buffered,
              config.maxDecodedBytes,
              attemptId,
            )
          }
          if (buffered > config.maxDecompressedBytes) {
            yield* clearInFlight(opId, { _tag: "Interrupted" }, config.maxDecodedBytes)
            return yield* remoteBudget(
              opId,
              "decompressed",
              buffered,
              config.maxDecompressedBytes,
              attemptId,
            )
          }
          received += wire.bytes.length
          yield* Ref.set(receivedRef, received)
          chunks.push(wire.bytes.slice())
          break
        }
        case "Event":
          direct = wire
          break
      }
    }
  })
    return yield* Effect.scoped(exchangeLoop()).pipe(
      Effect.timeout(config.operationDeadlineMs),
      Effect.catchTag("TimeoutError", () => Ref.get(receivedRef).pipe(
        Effect.flatMap((receivedBytes) => clearInFlight(
          opId,
          { _tag: "Silence" },
          command._tag === "Upload" ? config.maxEncodedBytes : config.maxDecodedBytes,
        ).pipe(
          Effect.andThen(remoteUnavailable(
            opId,
            "timeout",
            "possiblyProcessed",
            receivedBytes,
            preparedSentBytes,
            attemptId,
          )),
        )),
      )),
    )
  })

  const failureFromExchange = (
    opId: number,
    attemptId: number,
    exchange: Exchange | undefined,
  ): Effect.Effect<never, CasRemoteError> => {
    const witness: CompletionWitness = exchange?.witness ?? {
      receivedBytes: 0,
      sentBytes: 0,
      terminalFraming: "reset",
    }
    if (exchange?.protocolCode !== undefined) {
      return Effect.fail(remoteProtocol(opId, exchange.protocolCode, witness, attemptId))
    }
    switch (exchange?.event._tag) {
      case "Unauthenticated":
      case "Denied":
        return Effect.fail(remoteUnavailable(
          opId,
          exchange.event._tag === "Denied" ? "denied" : "unauthenticated",
          "possiblyProcessed",
          witness.receivedBytes,
          witness.sentBytes,
          attemptId,
        ))
      case "Redirected":
        return Effect.fail(remotePolicy(
          opId,
          "redirectDenied",
          "possiblyProcessed",
          attemptId,
          undefined,
          exchange,
        ))
      case "Silence":
        return Effect.fail(remoteUnavailable(
          opId,
          "timeout",
          "possiblyProcessed",
          witness.receivedBytes,
          witness.sentBytes,
          attemptId,
        ))
      case "Interrupted":
        return Effect.fail(remoteUnavailable(
          opId,
          "cancelled",
          "possiblyProcessed",
          witness.receivedBytes,
          witness.sentBytes,
          attemptId,
        ))
      case "RateLimited":
        return Effect.fail(remoteUnavailable(
          opId,
          "rateLimited",
          "possiblyProcessed",
          witness.receivedBytes,
          witness.sentBytes,
          attemptId,
          exchange.event.retryAfter,
        ))
      case "Capacity":
        return Effect.fail(remoteUnavailable(
          opId,
          "capacity",
          "possiblyProcessed",
          witness.receivedBytes,
          witness.sentBytes,
          attemptId,
        ))
      default:
        return Effect.fail(remoteUnavailable(
          opId,
          "connectionReset",
          "possiblyProcessed",
          witness.receivedBytes,
          witness.sentBytes,
          attemptId,
        ))
    }
  }

  const budgetResultError = (
    opId: number,
    attemptId: number | undefined,
    evidence: BudgetEvidence,
  ): Effect.Effect<never, RemoteBudgetError> => Effect.fail(remoteBudget(
    opId,
    evidence.stage,
    evidence.observed,
    evidence.bound,
    attemptId,
  ))

  const resultError = (
    opId: number,
    attemptId: number | undefined,
    result: NonBudgetResult,
    exchange: Exchange | undefined,
  ): Effect.Effect<never, CasRemoteError | ContentNotFound> => {
    const key = "key" in result ? result.key : undefined
    switch (result._tag) {
      case "NotFound":
        return Effect.fail(new ContentNotFound({ id: result.key }))
      case "IntegrityRejected":
      case "RepeatRefused":
        return Effect.fail(remoteIntegrity(
          opId,
          "remoteRejected",
          exchange?.witness.receivedBytes ?? 0,
          "admission",
          attemptId,
        ))
      case "AuthFailed": {
        const tag = exchange?.event._tag
        return Effect.fail(remoteUnavailable(
          opId,
          tag === "Denied" ? "denied" : "unauthenticated",
          "possiblyProcessed",
          exchange?.witness.receivedBytes ?? 0,
          exchange?.witness.sentBytes ?? 0,
          attemptId,
        ))
      }
      case "TransportFailed": {
        if (attemptId === undefined) {
          return Effect.die(new Error("transport failure has no wire attempt"))
        }
        return failureFromExchange(opId, attemptId, exchange)
      }
      case "BatchRejected":
        return Effect.fail(remoteProtocol(
          opId,
          "batchMisaligned",
          exchange?.witness ?? {
            receivedBytes: 0,
            sentBytes: 0,
            terminalFraming: "complete",
          },
          attemptId,
        ))
      case "BatchFailed":
        if (attemptId === undefined) {
          return Effect.die(new Error("batch failure has no wire attempt"))
        }
        return failureFromExchange(opId, attemptId, exchange)
      case "OrderingRefused":
        return Effect.fail(remotePolicy(
          opId,
          "publishUnconfirmed",
          "knownUnprocessed",
        ))
      case "PublishFailed":
        return exchange?.event._tag === "IntegrityMismatch"
          ? Effect.fail(remoteIntegrity(
            opId,
            "remoteRejected",
            exchange.witness.receivedBytes,
            "response",
            attemptId,
          ))
          : attemptId === undefined
          ? Effect.die(new Error("publish failure has no wire attempt"))
          : failureFromExchange(opId, attemptId, exchange)
      case "AttestRefused":
        return Effect.fail(remotePolicy(opId, "attestRefused"))
      case "DuplicateId":
      case "Absorbed":
      case "Commanded":
      case "Delivered":
      case "Uploaded":
      case "BatchAnswered":
      case "Published":
      case "Attested":
        return Effect.die(new Error(`remote machine result is not an error: ${result._tag}${key ?? ""}`))
    }
  }

  const dispatchResult = (
    opId: number,
    attemptId: number | undefined,
    result: MResult<ContentId, Uint8Array>,
    exchange: Exchange | undefined,
    evidence: BudgetEvidence,
  ): Effect.Effect<never, CasRemoteError | ContentNotFound> => isBudgetResult(result)
    ? budgetResultError(opId, attemptId, evidence)
    : resultError(opId, attemptId, result, exchange)

  const remoteResultError = (
    opId: number,
    attemptId: number | undefined,
    result: MResult<ContentId, Uint8Array>,
    exchange: Exchange | undefined,
    evidence: BudgetEvidence,
  ): Effect.Effect<never, CasRemoteError> => dispatchResult(
    opId,
    attemptId,
    result,
    exchange,
    evidence,
  ).pipe(Effect.catchTag("CasError/ContentNotFound", (error) => Effect.die(
    new Error(`remote machine produced impossible not-found result for ${error.id}`),
  )))

  const probeCapabilities = Effect.fn("CasTransfer.Remote.capabilities.probe")(function* () {
    const opId = yield* allocateOpId
    const exchange = yield* consumeExchange(opId, 1, {
      _tag: "Command",
      command: { _tag: "ProbeCapabilities" },
    })
    if (exchange.event._tag === "Capabilities") return exchange.event.limits
    return yield* failureFromExchange(opId, 1, exchange)
  })

  const capabilities = config.authorityMode === "remote-authoritative"
    ? yield* makeCapabilitiesCache(probeCapabilities())
    : allocateOpId.pipe(Effect.flatMap((opId) => Effect.fail(remotePolicy(
      opId,
      config.authorityMode === "offline" ? "offline" : "authorityMode",
    ))))

  if (config.authorityMode === "remote-authoritative"
    && (config.capabilityProbe ?? "eager") === "eager") {
    yield* capabilities
  }

  const validateUploadNode = Effect.fn("RemoteAdapter.validateUploadNode")(
    function* (
      input: CasNodeInput,
    ): Effect.fn.Return<
      { readonly node: CasNodeInput; readonly bytes: Uint8Array; readonly id: ContentId },
      CasError
    > {
      const node = yield* CasNodeInput.makeEffect(input).pipe(
        Effect.mapError((issue) => new StoreFailure({
          reason: `Invalid CAS node input: ${String(issue)}`,
          cause: issue,
        })),
      )
      if (node.kind.version !== CasSchemeVersion) return yield* new UnknownKind(node.kind)

      for (const ref of node.refs) {
        const resident = yield* localStore.load(ref.id).pipe(
          Effect.mapError((error): CasError => error._tag === "CasError/ContentNotFound"
            ? new DanglingReference({ missing: ref.id })
            : error),
        )
        if (resident.kind.tag !== ref.expectedTag) {
          return yield* new WrongKindReference({
            ref: ref.id,
            expectedTag: ref.expectedTag,
            actualTag: resident.kind.tag,
          })
        }
      }

      const bytes = encodeCasNode(node)
      const id = yield* address.digest(bytes.slice())
      return { node, bytes, id }
    },
  )

  const driveUpload = Effect.fn("CasTransfer.Remote.driveUpload")(function* (
    opId: number,
    attemptId: number,
    node: CasNodeInput,
    key: ContentId,
    bytes: Uint8Array,
  ): Effect.fn.Return<ContentId, CasRemoteError | CasError> {
    const actual = yield* address.digest(bytes.slice())
    const verified = actual === key
    const requested = yield* machineStep({
      _tag: "Request",
      id: opId,
      op: { _tag: "Upload", key, bytes },
    }, { key, bytes, valid: verified }, config.maxEncodedBytes)

    if (!verified || requested.result._tag === "IntegrityRejected") {
      return yield* remoteIntegrity(
        opId,
        "addressMismatch",
        bytes.length,
        "request",
      )
    }
    if (requested.result._tag === "Uploaded") {
      const admitted = yield* localStore.put(node)
      return admitted
    }
    if (requested.result._tag !== "Commanded") {
      return yield* dispatchResult(opId, undefined, requested.result, undefined, {
        stage: "encoded",
        observed: bytes.length,
        bound: config.maxEncodedBytes,
      })
    }

    const command = requested.commands[0]?.command
    if (command === undefined || command._tag !== "Upload") {
      return yield* Effect.die(new Error("commanded upload emitted no command"))
    }
    const exchange = yield* consumeExchange(opId, attemptId, {
      _tag: "Command",
      command,
    })
    const rechecked = yield* address.digest(bytes.slice())
    const answered = yield* machineStep({
      _tag: "FromWire",
      id: opId,
      event: exchange.event,
    }, { key, bytes, valid: rechecked === key }, config.maxEncodedBytes)

    if (answered.result._tag !== "Uploaded") {
      return yield* dispatchResult(opId, attemptId, answered.result, exchange, {
        stage: "encoded",
        observed: bytes.length,
        bound: config.maxEncodedBytes,
      })
    }
    const admitted = yield* localStore.put(node)
    if (admitted !== key) {
      return yield* new AddressMismatch({ expected: key, actual: admitted })
    }
    return key
  }, (effect, opId) => effect.pipe(Effect.onInterrupt(() => clearInFlight(
      opId,
      { _tag: "Interrupted" },
      config.maxEncodedBytes,
    ))))

  const driveLoad = Effect.fn("CasTransfer.Remote.driveLoad")(function* (
    opId: number,
    id: ContentId,
  ): Effect.fn.Return<CasNodeInput, CasRemoteError | CasError> {
    const requested = yield* machineStep({
      _tag: "Request",
      id: opId,
      op: { _tag: "Load", key: id },
    }, undefined, config.maxDecodedBytes)
    if (requested.result._tag !== "Commanded") {
      return yield* dispatchResult(opId, undefined, requested.result, undefined, {
        stage: "decoded",
        observed: 0,
        bound: config.maxDecodedBytes,
      })
    }

    const command = requested.commands[0]?.command
    if (command === undefined || command._tag !== "Load") {
      return yield* Effect.die(new Error("commanded load emitted no command"))
    }
    const exchange = yield* consumeExchange(opId, 1, {
      _tag: "Command",
      command,
    })

    if (exchange.event._tag !== "Ok") {
      const answered = yield* machineStep({
        _tag: "FromWire",
        id: opId,
        event: exchange.event,
      }, undefined, config.maxDecodedBytes)
      return yield* dispatchResult(opId, 1, answered.result, exchange, {
        stage: "decoded",
        observed: exchange.witness.receivedBytes,
        bound: config.maxDecodedBytes,
      })
    }

    const bytes = exchange.event.bytes
    const decoded = Option.getOrUndefined(decodeCasNode(bytes))
    if (decoded === undefined || !bytesEqual(encodeCasNode(decoded), bytes)) {
      yield* machineStep({
        _tag: "FromWire",
        id: opId,
        event: exchange.event,
      }, { key: id, bytes, valid: false }, config.maxDecodedBytes)
      return yield* remoteIntegrity(opId, "nonCanonicalBytes", bytes.length, "admission", 1)
    }

    const actual = yield* address.digest(bytes.slice())
    if (actual !== id) {
      yield* machineStep({
        _tag: "FromWire",
        id: opId,
        event: exchange.event,
      }, { key: id, bytes, valid: false }, config.maxDecodedBytes)
      return yield* remoteIntegrity(opId, "addressMismatch", bytes.length, "admission", 1)
    }

    const admitted = yield* localStore.put(decoded).pipe(
      Effect.tapError(() => machineStep({
        _tag: "FromWire",
        id: opId,
        event: exchange.event,
      }, { key: id, bytes, valid: false }, config.maxDecodedBytes)),
      Effect.mapError((error): CasError => error._tag === "CasError/DanglingReference"
        ? new RemoteFailure({ cause: error })
        : error),
    )
    if (admitted !== id) {
      return yield* new AddressMismatch({ expected: id, actual: admitted })
    }

    const answered = yield* machineStep({
      _tag: "FromWire",
      id: opId,
      event: exchange.event,
    }, { key: id, bytes, valid: true }, config.maxDecodedBytes)
    if (answered.result._tag !== "Delivered") {
      return yield* dispatchResult(opId, 1, answered.result, exchange, {
        stage: "decoded",
        observed: bytes.length,
        bound: config.maxDecodedBytes,
      })
    }
    return decoded
  }, (effect, opId) => effect.pipe(Effect.onInterrupt(() => clearInFlight(
      opId,
      { _tag: "Interrupted" },
      config.maxDecodedBytes,
    ))))

  const withOp = <A, E>(
    maxBytes: number,
    body: (opId: number) => Effect.Effect<A, E>,
  ): Effect.Effect<A, E> => Effect.flatMap(allocateOpId, (opId) =>
    body(opId).pipe(Effect.onInterrupt(() => clearInFlight(
      opId,
      { _tag: "Interrupted" },
      maxBytes,
    ))))

  const missing = Effect.fn("CasTransfer.Remote.missing")(function* (
    keys: ReadonlyArray<ContentId>,
  ): Effect.fn.Return<CasPresence, CasRemoteError> {
    return yield* withOp(config.maxDecodedBytes, Effect.fn(
      "CasTransfer.Remote.missing.op",
    )(function* (opId: number) {
      if (config.authorityMode !== "remote-authoritative") {
        return yield* remotePolicy(
          opId,
          config.authorityMode === "offline" ? "offline" : "authorityMode",
        )
      }
      const limits = yield* capabilities

      const requested = yield* machineStep({
        _tag: "Request",
        id: opId,
        op: { _tag: "FindMissing", keys },
      }, undefined, config.maxDecodedBytes, limits.maxBatchKeys)
      if (requested.result._tag !== "Commanded") {
        return yield* remoteResultError(opId, undefined, requested.result, undefined, {
          stage: "keys",
          observed: keys.length,
          bound: limits.maxBatchKeys,
        })
      }

      const command = requested.commands[0]?.command
      if (command === undefined || command._tag !== "FindMissing") {
        return yield* Effect.die(new Error("commanded find-missing emitted no batch command"))
      }
      const encodedLength = Option.getOrThrow(keyListDocumentEncodedLength(command.keys.length))
      if (encodedLength > config.maxEncodedBytes) {
        yield* clearInFlight(opId, { _tag: "Interrupted" }, config.maxDecodedBytes)
        return yield* remoteBudget(opId, "encoded", encodedLength, config.maxEncodedBytes)
      }
      const exchange = yield* consumeExchange(opId, 1, {
        _tag: "Command",
        command,
      })
      const answered = yield* machineStep({
        _tag: "FromWire",
        id: opId,
        event: exchange.event,
      }, undefined, config.maxDecodedBytes, limits.maxBatchKeys)
      if (answered.result._tag !== "BatchAnswered" || exchange.event._tag !== "BatchResult") {
        return yield* remoteResultError(opId, 1, answered.result, exchange, {
          stage: "keys",
          observed: keys.length,
          bound: limits.maxBatchKeys,
        })
      }

      if (exchange.presence !== undefined) return exchange.presence
      const present: Array<ContentId> = []
      const absent: Array<ContentId> = []
      const failed: Array<ContentId> = []
      for (const status of exchange.event.results) {
        switch (status._tag) {
          case "Found":
            present.push(status.key)
            break
          case "Missing":
            absent.push(status.key)
            break
          case "Failed":
            failed.push(status.key)
            break
        }
      }
      return { present, missing: absent, failed }
    }))
  })

  const publish = Effect.fn("CasTransfer.Remote.publish")(function* (
    root: ContentId,
    closure: ReadonlyArray<ContentId>,
  ): Effect.fn.Return<void, CasRemoteError> {
    return yield* withOp(config.maxEncodedBytes, Effect.fn(
      "CasTransfer.Remote.publish.op",
    )(function* (opId: number) {
      if (config.authorityMode !== "remote-authoritative") {
        return yield* remotePolicy(
          opId,
          config.authorityMode === "offline" ? "offline" : "authorityMode",
        )
      }
      yield* capabilities

      const requested = yield* machineStep({
        _tag: "Request",
        id: opId,
        op: { _tag: "PublishRoot", key: root, closure },
      }, undefined, config.maxEncodedBytes)
      if (requested.result._tag !== "Commanded") {
        return yield* remoteResultError(opId, undefined, requested.result, undefined, {
          stage: "encoded",
          observed: 4 + 32 * closure.length,
          bound: config.maxEncodedBytes,
        })
      }

      const command = requested.commands[0]?.command
      if (command === undefined || command._tag !== "PublishRoot") {
        return yield* Effect.die(new Error("commanded publish emitted no publish command"))
      }
      const encodedLength = Option.getOrThrow(keyListDocumentEncodedLength(closure.length))
      if (encodedLength > config.maxEncodedBytes) {
        yield* clearInFlight(opId, { _tag: "Interrupted" }, config.maxEncodedBytes)
        return yield* remoteBudget(opId, "encoded", encodedLength, config.maxEncodedBytes)
      }
      const exchange = yield* consumeExchange(opId, 1, {
        _tag: "Publish",
        command,
        closure,
      })
      const answered = yield* machineStep({
        _tag: "FromWire",
        id: opId,
        event: exchange.event,
      }, undefined, config.maxEncodedBytes)
      if (answered.result._tag !== "Published") {
        return yield* remoteResultError(opId, 1, answered.result, exchange, {
          stage: "encoded",
          observed: 4 + 32 * closure.length,
          bound: config.maxEncodedBytes,
        })
      }
    }))
  })

  interface LocalGraphEntry {
    readonly id: ContentId
    readonly node: CasNodeInput
    readonly bytes: Uint8Array
  }

  interface LocalGraphPreflight {
    readonly ids: ReadonlyArray<ContentId>
    readonly largestEncodedBytes: number
  }

  const collectLocalGraphIds = Effect.fn(
    "RemoteAdapter.collectLocalGraphIds",
  )(function* (
    root: ContentId,
  ): Effect.fn.Return<LocalGraphPreflight, CasError> {
    const seen = new Set<ContentId>()
    const ids: Array<ContentId> = []
    let largestEncodedBytes = 0

    const visit = Effect.fn("RemoteAdapter.collectLocalGraphIds.visit")(function* (
      id: ContentId,
      isRoot: boolean,
      resident?: CasNodeInput,
    ): Effect.fn.Return<void, CasError> {
      if (seen.has(id)) return
      const current = resident ?? (yield* localStore.load(id).pipe(
          Effect.mapError((error): CasError => !isRoot && error._tag === "CasError/ContentNotFound"
            ? new DanglingReference({ missing: id })
            : error),
        ))
      seen.add(id)
      largestEncodedBytes = Math.max(largestEncodedBytes, encodeCasNode(current).length)
      for (const ref of current.refs) {
        const child = yield* localStore.load(ref.id).pipe(
          Effect.mapError((error): CasError => error._tag === "CasError/ContentNotFound"
            ? new DanglingReference({ missing: ref.id })
            : error),
        )
        if (child.kind.tag !== ref.expectedTag) {
          return yield* new WrongKindReference({
            ref: ref.id,
            expectedTag: ref.expectedTag,
            actualTag: child.kind.tag,
          })
        }
        if (seen.has(ref.id)) continue
        yield* visit(ref.id, false, child)
      }
      ids.push(id)
    })

    yield* visit(root, true)
    return { ids, largestEncodedBytes }
  })

  const materializeLocalBatch = (
    ids: ReadonlyArray<ContentId>,
  ): Effect.Effect<ReadonlyArray<LocalGraphEntry>, CasError> => Effect.forEach(
    ids,
    (id) => localStore.load(id).pipe(
      Effect.map((node) => ({ id, node, bytes: encodeCasNode(node) })),
    ),
  )

  const push = Effect.fn("CasTransfer.Remote.push")(function* (
    root: ContentId,
  ): Effect.fn.Return<CasPushReport, CasRemoteError | CasError> {
    // Preflight the complete closure before operation-specific traffic, but
    // retain only identifiers. Encoded nodes are materialized one negotiated
    // batch at a time below.
    const preflight = yield* collectLocalGraphIds(root)
    const ids = preflight.ids
    const limits = yield* capabilities
    if (preflight.largestEncodedBytes > limits.maxBlobBytes) {
      return yield* remoteBudget(
        undefined,
        "encoded",
        preflight.largestEncodedBytes,
        limits.maxBlobBytes,
      )
    }
    if (limits.maxBatchKeys === 0) {
      // A zero batch capability cannot negotiate at all: this call fails
      // typed through the machine's key-budget rejection, so the
      // zero-stride batch loop below is never entered.
      yield* missing(ids)
    }

    const transferred: Array<ContentId> = []
    const alreadyPresent: Array<ContentId> = []
    for (let offset = 0; offset < ids.length; offset += limits.maxBatchKeys) {
      const batchIds = ids.slice(offset, offset + limits.maxBatchKeys)
      const batch = yield* materializeLocalBatch(batchIds)

      const presence = yield* missing(batchIds)
      const planned = new Map<ContentId, "present" | "missing" | "failed">()
      for (const key of presence.present) planned.set(key, "present")
      for (const key of presence.missing) planned.set(key, "missing")
      for (const key of presence.failed) planned.set(key, "failed")

      for (const entry of batch) {
        const status = planned.get(entry.id)
        if (status === "missing") {
          const opId = yield* allocateOpId
          const confirmed = yield* SynchronizedRef.get(runtime).pipe(
            Effect.map((current) => HashSet.has(current.machine.confirmed, entry.id)),
          )
          if (confirmed) {
            return yield* remoteIntegrity(
              opId,
              "remoteRejected",
              0,
              "response",
            )
          }
          yield* driveUpload(opId, 1, entry.node, entry.id, entry.bytes)
          transferred.push(entry.id)
        } else if (status === "present") {
          const opId = yield* allocateOpId
          const actual = yield* address.digest(entry.bytes.slice())
          const attested = yield* machineStep({
            _tag: "Request",
            id: opId,
            op: { _tag: "Attest", key: entry.id, bytes: entry.bytes },
          }, {
            key: entry.id,
            bytes: entry.bytes,
            valid: actual === entry.id,
          }, config.maxEncodedBytes)
          if (attested.result._tag !== "Attested") {
            return yield* remoteResultError(opId, undefined, attested.result, undefined, {
              stage: "encoded",
              observed: entry.bytes.length,
              bound: config.maxEncodedBytes,
            })
          }
          alreadyPresent.push(entry.id)
        }
      }
    }

    const closure = ids.filter((id) => id !== root)
    yield* publish(root, closure)
    return { transferred, alreadyPresent }
  })

  const putTransfer = Effect.fn("CasTransfer.Remote.putStream")(function* (
    source: UploadSource,
    putOptions: PutStreamOptions,
  ) {
    if (config.authorityMode === "remote-authoritative") yield* capabilities
    const opId = yield* allocateOpId
    let expected = putOptions.expected
    let attemptId = 1

    // The explicit loop preserves attemptId threading and acquires a fresh
    // stream from a Restartable source for every attempt; a generic retry
    // combinator cannot.
    while (true) {
      const chunks: Array<Uint8Array> = []
      let length = 0
      const stream = source._tag === "Restartable" ? source.acquire() : source.stream

      yield* stream.pipe(Stream.runForEach((chunk) => {
        const buffered = length + chunk.length
        if (buffered > config.maxQueuedBytes) {
          return Effect.fail(remoteBudget(
            opId,
            "queued",
            buffered,
            config.maxQueuedBytes,
          ))
        }
        length += chunk.length
        chunks.push(chunk.slice())
        return Effect.void
      }))

      const node = CasNodeInput.make({
        kind: putOptions.kind,
        refs: [...putOptions.refs],
        payload: joinChunks(chunks, length),
      })
      const validated = yield* validateUploadNode(node)
      expected ??= validated.id
      if (expected !== validated.id) {
        return yield* remoteIntegrity(
          opId,
          "addressMismatch",
          validated.bytes.length,
          "request",
        )
      }

      if (config.authorityMode === "offline") {
        return yield* remotePolicy(opId, "offline")
      }
      if (config.authorityMode === "local-authoritative") {
        return yield* localStore.put(validated.node)
      }

      const uploaded = yield* driveUpload(
        opId,
        attemptId,
        validated.node,
        validated.id,
        validated.bytes,
      ).pipe(Effect.result)
      if (uploaded._tag === "Success") return uploaded.success

      const retryable = isRetryableUploadFailure(uploaded.failure)
      if (source._tag === "OneShot" && retryable) {
        return yield* remotePolicy(
          opId,
          "oneShotRetryRefused",
          uploaded.failure.completion,
          attemptId,
          uploaded.failure,
        )
      }
      if (!retryable || attemptId >= config.maxAttempts) {
        return yield* uploaded.failure
      }
      attemptId += 1
    }
  })

  const put = Effect.fn("CasStore.Remote.put")(function* (input: CasNodeInput) {
    if (config.authorityMode === "remote-authoritative") {
      yield* capabilities.pipe(Effect.mapError(wrapRemoteFailure))
    }
    const opId = yield* allocateOpId
    const validated = yield* validateUploadNode(input)
    if (config.authorityMode === "offline") {
      return yield* wrapRemoteFailure(remotePolicy(opId, "offline"))
    }
    if (config.authorityMode === "local-authoritative") {
      return yield* localStore.put(validated.node)
    }
    return yield* driveUpload(opId, 1, validated.node, validated.id, validated.bytes).pipe(
      Effect.mapError(wrapRemoteFailure),
    )
  })

  const load = Effect.fn("CasStore.Remote.load")(function* (id: ContentId) {
    const local = yield* localStore.load(id).pipe(
      Effect.asSome,
      Effect.catchTag("CasError/ContentNotFound", () => Effect.succeed(Option.none())),
    )
    if (local._tag === "Some") return local.value
    if (config.authorityMode !== "remote-authoritative") {
      return yield* new ContentNotFound({ id })
    }
    yield* capabilities.pipe(Effect.mapError(wrapRemoteFailure))

    const opId = yield* allocateOpId
    return yield* driveLoad(opId, id).pipe(
      Effect.mapError(wrapRemoteFailure),
    )
  })

  const loadStream = Effect.fn("CasTransfer.Remote.loadStream")(function* (id: ContentId) {
    const node = yield* load(id).pipe(
      Effect.mapError((error): CasError | CasRemoteError => error._tag === "CasError/RemoteFailure"
        ? error.cause
        : error),
    )
    const bytes = encodeCasNode(node)
    if (bytes.length > config.maxDecodedBytes) {
      return yield* remoteBudget(undefined, "decoded", bytes.length, config.maxDecodedBytes)
    }
    return Stream.succeed(bytes)
  })

  const snapshot = SynchronizedRef.modify(runtime, (
    current,
  ): readonly [RemoteMachineSnapshot, MachineRuntime] => {
    const decisions: Array<TaggedTranscriptDecision> = []
    for (let offset = 0; offset < current.transcript.length; offset += 1) {
      const decision = current.transcript.buffer[
        (current.transcript.head + offset) % decisionCapacity
      ]
      if (decision !== undefined) decisions.push(decision)
    }
    return [{
      decisions,
      droppedDecisions: current.transcript.dropped,
      cacheSize: HashSet.size(current.machine.cache),
      confirmedSize: HashSet.size(current.machine.confirmed),
      inFlightSize: HashMap.size(current.machine.inFlight),
      publishedSize: HashSet.size(current.machine.published),
      rejectedSize: HashSet.size(current.machine.rejected),
      reportedMissingSize: HashSet.size(current.machine.reportedMissing),
      reportedPresentSize: HashSet.size(current.machine.reportedPresent),
    }, current]
  })

  return {
    store: { put, load },
    transfer: {
      capabilities,
      missing,
      publish,
      push,
      putStream: putTransfer,
      loadStream,
    },
    snapshot,
  }
})

/** Build the remote store and transfer projections over one shared adapter. */
export const layerRemote = (
  config: CasRemoteConfig,
): Layer.Layer<
  CasStore | CasTransfer,
  CasRemoteError,
  Crypto.Crypto
> => Layer.effectContext(
  Effect.flatMap(makeRemoteHttp(config), (transport) =>
    Effect.flatMap(makeSha256Address, (address) =>
      Effect.map(makeRemoteAdapter(config, transport, address), (adapter) =>
        Context.empty().pipe(
          Context.add(CasStore, adapter.store),
          Context.add(CasTransfer, adapter.transfer),
        )))),
)
