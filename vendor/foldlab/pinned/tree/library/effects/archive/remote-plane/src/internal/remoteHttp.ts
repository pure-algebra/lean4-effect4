/** Real HttpClient realization of the project-owned cas-http/0 profile. */
import { Channel, Effect, Match, Option, pipe, Predicate, Schema, SchemaGetter, Stream } from "effect"
import * as FetchHttpClient from "effect/unstable/http/FetchHttpClient"
import * as HttpClient from "effect/unstable/http/HttpClient"
import type * as HttpClientError from "effect/unstable/http/HttpClientError"
import * as HttpClientRequest from "effect/unstable/http/HttpClientRequest"
import * as HttpClientResponse from "effect/unstable/http/HttpClientResponse"
import type { CasRemoteConfig } from "../cas/Remote.ts"
import type { ContentId } from "../cas/Node.ts"
import { encodeKeyListDocument } from "./remoteControl.ts"
import type { Event } from "./remoteMachine.ts"
import type {
  CompletionWitness,
  RemoteCasTransport,
  RemoteIssue,
  RemoteTransportFailure,
  RemoteWireEvent,
} from "./remoteTransport.ts"

const PROFILE = "cas-http/0"

// Failures raised while the request is still being prepared: nothing was
// transmitted, so the attempt is known unprocessed.
const isKnownUnprocessedReason = Predicate.or(
  Predicate.isTagged("EncodeError"),
  Predicate.isTagged("InvalidUrlError"),
)

export const classifyTransportFailure = (
  error: HttpClientError.HttpClientError,
  preparedBytes: number,
  receivedBytes = 0,
): RemoteTransportFailure => {
  if (isKnownUnprocessedReason(error.reason)) {
    return {
      _tag: "RemoteTransportFailure",
      code: "connectionFailed",
      completion: "knownUnprocessed",
      receivedBytes: 0,
      sentBytes: 0,
    }
  }
  let current: unknown = "cause" in error.reason ? error.reason.cause : undefined
  let connectionReset = false
  let timedOut = false
  let cancelled = false
  for (let depth = 0; depth < 2 && Predicate.isObjectOrArray(current); depth += 1) {
    const causeCode = "code" in current ? current.code : undefined
    const causeName = "name" in current ? current.name : undefined
    connectionReset ||= causeCode === "ECONNRESET"
    timedOut ||= causeCode === "ETIMEDOUT"
    cancelled ||= causeName === "AbortError"
    current = "cause" in current ? current.cause : undefined
  }
  const code: RemoteTransportFailure["code"] = connectionReset
    ? "connectionReset"
    : timedOut
    ? "timeout"
    : cancelled
    ? "cancelled"
    : "connectionFailed"
  return {
    _tag: "RemoteTransportFailure",
    code,
    completion: "possiblyProcessed",
    receivedBytes,
    // Fetch does not expose transmitted byte counts. On its transport-error
    // path this is the conservative prepared-byte witness, never the error.
    sentBytes: preparedBytes,
  }
}

const terminal = (
  receivedBytes: number,
  sentBytes: number,
  terminalFraming: CompletionWitness["terminalFraming"] = "complete",
): CompletionWitness => ({ receivedBytes, sentBytes, terminalFraming })

const finishAfter = (
  event: RemoteWireEvent,
  witness: CompletionWitness,
): Channel.Channel<RemoteWireEvent, never, CompletionWitness> =>
  Channel.succeed(event).pipe(
    Channel.concatWith(() => Channel.fromEffectDone(Effect.succeed(witness))),
  )

const NonNegativeIntegerHeader = Schema.String.check(
  Schema.isPattern(/^(0|[1-9][0-9]*)$/u),
).pipe(
  Schema.decodeTo(
    Schema.Int.check(Schema.isBetween({ minimum: 0, maximum: Number.MAX_SAFE_INTEGER })),
    {
      decode: SchemaGetter.transform(Number),
      encode: SchemaGetter.transform(String),
    },
  ),
)

type ParsedNonNegativeInteger =
  | { readonly _tag: "Valid"; readonly value: number | undefined }
  | { readonly _tag: "Invalid" }

const parseNonNegativeInteger = (value: string | undefined): ParsedNonNegativeInteger => {
  if (value === undefined) return { _tag: "Valid", value: undefined }
  const decoded = Schema.decodeOption(NonNegativeIntegerHeader)(value)
  return Option.isSome(decoded)
    ? { _tag: "Valid", value: decoded.value }
    : { _tag: "Invalid" }
}

const unsupportedContentEncoding = (value: string | undefined): boolean =>
  value !== undefined && value.split(",").some((coding) =>
    coding.trim().toLowerCase() !== "identity")

const responseEvent = (
  event: Event<ContentId, Uint8Array>,
  sentBytes: number,
  protocolCode?: Extract<RemoteWireEvent, { readonly _tag: "Event" }>["protocolCode"],
) => finishAfter(
  protocolCode === undefined
    ? { _tag: "Event", event }
    : { _tag: "Event", event, protocolCode },
  terminal(0, sentBytes),
)

const rateLimitedEvent = (
  response: HttpClientResponse.HttpClientResponse,
  sentBytes: number,
) => {
  const retryAfter = parseNonNegativeInteger(response.headers["retry-after"])
  return responseEvent(
    retryAfter._tag === "Valid" && retryAfter.value !== undefined
      ? { _tag: "RateLimited", retryAfter: retryAfter.value }
      : { _tag: "RateLimited" },
    sentBytes,
  )
}

const sharedStatusCases = (sentBytes: number) => ({
  401: () => responseEvent({ _tag: "Unauthenticated" }, sentBytes),
  403: () => responseEvent({ _tag: "Denied" }, sentBytes),
  429: (limited: HttpClientResponse.HttpClientResponse) => rateLimitedEvent(limited, sentBytes),
  503: () => responseEvent({ _tag: "Capacity" }, sentBytes),
  507: () => responseEvent({ _tag: "Capacity" }, sentBytes),
  "3xx": () => responseEvent({ _tag: "Redirected" }, sentBytes),
})

const binaryBody = (
  response: HttpClientResponse.HttpClientResponse,
  sentBytes: number,
): Channel.Channel<RemoteWireEvent, RemoteTransportFailure, CompletionWitness> => {
  const contentType = response.headers["content-type"]
  const contentEncoding = response.headers["content-encoding"]
  const parsedDeclared = parseNonNegativeInteger(response.headers["content-length"])
  if (parsedDeclared._tag === "Invalid"
    || contentType !== "application/octet-stream"
    || unsupportedContentEncoding(contentEncoding)) {
    return responseEvent({ _tag: "Reset" }, sentBytes, "invalidHeaders")
  }
  const declared = parsedDeclared.value

  let receivedBytes = 0
  let framing: CompletionWitness["terminalFraming"] = "complete"
  const body = response.stream.pipe(
    Stream.map((bytes): RemoteWireEvent => {
      receivedBytes += bytes.length
      return { _tag: "BodyChunk", bytes }
    }),
    Stream.catchTag("HttpClientError", () => {
      framing = "truncated"
      return Stream.succeed<RemoteWireEvent>({
        _tag: "Event",
        event: { _tag: "Truncated" },
        protocolCode: "truncatedBody",
      })
    }),
  )

  const started: RemoteWireEvent = declared === undefined
    ? { _tag: "ResponseStarted" }
    : { _tag: "ResponseStarted", declared }
  const bodyChannel = Channel.flattenArray(body.channel).pipe(
    Channel.concatWith(() => Channel.fromEffectDone(Effect.sync(() =>
      terminal(receivedBytes, sentBytes, framing)
    ))),
  )
  return Channel.succeed(started).pipe(Channel.concatWith(() => bodyChannel))
}

const loadResponse = (
  response: HttpClientResponse.HttpClientResponse,
  sentBytes: number,
): Channel.Channel<RemoteWireEvent, RemoteTransportFailure, CompletionWitness> =>
  HttpClientResponse.matchStatus(response, {
    ...sharedStatusCases(sentBytes),
    200: (ok) => binaryBody(ok, sentBytes),
    404: () => responseEvent({ _tag: "Absent" }, sentBytes),
    orElse: () => responseEvent({ _tag: "Reset" }, sentBytes, "invalidStatus"),
  })

const controlResponse = (
  response: HttpClientResponse.HttpClientResponse,
  sentBytes: number,
  acceptsPayloadTooLarge: boolean,
): Channel.Channel<RemoteWireEvent, RemoteTransportFailure, CompletionWitness> =>
  HttpClientResponse.matchStatus(response, {
    ...sharedStatusCases(sentBytes),
    200: (ok) => binaryBody(ok, sentBytes),
    // 413 carries capacity meaning only on the batch plane; elsewhere it
    // stays an invalid status.
    413: () =>
      acceptsPayloadTooLarge
        ? responseEvent({ _tag: "Capacity" }, sentBytes)
        : responseEvent({ _tag: "Reset" }, sentBytes, "invalidStatus"),
    orElse: () => responseEvent({ _tag: "Reset" }, sentBytes, "invalidStatus"),
  })

const emptyAcknowledgement = (
  response: HttpClientResponse.HttpClientResponse,
  sentBytes: number,
  consumeBody = true,
): Channel.Channel<RemoteWireEvent, RemoteTransportFailure, CompletionWitness> => {
  const parsedDeclared = parseNonNegativeInteger(response.headers["content-length"])
  const contentType = response.headers["content-type"]
  const contentEncoding = response.headers["content-encoding"]
  if (parsedDeclared._tag === "Invalid"
    || (contentType !== undefined && contentType !== "application/octet-stream")
    || unsupportedContentEncoding(contentEncoding)) {
    return responseEvent({ _tag: "Reset" }, sentBytes, "invalidHeaders")
  }
  const declared = parsedDeclared.value
  if (declared !== undefined && declared !== 0) {
    return responseEvent({ _tag: "Truncated" }, sentBytes, "unexpectedBody")
  }
  if (!consumeBody) {
    return responseEvent({ _tag: "Ok", declared: 0, bytes: new Uint8Array() }, sentBytes)
  }

  return Channel.unwrap(response.stream.pipe(
    Stream.runHead,
    Effect.mapError((error) => classifyTransportFailure(error, sentBytes)),
    Effect.map((head) => Option.isNone(head)
      ? responseEvent({ _tag: "Ok", declared: 0, bytes: new Uint8Array() }, sentBytes)
      : finishAfter(
        {
          _tag: "Event",
          event: { _tag: "Truncated" },
          protocolCode: "unexpectedBody",
        },
        terminal(head.value.length, sentBytes),
      )),
  ))
}

const acknowledgementResponse = (
  response: HttpClientResponse.HttpClientResponse,
  sentBytes: number,
): Channel.Channel<RemoteWireEvent, RemoteTransportFailure, CompletionWitness> =>
  HttpClientResponse.matchStatus(response, {
    ...sharedStatusCases(sentBytes),
    200: (accepted) => emptyAcknowledgement(accepted, sentBytes),
    201: (accepted) => emptyAcknowledgement(accepted, sentBytes),
    // Even a bodyless 204 must satisfy profile header discipline.
    204: (accepted) => emptyAcknowledgement(accepted, sentBytes, false),
    409: () => responseEvent({ _tag: "IntegrityMismatch" }, sentBytes),
    orElse: () => responseEvent({ _tag: "Reset" }, sentBytes, "invalidStatus"),
  })

/** Select the profile's response interpretation for the issued command. */
const commandResponse = (
  response: HttpClientResponse.HttpClientResponse,
  sentBytes: number,
): (
  command: RemoteIssue["command"],
) => Channel.Channel<RemoteWireEvent, RemoteTransportFailure, CompletionWitness> =>
  pipe(
    Match.type<RemoteIssue["command"]>(),
    Match.tagsExhaustive({
      ProbeCapabilities: () => controlResponse(response, sentBytes, false),
      Load: () => loadResponse(response, sentBytes),
      FindMissing: () => controlResponse(response, sentBytes, true),
      Upload: () => acknowledgementResponse(response, sentBytes),
      PublishRoot: () => acknowledgementResponse(response, sentBytes),
    }),
  )

interface PreparedRequest {
  readonly request: HttpClientRequest.HttpClientRequest
  readonly sentBytes: number
}

const commandRequest = (
  config: CasRemoteConfig,
  issue: RemoteIssue,
): PreparedRequest => {
  let request: HttpClientRequest.HttpClientRequest
  let sentBytes = 0
  if (issue._tag === "Publish") {
    const body = encodeKeyListDocument(issue.closure)
    sentBytes = body.length
    request = HttpClientRequest.put(`${config.authority}/roots/${issue.command.key}`).pipe(
      HttpClientRequest.bodyUint8Array(body, "application/octet-stream"),
    )
  } else {
    const command = issue.command
    switch (command._tag) {
      case "ProbeCapabilities":
        request = HttpClientRequest.get(`${config.authority}/control/capabilities`)
        break
      case "Load":
        request = HttpClientRequest.get(`${config.authority}/cas/${command.key}`)
        break
      case "FindMissing": {
        const body = encodeKeyListDocument(command.keys)
        sentBytes = body.length
        request = HttpClientRequest.post(`${config.authority}/control/missing`).pipe(
          HttpClientRequest.bodyUint8Array(body, "application/octet-stream"),
        )
        break
      }
      case "Upload":
        sentBytes = command.bytes.length
        request = HttpClientRequest.put(`${config.authority}/cas/${command.key}`).pipe(
          HttpClientRequest.bodyUint8Array(command.bytes, "application/octet-stream"),
        )
        break
    }
  }
  request = request.pipe(
    HttpClientRequest.setHeader("accept", "application/octet-stream"),
    HttpClientRequest.setHeader("cas-profile", PROFILE),
  )
  if (config.credentials !== undefined) {
    request = HttpClientRequest.bearerToken(request, config.credentials)
  }
  return {
    request,
    sentBytes,
  }
}

/**
 * Build a single-attempt transport over the pinned FetchHttpClient. The
 * transport owns this realization so every request honors `redirect: manual`;
 * arbitrary HttpClient implementations are intentionally not accepted because
 * they cannot prove that redirects remain observable machine events.
 * redirectPolicy is validated configuration whose bounded following semantics
 * arrive in R4. No retry combinator is applied, so attempts remain machine
 * decisions.
 */
export const makeRemoteHttp = (
  config: CasRemoteConfig,
): Effect.Effect<RemoteCasTransport> =>
  Effect.map(HttpClient.HttpClient, (baseClient) => {
    const client = HttpClient.withScope(baseClient)

    const transport: RemoteCasTransport = {
      issue: (_opId, _attemptId, issue) => {
        const command = issue.command
        const prepared = commandRequest(config, issue)

        return Channel.unwrap(
          client.execute(prepared.request).pipe(
            Effect.provideService(FetchHttpClient.RequestInit, { redirect: "manual" }),
            Effect.mapError((error) => classifyTransportFailure(error, prepared.sentBytes)),
            Effect.map((response) => commandResponse(response, prepared.sentBytes)(command)),
          ),
        )
      },
    }
    return transport
  }).pipe(Effect.provide(FetchHttpClient.layer))

