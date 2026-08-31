/** Typed remote-CAS policy and failure surface. */
import { Schema, type Stream } from "effect"
import type { CasError, ContentId } from "./Node.ts"

export const RemoteAuthority = Schema.String.check(
  Schema.makeFilter((value) => {
    if (!URL.canParse(value)) {
      return "authority must be a valid URL origin"
    }
    const url = new URL(value)
    return (url.protocol === "http:" || url.protocol === "https:")
        && url.username === ""
        && url.password === ""
        && url.pathname === "/"
        && url.search === ""
        && url.hash === ""
        && url.origin === value
      ? undefined
      : "authority must be an http(s) origin with no userinfo, path, query, or fragment"
  }),
).pipe(Schema.brand("RemoteAuthority"))
export type RemoteAuthority = typeof RemoteAuthority.Type

export const RemoteAuthorityMode = Schema.Literals([
  "remote-authoritative",
  "local-authoritative",
  "offline",
])
export type RemoteAuthorityMode = typeof RemoteAuthorityMode.Type

export const RemoteCompletion = Schema.Literals([
  "knownUnprocessed",
  "possiblyProcessed",
])
export type RemoteCompletion = typeof RemoteCompletion.Type

export const RemoteStage = Schema.Literals(["request", "response", "admission"])
export type RemoteStage = typeof RemoteStage.Type

export const RemoteBudgetStage = Schema.Literals([
  "encoded",
  "decoded",
  "decompressed",
  "queued",
  "keys",
])
export type RemoteBudgetStage = typeof RemoteBudgetStage.Type

const Count = Schema.Int.check(Schema.isGreaterThanOrEqualTo(0))
const PositiveCount = Schema.Int.check(Schema.isGreaterThanOrEqualTo(1))
const AttemptId = Schema.optionalKey(PositiveCount)
const Uint32 = Schema.Int.check(Schema.isBetween({ minimum: 0, maximum: 0xffff_ffff }))

/** Canonical server capability document carried by the cas-http/0 control plane. */
export const RemoteCapabilities = Schema.Struct({
  maxBatchKeys: Uint32,
  maxBlobBytes: Uint32,
})
export type RemoteCapabilities = typeof RemoteCapabilities.Type

/** Advisory request-order subsequences from one find-missing operation. */
export interface CasPresence {
  readonly present: ReadonlyArray<ContentId>
  readonly missing: ReadonlyArray<ContentId>
  readonly failed: ReadonlyArray<ContentId>
}

/** Completed graph push accounting. Presence remains planning data only. */
export interface CasPushReport {
  readonly transferred: ReadonlyArray<ContentId>
  readonly alreadyPresent: ReadonlyArray<ContentId>
}

export const RemoteIntegrityCode = Schema.Literals([
  "addressMismatch",
  "nonCanonicalBytes",
  "remoteRejected",
  "acknowledgementMismatch",
])

export const RemoteProtocolCode = Schema.Literals([
  "invalidStatus",
  "invalidHeaders",
  "invalidFraming",
  "truncatedBody",
  "unexpectedBody",
  "invalidAcknowledgement",
  "batchMisaligned",
])

export const RemoteUnavailableCode = Schema.Literals([
  "connectionFailed",
  "connectionReset",
  "timeout",
  "cancelled",
  "unauthenticated",
  "denied",
  "rateLimited",
  "capacity",
])

export const RemotePolicyCode = Schema.Literals([
  "offline",
  "authorityMode",
  "redirectDenied",
  "oneShotRetryRefused",
  "attemptLimit",
  "publishUnconfirmed",
  "attestRefused",
])

export class RemoteIntegrityError extends Schema.TaggedError<RemoteIntegrityError>()(
  "CasRemoteError/Integrity",
  {
    opId: PositiveCount,
    attemptId: AttemptId,
    stage: RemoteStage,
    authority: RemoteAuthority,
    code: RemoteIntegrityCode,
    receivedBytes: Count,
  },
) {}

export class RemoteBudgetError extends Schema.TaggedError<RemoteBudgetError>()(
  "CasRemoteError/Budget",
  {
    opId: Schema.optionalKey(PositiveCount),
    attemptId: AttemptId,
    stage: RemoteBudgetStage,
    authority: RemoteAuthority,
    observed: Count,
    bound: Count,
  },
) {}

export class RemoteProtocolError extends Schema.TaggedError<RemoteProtocolError>()(
  "CasRemoteError/Protocol",
  {
    opId: PositiveCount,
    attemptId: AttemptId,
    stage: RemoteStage,
    authority: RemoteAuthority,
    code: RemoteProtocolCode,
    completion: RemoteCompletion,
    receivedBytes: Count,
    sentBytes: Count,
  },
) {}

export class RemoteUnavailableError extends Schema.TaggedError<RemoteUnavailableError>()(
  "CasRemoteError/Unavailable",
  {
    opId: PositiveCount,
    attemptId: AttemptId,
    stage: RemoteStage,
    authority: RemoteAuthority,
    code: RemoteUnavailableCode,
    completion: RemoteCompletion,
    receivedBytes: Count,
    sentBytes: Count,
    retryAfter: Schema.optionalKey(Count),
  },
) {}

export class RemotePolicyError extends Schema.TaggedError<RemotePolicyError>()(
  "CasRemoteError/Policy",
  {
    opId: PositiveCount,
    attemptId: AttemptId,
    stage: RemoteStage,
    authority: RemoteAuthority,
    code: RemotePolicyCode,
    completion: RemoteCompletion,
    receivedBytes: Count,
    sentBytes: Count,
    cause: Schema.optionalKey(Schema.Union([RemoteProtocolError, RemoteUnavailableError])),
  },
) {}

export const CasRemoteError = Schema.Union([
  RemoteIntegrityError,
  RemoteBudgetError,
  RemoteProtocolError,
  RemoteUnavailableError,
  RemotePolicyError,
])
export type CasRemoteError = typeof CasRemoteError.Type

/**
 * Upload restartability is explicit so one-shot streams cannot be retried.
 * A restartable source is a factory: every attempt acquires a fresh stream,
 * so a queue-backed or otherwise consumptive stream cannot be labeled safely
 * re-runnable while rerunning it would not reproduce its bytes.
 */
export type UploadSource =
  | {
    readonly _tag: "Restartable"
    readonly acquire: () => Stream.Stream<Uint8Array, CasError | CasRemoteError>
  }
  | { readonly _tag: "OneShot"; readonly stream: Stream.Stream<Uint8Array, CasError | CasRemoteError> }

export const restartable = (
  acquire: () => Stream.Stream<Uint8Array, CasError | CasRemoteError>,
): UploadSource => ({ _tag: "Restartable", acquire })

export const oneShot = (
  stream: Stream.Stream<Uint8Array, CasError | CasRemoteError>,
): UploadSource => ({ _tag: "OneShot", stream })

export const RedirectPolicy = Schema.Struct({
  maxRedirects: Count,
  crossOrigin: Schema.Literals(["deny", "allow"]),
})
export type RedirectPolicy = typeof RedirectPolicy.Type

/** Default number of most-recent remote machine decisions retained for
 * diagnostics by one acquired adapter. */
export const DefaultDecisionTranscriptCapacity = 4_096

export const CapabilityProbeMode = Schema.Literals(["eager", "lazy"])
export type CapabilityProbeMode = typeof CapabilityProbeMode.Type

/**
 * Explicit remote policy. Credentials are accepted only as Redacted values;
 * no error or transcript type has a field capable of carrying them.
 * Redirect policy fields are validated now but become behaviorally active in
 * R4; the current adapter observes every redirect and denies it through the
 * machine.
 */
export class CasRemoteConfig extends Schema.Class<CasRemoteConfig>("CasRemoteConfig")({
  authority: RemoteAuthority,
  authorityMode: RemoteAuthorityMode,
  maxEncodedBytes: PositiveCount,
  maxDecodedBytes: PositiveCount,
  maxDecompressedBytes: PositiveCount,
  maxQueuedBytes: PositiveCount,
  maxAttempts: PositiveCount,
  operationDeadlineMs: PositiveCount,
  decisionTranscriptCapacity: Schema.optionalKey(Count),
  capabilityProbe: Schema.optionalKey(CapabilityProbeMode),
  redirectPolicy: RedirectPolicy,
  credentials: Schema.optionalKey(Schema.Redacted(Schema.String, {
    disallowJsonEncode: true,
  })),
}) {}

export interface RemoteConfigOptions {
  readonly authorityMode?: RemoteAuthorityMode
  readonly maxEncodedBytes?: number
  readonly maxDecodedBytes?: number
  readonly maxDecompressedBytes?: number
  readonly maxQueuedBytes?: number
  readonly maxAttempts?: number
  readonly operationDeadlineMs?: number
  readonly decisionTranscriptCapacity?: number
  readonly capabilityProbe?: CapabilityProbeMode
  readonly redirectPolicy?: RedirectPolicy
  readonly credentials?: CasRemoteConfig["credentials"]
}

const DefaultRemoteBudgetBytes = 1_000_000

/** The optional-key fields of the explicit config: present only when the
 * caller supplied them, so the constructed props omit the keys entirely. */
interface RemoteConfigOptionals {
  decisionTranscriptCapacity?: number
  credentials?: Exclude<CasRemoteConfig["credentials"], undefined>
}

/**
 * Validate a plain HTTP(S) authority and fill the ordinary remote policy
 * defaults without weakening the fully explicit CasRemoteConfig contract.
 */
export const remoteConfig = (
  authority: string,
  options: RemoteConfigOptions = {},
): CasRemoteConfig => {
  const optionals: RemoteConfigOptionals = {}
  if (options.decisionTranscriptCapacity !== undefined) {
    optionals.decisionTranscriptCapacity = options.decisionTranscriptCapacity
  }
  if (options.credentials !== undefined) {
    optionals.credentials = options.credentials
  }
  return new CasRemoteConfig({
    authority: RemoteAuthority.make(authority),
    authorityMode: options.authorityMode ?? "remote-authoritative",
    maxEncodedBytes: options.maxEncodedBytes ?? DefaultRemoteBudgetBytes,
    maxDecodedBytes: options.maxDecodedBytes ?? DefaultRemoteBudgetBytes,
    maxDecompressedBytes: options.maxDecompressedBytes ?? DefaultRemoteBudgetBytes,
    maxQueuedBytes: options.maxQueuedBytes ?? DefaultRemoteBudgetBytes,
    maxAttempts: options.maxAttempts ?? 1,
    operationDeadlineMs: options.operationDeadlineMs ?? 10_000,
    capabilityProbe: options.capabilityProbe ?? "eager",
    redirectPolicy: options.redirectPolicy ?? { maxRedirects: 0, crossOrigin: "deny" },
    ...optionals,
  })
}
