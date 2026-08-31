/**
 * The cas-http/0 server protocol as data: tagged enums for the request
 * algebra, the refusal vocabulary, and the outcome vocabulary; one pure
 * wire law deciding every exchange into a refusal or a typed operation;
 * and the profile's status table as two exhaustive matchers.
 *
 * Everything here is total and service-free. The effectful semantic
 * core interprets `CasRequest` over the backend; the HTTP shell is only
 * the pipeline decide → serve → render. A future wire plane extends
 * the enums and the tables — it never reshapes the pipeline.
 */
import {
  Data,
  Match,
  Option,
  pipe,
  Redacted,
  Schema,
  SchemaGetter,
} from "effect"
import { HttpServerResponse } from "effect/unstable/http"
import { ContentId } from "../cas/Node.ts"
import type { AdmissionVerdict } from "../internal/admission.ts"
import {
  decodeKeyListDocument,
  encodeCapabilityDocument,
  encodePresenceDocument,
  type PresenceStatus,
} from "../internal/wire.ts"

export interface CasServerPolicy {
  /** Published as the capability document's `maxBatchKeys`. */
  readonly maxBatchKeys: number
  /** Published as the capability document's second field: the maximum
   * canonical node body accepted, enforced as the 413 bound. */
  readonly maxNodeBytes: number
  /** The opaque bearer credential for this authority. Absent means an
   * open instance. */
  readonly credential?: Redacted.Redacted<string> | undefined
  /** Whether reads (load, capabilities, presence) are served without a
   * credential when one is configured. Writes always require it. */
  readonly anonymousReads?: boolean | undefined
}

/** The authenticated principal, passed explicitly to every semantic
 * operation per §9. */
export type Principal = Data.TaggedEnum<{
  Anonymous: {}
  Bearer: {}
}>
export const Principal = Data.taggedEnum<Principal>()

/** The closed request algebra — the server's event signature.
 * `ReadRoot` is the /0-additive root-presence read: has this root been
 * published here? */
export type CasRequest = Data.TaggedEnum<{
  ReadCapabilities: {}
  QueryPresence: { readonly keys: ReadonlyArray<ContentId> }
  LoadNode: { readonly id: ContentId }
  ReadRoot: { readonly root: ContentId }
  UploadNode: { readonly id: ContentId; readonly bytes: Uint8Array }
  PublishRoot: {
    readonly root: ContentId
    readonly closure: ReadonlyArray<ContentId>
  }
}>
export const CasRequest = Data.taggedEnum<CasRequest>()

/** The operation classes §9 keeps independently authorizable: object
 * reads, object uploads, and root publication. */
export type OperationClass = "read" | "write" | "publish"

export const operationClass: (request: CasRequest) => OperationClass = pipe(
  Match.type<CasRequest>(),
  Match.withReturnType<OperationClass>(),
  Match.tagsExhaustive({
    LoadNode: () => "read",
    PublishRoot: () => "publish",
    QueryPresence: () => "read",
    ReadCapabilities: () => "read",
    ReadRoot: () => "read",
    UploadNode: () => "write",
  }),
)

/** Every way the wire law refuses before a semantic operation exists. */
export type WireRefusal = Data.TaggedEnum<{
  MalformedBody: {}
  MethodNotAllowed: {}
  MissingProfile: {}
  NotPermitted: {}
  Unauthenticated: {}
  UnknownResource: {}
  WrongMediaType: {}
}>
export const WireRefusal = Data.taggedEnum<WireRefusal>()

/** Every way a semantic operation concludes. `Capabilities` carries its
 * published limits so rendering never needs the policy. */
export type CasOutcome = Data.TaggedEnum<{
  AdmissionRefused: { readonly verdict: AdmissionVerdict["_tag"] }
  Admitted: {}
  AlreadyAdmitted: {}
  BackendUnavailable: {}
  BatchBudgetExceeded: {}
  Capabilities: {
    readonly maxBatchKeys: number
    readonly maxNodeBytes: number
  }
  ClosureUnverified: {}
  DigestMismatch: {}
  NodeAbsent: {}
  NodeBudgetExceeded: {}
  NodeBytes: { readonly bytes: Uint8Array }
  Presence: { readonly statuses: ReadonlyArray<PresenceStatus> }
  Published: {}
  RootAbsent: {}
  RootPublished: {}
}>
export const CasOutcome = Data.taggedEnum<CasOutcome>()

/** The facts the shell gathers from one HTTP exchange before any law
 * runs: method, path, the three governed headers, and the raw body. */
export interface WireFacts {
  readonly method: string
  readonly path: string
  readonly profile: string | undefined
  readonly authorization: string | undefined
  readonly contentType: string | undefined
  readonly body: Uint8Array
}

export type WireDecision = Data.TaggedEnum<{
  Refused: { readonly refusal: WireRefusal }
  Accepted: {
    readonly principal: Principal
    readonly request: CasRequest
  }
}>
export const WireDecision = Data.taggedEnum<WireDecision>()

const octetStream = "application/octet-stream"
const utf8 = new TextEncoder()

/** Constant-time byte comparison over the UTF-8 encodings — no early
 * exit, length folded into the accumulator. */
const constantTimeEquals = (left: string, right: string): boolean => {
  const a = utf8.encode(left)
  const b = utf8.encode(right)
  let acc = a.length ^ b.length
  const length = Math.max(a.length, b.length)
  for (let index = 0; index < length; index += 1) {
    acc |= (a[index] ?? 0) ^ (b[index] ?? 0)
  }
  return acc === 0
}

const authenticate = (
  policy: CasServerPolicy,
  authorization: string | undefined,
): Option.Option<Principal> => {
  if (authorization === undefined) return Option.some(Principal.Anonymous())
  if (!authorization.startsWith("Bearer ")) return Option.none()
  if (policy.credential === undefined) return Option.none()
  return constantTimeEquals(
    authorization.slice("Bearer ".length),
    Redacted.value(policy.credential),
  )
    ? Option.some(Principal.Bearer())
    : Option.none()
}

const authorized = (
  policy: CasServerPolicy,
  principal: Principal,
  operation: OperationClass,
): boolean => {
  if (policy.credential === undefined) return true
  if (Principal.$is("Bearer")(principal)) return true
  return operation === "read" && policy.anonymousReads === true
}

const refused = (refusal: WireRefusal): WireDecision =>
  WireDecision.Refused({ refusal })

const resourcePath = (prefix: "cas" | "roots") =>
  Schema.String.check(
    Schema.isPattern(new RegExp(`^/${prefix}/[0-9a-f]{64}$(?![\\s\\S])`, "u")),
  ).pipe(Schema.decodeTo(ContentId, {
    decode: SchemaGetter.transform((path) => path.slice(prefix.length + 2)),
    encode: SchemaGetter.transform((id) => `/${prefix}/${id}`),
  }))

const CasResourcePath = resourcePath("cas")
const RootResourcePath = resourcePath("roots")

/** The wire law: one total pure function from gathered facts to a
 * refusal or an authenticated, authorized, fully decoded operation.
 * Order is law and mirrors the profile: profile header,
 * authentication, resource, method, media type, body decoding,
 * authorization. */
export const decide = (
  policy: CasServerPolicy,
  facts: WireFacts,
): WireDecision => {
  if (facts.profile !== "cas-http/0") {
    return refused(WireRefusal.MissingProfile())
  }

  const principal = authenticate(policy, facts.authorization)
  if (Option.isNone(principal)) {
    return refused(WireRefusal.Unauthenticated())
  }

  const accept = (request: CasRequest): WireDecision =>
    authorized(policy, principal.value, operationClass(request))
      ? WireDecision.Accepted({ principal: principal.value, request })
      : refused(Principal.$is("Anonymous")(principal.value)
          ? WireRefusal.Unauthenticated()
          : WireRefusal.NotPermitted())

  const bodyKeys = (): Option.Option<ReadonlyArray<ContentId>> =>
    decodeKeyListDocument(facts.body)

  if (facts.path === "/control/capabilities") {
    if (facts.method !== "GET") return refused(WireRefusal.MethodNotAllowed())
    return accept(CasRequest.ReadCapabilities())
  }

  if (facts.path === "/control/missing") {
    if (facts.method !== "POST") return refused(WireRefusal.MethodNotAllowed())
    if (facts.contentType !== octetStream) {
      return refused(WireRefusal.WrongMediaType())
    }
    return Option.match(bodyKeys(), {
      onNone: () => refused(WireRefusal.MalformedBody()),
      onSome: (keys) => accept(CasRequest.QueryPresence({ keys })),
    })
  }

  const root = Schema.decodeOption(RootResourcePath)(facts.path)
  if (Option.isSome(root)) {
    if (facts.method === "GET") {
      return accept(CasRequest.ReadRoot({ root: root.value }))
    }
    if (facts.method !== "PUT") return refused(WireRefusal.MethodNotAllowed())
    if (facts.contentType !== octetStream) {
      return refused(WireRefusal.WrongMediaType())
    }
    return Option.match(bodyKeys(), {
      onNone: () => refused(WireRefusal.MalformedBody()),
      onSome: (closure) => accept(CasRequest.PublishRoot({
        closure,
        root: root.value,
      })),
    })
  }

  const node = Schema.decodeOption(CasResourcePath)(facts.path)
  if (Option.isSome(node)) {
    const id = node.value
    if (facts.method === "GET") return accept(CasRequest.LoadNode({ id }))
    if (facts.method === "PUT") {
      if (facts.contentType !== octetStream) {
        return refused(WireRefusal.WrongMediaType())
      }
      return accept(CasRequest.UploadNode({ bytes: facts.body, id }))
    }
    return refused(WireRefusal.MethodNotAllowed())
  }

  return refused(WireRefusal.UnknownResource())
}

const status = (code: number): HttpServerResponse.HttpServerResponse =>
  HttpServerResponse.empty({ status: code })

const bytesResponse = (
  bytes: Uint8Array,
): HttpServerResponse.HttpServerResponse =>
  HttpServerResponse.uint8Array(bytes, { contentType: octetStream })

/** The refusal half of the profile's status table. */
export const renderRefusal: (
  refusal: WireRefusal,
) => HttpServerResponse.HttpServerResponse = pipe(
  Match.type<WireRefusal>(),
  Match.tagsExhaustive({
    MalformedBody: () => status(400),
    MethodNotAllowed: () => status(405),
    MissingProfile: () => status(400),
    NotPermitted: () => status(403),
    Unauthenticated: () => status(401),
    UnknownResource: () => status(400),
    WrongMediaType: () => status(400),
  }),
)

/** The outcome half of the profile's status table. Acknowledgments are
 * closed empty bodies; data answers are exact octet streams. */
export const renderOutcome: (
  outcome: CasOutcome,
) => HttpServerResponse.HttpServerResponse = pipe(
  Match.type<CasOutcome>(),
  Match.tagsExhaustive({
    AdmissionRefused: () => status(409),
    Admitted: () => status(201),
    AlreadyAdmitted: () => status(200),
    BackendUnavailable: () => status(503),
    BatchBudgetExceeded: () => status(413),
    Capabilities: ({ maxBatchKeys, maxNodeBytes }) =>
      bytesResponse(encodeCapabilityDocument({
        maxBatchKeys,
        maxBlobBytes: maxNodeBytes,
      })),
    ClosureUnverified: () => status(409),
    DigestMismatch: () => status(409),
    NodeAbsent: () => status(404),
    NodeBudgetExceeded: () => status(413),
    NodeBytes: ({ bytes }) => bytesResponse(bytes),
    Presence: ({ statuses }) => bytesResponse(encodePresenceDocument(statuses)),
    Published: () => status(204),
    RootAbsent: () => status(404),
    RootPublished: () => status(204),
  }),
)
