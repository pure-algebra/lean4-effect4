/**
 * The cas-http/0 semantic core: the closed request algebra interpreted
 * over the byte-plane seams, with no transport anywhere in sight.
 *
 * `serve` is total — every conclusion is a member of the closed outcome
 * vocabulary, a backend that cannot answer included. The principal is
 * an explicit argument to every operation per §9, and every upload is
 * judged by the shared pure admission law before the writer sees it.
 * The core is an ordinary service: a deployment topology is a choice of
 * backend layers beneath it — the same seams an embedded store stands
 * on — and a new wire plane is new request constructors matched here.
 */
import { Context, Effect, Layer, Option } from "effect"
import {
  BackendFailure,
  ByteReader,
  ByteWriter,
  RootStore,
} from "../cas/Backend.ts"
import type { ContentId } from "../cas/Node.ts"
import {
  AddressScheme,
  verifyNodeBytes,
  type CasAddress,
} from "../cas/Store.ts"
import {
  canonicalNode,
  judgeAdmission,
  type AdmissionFacts,
} from "../internal/admission.ts"
import {
  CasOutcome,
  CasRequest,
  type CasServerPolicy,
  type Principal,
} from "./Protocol.ts"

export class CasServerCore extends Context.Service<CasServerCore, {
  readonly serve: (
    principal: Principal,
    request: CasRequest,
  ) => Effect.Effect<CasOutcome>
}>()("foldlab/cas/CasServerCore") {
  /** Build the core over whichever backend layers and address scheme
   * sit beneath it — the same context an embedded store stands on. */
  static readonly layer = (
    policy: CasServerPolicy,
  ): Layer.Layer<
    CasServerCore,
    never,
    ByteReader | ByteWriter | RootStore | AddressScheme
  > =>
    Layer.effect(
      CasServerCore,
      AddressScheme.pipe(
        Effect.flatMap((address) => makeCasServerCore(policy, address)),
      ),
    )
}

/** Build the core over an explicit address function — the model
 * quantifies over the digest, and so does the core, which is what lets
 * the conformance binding replay model vectors under the vector
 * digest. */
export const makeCasServerCore = (
  policy: CasServerPolicy,
  address: CasAddress,
): Effect.Effect<
  CasServerCore["Service"],
  never,
  ByteReader | ByteWriter | RootStore
> => Effect.map(
  Effect.all([ByteReader, ByteWriter, RootStore]),
  ([reader, writer, roots]) => {
  const admissionFacts = Effect.fn("CasServerCore.admissionFacts")(function* (
    id: ContentId,
    refs: ReadonlyArray<{ readonly id: ContentId }>,
  ) {
    const refTags: Array<Option.Option<number>> = []
    for (const ref of refs) {
      const resident = yield* reader.loadBytes(ref.id)
      if (Option.isNone(resident)) {
        refTags.push(Option.none())
      } else {
        const verified = yield* verifyNodeBytes(address, ref.id, resident.value).pipe(
          Effect.mapError((error) => new BackendFailure({
            reason: `Referenced content ${ref.id} failed verification: ${error._tag}`,
            cause: error,
          })),
        )
        refTags.push(Option.some(verified.kind.tag))
      }
    }
    const resident = yield* reader.loadBytes(id)
    const facts: AdmissionFacts = { refTags, resident }
    return facts
  })

  const loadNode = Effect.fn("CasServerCore.load")(function* (
    _principal: Principal,
    id: ContentId,
  ): Effect.fn.Return<CasOutcome, BackendFailure> {
    const resident = yield* reader.loadBytes(id)
    return Option.match(resident, {
      onNone: () => CasOutcome.NodeAbsent(),
      onSome: (bytes) => CasOutcome.NodeBytes({ bytes }),
    })
  })

  const uploadNode = Effect.fn("CasServerCore.upload")(function* (
    _principal: Principal,
    id: ContentId,
    bytes: Uint8Array,
  ): Effect.fn.Return<CasOutcome, BackendFailure> {
    if (bytes.length > policy.maxNodeBytes) {
      return CasOutcome.NodeBudgetExceeded()
    }
    const actual = yield* address.digest(bytes.slice()).pipe(
      Effect.asSome,
      Effect.orElseSucceed(() => Option.none<ContentId>()),
    )
    if (Option.isNone(actual)) {
      return CasOutcome.BackendUnavailable()
    }
    if (actual.value !== id) {
      return CasOutcome.DigestMismatch()
    }
    const decoded = canonicalNode(bytes)
    if (Option.isNone(decoded)) {
      return CasOutcome.AdmissionRefused({ verdict: "NonCanonical" })
    }
    const verdict = judgeAdmission(
      bytes,
      yield* admissionFacts(id, decoded.value.refs),
    )
    switch (verdict._tag) {
      case "Admit":
        yield* writer.putBytes(id, bytes)
        return CasOutcome.Admitted()
      case "AlreadyResident":
        return CasOutcome.AlreadyAdmitted()
      default:
        return CasOutcome.AdmissionRefused({ verdict: verdict._tag })
    }
  })

  const queryPresence = Effect.fn("CasServerCore.missing")(function* (
    _principal: Principal,
    keys: ReadonlyArray<ContentId>,
  ): Effect.fn.Return<CasOutcome, BackendFailure> {
    if (keys.length > policy.maxBatchKeys) {
      return CasOutcome.BatchBudgetExceeded()
    }
    const statuses = yield* reader.presence(keys)
    return CasOutcome.Presence({ statuses })
  })

  const readRoot = Effect.fn("CasServerCore.readRoot")(function* (
    _principal: Principal,
    root: ContentId,
  ): Effect.fn.Return<CasOutcome, BackendFailure> {
    const published = yield* roots.list
    return published.includes(root)
      ? CasOutcome.RootPublished()
      : CasOutcome.RootAbsent()
  })

  const publishRoot = Effect.fn("CasServerCore.publish")(function* (
    _principal: Principal,
    root: ContentId,
    closure: ReadonlyArray<ContentId>,
  ): Effect.fn.Return<CasOutcome, BackendFailure> {
    // Server-side closure verification — optional at /0, enforced
    // here: the root and every declared closure key must be admitted
    // content.
    const held = yield* reader.presence([root, ...closure])
    if (held.some((presence) => presence !== "present")) {
      return CasOutcome.ClosureUnverified()
    }
    yield* roots.publish(root)
    return CasOutcome.Published()
  })

  const serve = (
    principal: Principal,
    request: CasRequest,
  ): Effect.Effect<CasOutcome> =>
    CasRequest.$match(request, {
      LoadNode: ({ id }) => loadNode(principal, id),
      PublishRoot: ({ closure, root }) => publishRoot(principal, root, closure),
      QueryPresence: ({ keys }) => queryPresence(principal, keys),
      ReadCapabilities: () => Effect.succeed(CasOutcome.Capabilities({
        maxBatchKeys: policy.maxBatchKeys,
        maxNodeBytes: policy.maxNodeBytes,
      })),
      ReadRoot: ({ root }) => readRoot(principal, root),
      UploadNode: ({ bytes, id }) => uploadNode(principal, id, bytes),
    }).pipe(
      // A backend that cannot answer is the capacity class, never an
      // admission verdict.
      Effect.catchTag("CasBackendFailure", () =>
        Effect.succeed(CasOutcome.BackendUnavailable())),
    )

  return CasServerCore.of({ serve })
  },
)
