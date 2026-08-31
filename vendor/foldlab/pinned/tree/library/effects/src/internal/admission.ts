/**
 * The CAS admission core: one pure judgment shared by every backend.
 *
 * Admission is store law, not adapter code — canonical verification,
 * reference checking, and collision detection must hold identically for
 * the in-memory adapter, a server over any byte backend, and any future
 * store. The judge is a total pure function over the candidate's
 * canonical bytes and a small record of facts the backend answered, so
 * a second backend implements two lookups, never the law.
 *
 * Concurrency note the factoring makes precise: an admitted store only
 * grows, so a passed reference check cannot be invalidated by a
 * concurrent admission — check-then-insert is sound without a global
 * lock, and only the collision arm (same address, different bytes)
 * needs a read-back compare against what actually resides.
 */
import { Option } from "effect"
import type { CasNodeInput, ContentId } from "../cas/Node.ts"
import { CasSchemeVersion, decodeCasNode, encodeCasNode } from "./casCodec.ts"
import { bytesEqual } from "./bytes.ts"

/** What the backend answered about the state this admission consults:
 * the actual kind tag of each referenced node in reference order (none
 * when absent), and any bytes already resident at the candidate's own
 * address. */
export interface AdmissionFacts {
  readonly refTags: ReadonlyArray<Option.Option<number>>
  readonly resident: Option.Option<Uint8Array>
}

export type AdmissionVerdict =
  | { readonly _tag: "Admit"; readonly node: CasNodeInput }
  | { readonly _tag: "AlreadyResident"; readonly node: CasNodeInput }
  | { readonly _tag: "NonCanonical" }
  | { readonly _tag: "UnknownKind"; readonly version: number; readonly tag: number }
  | { readonly _tag: "DanglingReference"; readonly missing: ContentId }
  | {
      readonly _tag: "WrongKindReference"
      readonly ref: ContentId
      readonly expectedTag: number
      readonly actualTag: number
    }
  | { readonly _tag: "Collision" }

/** The admitted-bytes fast path for backends that hold canonical
 * encodings: the kind tag is the second byte of every canonical node. */
export const kindTagOfCanonical = (bytes: Uint8Array): number => bytes[1] ?? 0

/** Decode a candidate as exactly one canonical node: closed decode plus
 * byte-identical re-encoding. */
export const canonicalNode = (bytes: Uint8Array): Option.Option<CasNodeInput> => {
  const decoded = decodeCasNode(bytes)
  if (Option.isNone(decoded)) return Option.none()
  return bytesEqual(encodeCasNode(decoded.value), bytes)
    ? decoded
    : Option.none()
}

/** The total pure admission judgment. Check order is law: canonical
 * form, known kind, references in declaration order (absence before
 * kind mismatch, per reference), then residency at the candidate's own
 * address — identical bytes join idempotently, different bytes are the
 * collision. */
export const judgeAdmission = (
  canonicalBytes: Uint8Array,
  facts: AdmissionFacts,
): AdmissionVerdict => {
  const decoded = canonicalNode(canonicalBytes)
  if (Option.isNone(decoded)) return { _tag: "NonCanonical" }
  const node = decoded.value

  if (node.kind.version !== CasSchemeVersion) {
    return { _tag: "UnknownKind", version: node.kind.version, tag: node.kind.tag }
  }

  for (let index = 0; index < node.refs.length; index += 1) {
    const ref = node.refs[index]
    if (ref === undefined) return { _tag: "NonCanonical" }
    const actual = facts.refTags[index]
    if (actual === undefined || Option.isNone(actual)) {
      return { _tag: "DanglingReference", missing: ref.id }
    }
    if (actual.value !== ref.expectedTag) {
      return {
        _tag: "WrongKindReference",
        ref: ref.id,
        expectedTag: ref.expectedTag,
        actualTag: actual.value,
      }
    }
  }

  if (Option.isSome(facts.resident)) {
    return bytesEqual(facts.resident.value, canonicalBytes)
      ? { _tag: "AlreadyResident", node }
      : { _tag: "Collision" }
  }
  return { _tag: "Admit", node }
}
