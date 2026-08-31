/**
 * The typed-reference marker law (CAS-005) over plain JSON values.
 *
 * A typed reference appears in a payload as exactly `{"$ref": k}`, and
 * the k-th marker in canonical byte order carries index k into the
 * node's reference array — indexes forced, sharing by repeated
 * entries, and the reserved keys refused outside their exact shapes.
 * Canonical order is the order the canonical encoding emits:
 * codepoint-sorted object keys at every depth, arrays in order.
 *
 * Two walks, one order: `markerize` lowers an encode-side value whose
 * references appear as `{"$link": {id, tag}}` sentinels into a
 * marker-bearing payload plus the reference array; `resolveMarkers`
 * is its exact inverse, verifying the forced-index law as it walks.
 * Both refuse — never escape — user data that collides with a
 * reserved key: an escape would invent a second spelling for the same
 * value and split its content identity.
 *
 * Both walks are typed over the closed `Schema.Json` union — the TS
 * twin of the model's `Json.Value` — so the only unparsed boundary is
 * where the caller parses wire text into that union.
 *
 * The two reserved keys are not written here. They are the model's —
 * `Cas.refKey`, and the one object key `Cas.Schema.encRef` writes —
 * and arrive through `lake exe emitgrammar`, beside the kind-tag
 * registry: a payload's identity turns on them, so the two sides of
 * the wire may not hold separate opinions about which two strings they
 * are. What this file carries is the walks, which are a decision
 * procedure and not data.
 */
import { Data, Option, Predicate, Result, Schema } from "effect"
import { Byte, ContentId, type CasReference } from "../cas/Node.ts"
import {
  RefMarkerKey,
  RefSentinelKey,
} from "../cas/generated/grammar/refMarkers.ts"

export { RefMarkerKey, RefSentinelKey }

/** The sentinel body: what a reference field encodes to before the
 * walk assigns indexes. */
const SentinelBody = Schema.Struct({ id: ContentId, tag: Byte })

export type MarkerViolation = Data.TaggedEnum<{
  /** A reserved key appears in plain data, or in a non-exact shape. */
  ReservedKeyCollision: { readonly key: string }
  /** The exact marker/sentinel key with an unusable body. */
  MalformedMarker: { readonly reason: string }
  /** The k-th marker in canonical order does not carry index k. */
  IndexOutOfOrder: { readonly expected: number; readonly actual: number }
  /** Marker count and reference count disagree. */
  CountMismatch: { readonly markers: number; readonly refs: number }
}>
export const MarkerViolation = Data.taggedEnum<MarkerViolation>()

/** One human sentence per violation, for the projection error. */
export const violationReason = (violation: MarkerViolation): string =>
  MarkerViolation.$match(violation, {
    CountMismatch: ({ markers, refs }) =>
      `payload carries ${markers} reference markers but the node carries ${refs} references`,
    IndexOutOfOrder: ({ actual, expected }) =>
      `marker ${expected} in canonical order carries index ${actual} — indexes are forced`,
    MalformedMarker: ({ reason }) => reason,
    ReservedKeyCollision: ({ key }) =>
      `the reserved key "${key}" appears outside its exact shape — rename the field, escapes are refused`,
  })

/** Codepoint order — equal to UTF-8 byte order, the canonical key
 * ordering CAS-004 pins. */
export const compareCodepoints = (left: string, right: string): number => {
  const a = Array.from(left)
  const b = Array.from(right)
  const shorter = Math.min(a.length, b.length)
  for (let index = 0; index < shorter; index += 1) {
    const delta = (a[index]?.codePointAt(0) ?? 0)
      - (b[index]?.codePointAt(0) ?? 0)
    if (delta !== 0) return delta
  }
  return a.length - b.length
}

const isScalar = (
  value: Schema.Json,
): value is null | number | boolean | string =>
  value === null || Predicate.isNumber(value) || Predicate.isBoolean(value)
    || Predicate.isString(value)

/** A JSON object with a plain prototype. The prototype check is
 * defense in depth for values cast into the union at a boundary. */
const isWalkableObject = (
  value: Schema.JsonArray | Schema.JsonObject,
): value is Schema.JsonObject => {
  if (Array.isArray(value)) return false
  const prototype = Object.getPrototypeOf(value)
  return prototype === Object.prototype || prototype === null
}

/** Keys in canonical traversal order. */
const canonicalKeys = (value: Schema.JsonObject): ReadonlyArray<string> =>
  Object.keys(value).toSorted(compareCodepoints)

const exactSingleKey = (
  value: Schema.JsonObject,
  key: string,
): boolean => {
  const keys = Object.keys(value)
  return keys.length === 1 && keys[0] === key
}

export interface MarkerizedValue {
  readonly payload: Schema.Json
  readonly refs: ReadonlyArray<CasReference>
}

/** Lower a sentinel-bearing value: sentinels become markers indexed in
 * canonical order, references accumulate in that order, and a reserved
 * key in plain data refuses the whole encode. */
export const markerize = (
  value: Schema.Json,
): Result.Result<MarkerizedValue, MarkerViolation> => {
  const refs: Array<CasReference> = []

  const walk = (
    current: Schema.Json,
  ): Result.Result<Schema.Json, MarkerViolation> => {
    if (isScalar(current)) return Result.succeed(current)
    if (Array.isArray(current)) {
      const items: Array<Schema.Json> = []
      for (const item of current) {
        const walked = walk(item)
        if (Result.isFailure(walked)) return walked
        items.push(walked.success)
      }
      return Result.succeed(items)
    }
    if (!isWalkableObject(current)) return Result.succeed(current)

    if (RefSentinelKey in current) {
      if (!exactSingleKey(current, RefSentinelKey)) {
        return Result.fail(
          MarkerViolation.ReservedKeyCollision({ key: RefSentinelKey }),
        )
      }
      const body = Schema.decodeUnknownOption(SentinelBody)(
        current[RefSentinelKey],
      )
      if (Option.isNone(body)) {
        return Result.fail(MarkerViolation.MalformedMarker({
          reason: "a $link sentinel must carry exactly {id, tag}",
        }))
      }
      const marker: Schema.JsonObject = { [RefMarkerKey]: refs.length }
      refs.push({ expectedTag: body.value.tag, id: body.value.id })
      return Result.succeed(marker)
    }
    if (RefMarkerKey in current) {
      return Result.fail(
        MarkerViolation.ReservedKeyCollision({ key: RefMarkerKey }),
      )
    }

    const rebuilt: Record<string, Schema.Json> = {}
    // Canonical-order recursion assigns indexes; insertion order of the
    // rebuilt object is cosmetic — the canonical encoding sorts keys.
    for (const key of canonicalKeys(current)) {
      const walked = walk(current[key] ?? null)
      if (Result.isFailure(walked)) return walked
      rebuilt[key] = walked.success
    }
    return Result.succeed(rebuilt)
  }

  return Result.map(walk(value), (payload) => ({ payload, refs }))
}

/** The exact inverse walk: the k-th marker in canonical order must
 * carry index k and resolves to the k-th reference as a sentinel; the
 * counts must agree; reserved keys outside their exact shapes refuse. */
export const resolveMarkers = (
  payload: Schema.Json,
  refs: ReadonlyArray<CasReference>,
): Result.Result<Schema.Json, MarkerViolation> => {
  let next = 0

  const walk = (
    current: Schema.Json,
  ): Result.Result<Schema.Json, MarkerViolation> => {
    if (isScalar(current)) return Result.succeed(current)
    if (Array.isArray(current)) {
      const items: Array<Schema.Json> = []
      for (const item of current) {
        const walked = walk(item)
        if (Result.isFailure(walked)) return walked
        items.push(walked.success)
      }
      return Result.succeed(items)
    }
    if (!isWalkableObject(current)) return Result.succeed(current)

    if (RefMarkerKey in current) {
      if (!exactSingleKey(current, RefMarkerKey)) {
        return Result.fail(
          MarkerViolation.ReservedKeyCollision({ key: RefMarkerKey }),
        )
      }
      const index = current[RefMarkerKey]
      if (!Predicate.isNumber(index) || !Number.isSafeInteger(index)
        || index < 0) {
        return Result.fail(MarkerViolation.MalformedMarker({
          reason: "a $ref marker must carry a non-negative integer index",
        }))
      }
      if (index !== next) {
        return Result.fail(MarkerViolation.IndexOutOfOrder({
          actual: index,
          expected: next,
        }))
      }
      const ref = refs[next]
      if (ref === undefined) {
        return Result.fail(MarkerViolation.CountMismatch({
          markers: next + 1,
          refs: refs.length,
        }))
      }
      next += 1
      return Result.succeed({
        [RefSentinelKey]: { id: ref.id, tag: ref.expectedTag },
      })
    }
    if (RefSentinelKey in current) {
      return Result.fail(
        MarkerViolation.ReservedKeyCollision({ key: RefSentinelKey }),
      )
    }

    const rebuilt: Record<string, Schema.Json> = {}
    for (const key of canonicalKeys(current)) {
      const walked = walk(current[key] ?? null)
      if (Result.isFailure(walked)) return walked
      rebuilt[key] = walked.success
    }
    return Result.succeed(rebuilt)
  }

  return Result.flatMap(walk(payload), (value) =>
    next === refs.length
      ? Result.succeed(value)
      : Result.fail(MarkerViolation.CountMismatch({
          markers: next,
          refs: refs.length,
        })))
}
