/**
 * The typed-reference marker law (CAS-005), fixture-for-fixture with
 * the Lean model: canonical-order assignment, forced indexes, sharing
 * by repeated entries, collision refusal both directions, and the
 * exact inverse round trip.
 */
import { expect, it } from "@effect/vitest"
import { Effect, Result, type Schema } from "effect"
import { ContentId, type CasReference } from "../src/cas/Node.ts"
import {
  markerize,
  resolveMarkers,
  violationReason,
  type MarkerViolation,
} from "../src/internal/refMarkers.ts"

const idA = ContentId.make("01".repeat(32))
const idB = ContentId.make("02".repeat(32))

const linkA = { $link: { id: idA, tag: 5 } }
const linkB = { $link: { id: idB, tag: 7 } }

const refA: CasReference = { expectedTag: 5, id: idA }
const refB: CasReference = { expectedTag: 7, id: idB }

const lowered = (value: Schema.Json) => Result.getOrThrowWith(
  markerize(value),
  (violation) => new Error(violationReason(violation)),
)

const refused = (value: Schema.Json): MarkerViolation => {
  const result = markerize(value)
  if (Result.isSuccess(result)) throw new Error("expected a refusal")
  return result.failure
}

const resolveRefused = (
  payload: Schema.Json,
  refs: ReadonlyArray<CasReference>,
): MarkerViolation => {
  const result = resolveMarkers(payload, refs)
  if (Result.isSuccess(result)) throw new Error("expected a refusal")
  return result.failure
}

it.effect("assignment follows canonical key order, not declaration order", () =>
  Effect.sync(() => {
    // Declared b-first; canonical order puts a first, so a's link
    // takes index 0 — the load-bearing fixture.
    const { payload, refs } = lowered({ b: linkA, a: linkB })
    expect(payload).toEqual({ a: { $ref: 0 }, b: { $ref: 1 } })
    expect(refs).toEqual([refB, refA])
  }))

it.effect("a single link beside plain fields markers cleanly", () =>
  Effect.sync(() => {
    const { payload, refs } = lowered({ author: linkA, title: "hi" })
    expect(payload).toEqual({ author: { $ref: 0 }, title: "hi" })
    expect(refs).toEqual([refA])
  }))

it.effect("sharing one target is two markers and two entries", () =>
  Effect.sync(() => {
    const { payload, refs } = lowered([linkA, linkA])
    expect(payload).toEqual([{ $ref: 0 }, { $ref: 1 }])
    expect(refs).toEqual([refA, refA])
  }))

it.effect("nested composites assign depth-first in canonical order", () =>
  Effect.sync(() => {
    const { payload, refs } = lowered({
      z: 3,
      list: [linkB, { deep: linkA }],
    })
    expect(payload).toEqual({
      list: [{ $ref: 0 }, { deep: { $ref: 1 } }],
      z: 3,
    })
    expect(refs).toEqual([refB, refA])
  }))

it.effect("plain values with no links lower to themselves and no refs", () =>
  Effect.sync(() => {
    const { payload, refs } = lowered({ k: [1, 2] })
    expect(payload).toEqual({ k: [1, 2] })
    expect(refs).toEqual([])
  }))

it.effect("reserved keys in plain data refuse the encode — never escape", () =>
  Effect.sync(() => {
    expect(refused({ data: { $ref: 0 } })._tag).toBe("ReservedKeyCollision")
    expect(refused({ $ref: "x", y: 1 })._tag).toBe("ReservedKeyCollision")
    // The sentinel key is equally reserved on the way in.
    expect(refused({ $link: "not a sentinel body" })._tag).toBe("MalformedMarker")
    expect(refused({ $link: linkA.$link, extra: 1 })._tag)
      .toBe("ReservedKeyCollision")
    // Deep inside composites too.
    expect(refused([{ fine: 1 }, { nested: { $ref: 2 } }])._tag)
      .toBe("ReservedKeyCollision")
  }))

it.effect("resolve is the exact inverse on every lowering", () =>
  Effect.sync(() => {
    const fixtures: ReadonlyArray<Schema.Json> = [
      { b: linkA, a: linkB },
      { author: linkA, title: "hi" },
      [linkA, linkA],
      { z: 3, list: [linkB, { deep: linkA }] },
      { k: [1, 2] },
      "scalar",
      null,
    ]
    for (const fixture of fixtures) {
      const { payload, refs } = lowered(fixture)
      const back = resolveMarkers(payload, refs)
      expect(Result.isSuccess(back)).toBe(true)
      // Canonical-order rebuild may reorder keys; deep equality is the
      // contract, byte order belongs to the canonical encoding.
      expect(Result.getOrThrow(back)).toEqual(fixture)
    }
  }))

it.effect("the forced-index law refuses every disordered payload", () =>
  Effect.sync(() => {
    const two = [refA, refB]
    expect(resolveRefused({ a: { $ref: 1 }, b: { $ref: 0 } }, two))
      .toEqual({ _tag: "IndexOutOfOrder", actual: 1, expected: 0 })
    expect(resolveRefused([{ $ref: 0 }, { $ref: 2 }], [refA, refB, refB])._tag)
      .toBe("IndexOutOfOrder")
    expect(resolveRefused([{ $ref: 0 }, { $ref: 0 }], two)._tag)
      .toBe("IndexOutOfOrder")
    expect(resolveRefused([{ $ref: 0 }], two))
      .toEqual({ _tag: "CountMismatch", markers: 1, refs: 2 })
    expect(resolveRefused({ a: { $ref: 0 } }, [])._tag).toBe("CountMismatch")
  }))

it.effect("malformed markers and payload sentinels refuse the decode", () =>
  Effect.sync(() => {
    expect(resolveRefused({ $ref: 0, x: 1 }, [refA])._tag)
      .toBe("ReservedKeyCollision")
    expect(resolveRefused({ $ref: "0" }, [refA])._tag).toBe("MalformedMarker")
    expect(resolveRefused({ $ref: -1 }, [refA])._tag).toBe("MalformedMarker")
    expect(resolveRefused({ $ref: 0.5 }, [refA])._tag).toBe("MalformedMarker")
    // A payload must never carry a sentinel — that shape exists only
    // on the encode side of the walk.
    expect(resolveRefused({ field: linkA }, [refA])._tag)
      .toBe("ReservedKeyCollision")
  }))

it.effect("marker order is canonical byte order under astral keys too", () =>
  Effect.sync(() => {
    // Codepoint order puts U+E000 before U+10000; UTF-16 code-unit
    // order would reverse them — the CAS-004 fixture, restated for
    // marker assignment.
    const astral = String.fromCodePoint(0x10000)
    const privateUse = String.fromCodePoint(0xe000)
    const { payload, refs } = lowered({ [astral]: linkA, [privateUse]: linkB })
    expect((payload as Record<string, { readonly $ref: number }>)[privateUse])
      .toEqual({ $ref: 0 })
    expect((payload as Record<string, { readonly $ref: number }>)[astral])
      .toEqual({ $ref: 1 })
    expect(refs).toEqual([refB, refA])
  }))
