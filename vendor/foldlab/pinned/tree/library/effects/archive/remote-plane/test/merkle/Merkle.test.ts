import { expect, it } from "@effect/vitest"
import { Effect } from "effect"
import { assertFamilyRows, loadFamily } from "../conformance/harness.ts"
import {
  mrk001Binding,
  mrk002Binding,
  mrk003Binding,
  mrk005Binding,
  mrk006Binding,
  mrk007Binding,
  mrk011Binding,
  mrk012Binding,
  mrk015Binding,
  realChunk,
  realConsistency,
  realInclusion,
  realOpeningDecode,
  realStep,
  realStreamDecode,
  realFeedAll,
  runChunkRow,
  runConsistencyRow,
  runDecoderRow,
  runInclusionRow,
  runOpeningRow,
  runStreamRow,
  runFramerRow,
} from "./MerkleFixtures.ts"
import { drain } from "../../src/internal/proofFramer.ts"
import { makeRng } from "../remote/fixtures/Rng.ts"

it.effect("MRK-001 consumes every ratified chunk-recipe row structurally", () =>
  assertFamilyRows(mrk001Binding, (row) => runChunkRow(realChunk, row)))

it.effect("MRK-002 consumes every ratified verified-emission row structurally", () =>
  assertFamilyRows(mrk002Binding, (row) => runDecoderRow(realStep, row)))

it.effect("MRK-003 consumes every ratified final-length row structurally", () =>
  assertFamilyRows(mrk003Binding, (row) => runDecoderRow(realStep, row)))

it.effect("MRK-005 consumes every ratified slice-consistency row structurally", () =>
  assertFamilyRows(mrk005Binding, (row) => runDecoderRow(realStep, row)))

it.effect("MRK-006 consumes every ratified inclusion-opening row structurally", () =>
  assertFamilyRows(mrk006Binding, (row) => runInclusionRow(realInclusion, row)))

it.effect("MRK-007 consumes every ratified consistency-proof row structurally", () =>
  assertFamilyRows(mrk007Binding, (row) => runConsistencyRow(realConsistency, row)))

it.effect("MRK-011 consumes every ratified opening-codec row structurally", () =>
  assertFamilyRows(mrk011Binding, (row) => runOpeningRow(realOpeningDecode, row)))

it.effect("MRK-012 consumes every ratified stream-codec row structurally", () =>
  assertFamilyRows(mrk012Binding, (row) => runStreamRow(realStreamDecode, row)))

it.effect("MRK-015 consumes every ratified incremental-framer row structurally", () =>
  assertFamilyRows(mrk015Binding, (row) => runFramerRow(realFeedAll, row)))

it.effect("MRK-015 seeded refragmentations equal single-shot parsing and final-frame truncations never complete", () =>
  Effect.gen(function* () {
    const manifest = yield* loadFamily(mrk015Binding)
    const singleShot = manifest.rows.find((row) => row.case === "single-shot-000")
    const body = singleShot?.input.fragments[0]
    if (body === undefined) return yield* Effect.die("MRK-015 has no single-shot body")
    const expected = drain(body)

    for (let seed = 0; seed < 128; seed += 1) {
      const rng = makeRng(seed)
      const fragments: Array<ReadonlyArray<number>> = []
      let offset = 0
      while (offset < body.length) {
        const length = rng.int(1, Math.min(17, body.length - offset))
        fragments.push(body.slice(offset, offset + length))
        offset += length
      }
      expect(realFeedAll(fragments), `splitmix32 seed ${seed}`).toEqual(expected)
    }

    for (let removed = 1; removed < 5; removed += 1) {
      const truncated = drain(body.slice(0, body.length - removed))
      expect(truncated._tag).toBe("Parsed")
      if (truncated._tag === "Parsed") {
        expect(truncated.remainder.length).toBeGreaterThan(0)
      }
    }
  }))
