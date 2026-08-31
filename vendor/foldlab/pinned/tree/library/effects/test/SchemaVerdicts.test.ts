/**
 * THE DISAGREEMENT VECTOR — the two doors, held to one answer.
 *
 * `library/cas/conformance/schema-verdicts.json` is emitted by executing
 * the Lean model (`lake exe verdicts`): every row carries a revision-1
 * schema-node payload, the verdict `Cas.Schema.ingest` gives that
 * payload, and — where Lean holds values of the code — a list of
 * candidates with the verdict `Cas.Schema.decode` gives each one. No
 * verdict in that file is hand-written, and nothing here derives one
 * side from the other: the corpus is the Lean door's answers, and this
 * suite is the TypeScript door being asked the same questions.
 *
 * Two agreements are gated:
 *
 * - ADMISSION — `Materialize.fromPayload` must succeed exactly where
 *   `ingest` answers `admit`, and must REFUSE, through the failure
 *   channel, exactly where `ingest` names a refusal. A refusal that
 *   arrives as a defect (a raw throw) counts as a disagreement: the
 *   door's job is to refuse by name, not to explode.
 * - VALIDATION — `Materialize.validator` must accept exactly the
 *   candidates `decode` accepts.
 *
 * Red on disagreement is the point (SCHEMA-MATERIALIZATION.md
 * ruling-queue item 19). Where a disagreement is real and its cause is
 * OUTSIDE this lane — an open ruling, or Effect's own behaviour — it is
 * pinned by name in `knownDisagreements` below with the cause written
 * out, and the last statement in this file asserts every pin STILL
 * disagrees, so a fix turns the pin red and forces it to be retired
 * rather than left to rot.
 *
 * One expected disagreement did NOT materialize and is recorded here
 * because the absence is worth as much as a hit: the corpus carries the
 * safe-integer boundary (`int/max-safe`, `int/above-max-safe`,
 * `int/below-min-safe`), and the two doors AGREE on it. Open ruling 3
 * (Integer semantics) reads `isInt` as a bare integer check; it is not
 * — `Schema.isInt` runs `Number.isSafeInteger` (`Schema.ts:8227`), the
 * same bound Lean's `SafeInt` carries. The rev-0/rev-1 spelling
 * question stands; the VALUE-plane disagreement ruling 3 predicts does
 * not exist.
 */
import { expect, it } from "@effect/vitest"
import { Effect, Exit, Layer } from "effect"
import { Cas } from "../src/index.ts"
import { layerDiskFs } from "./fixtures/diskFs.ts"
import { readFixtureString } from "./fixtures/read.ts"

const M = Cas.Materialize
const layer = Layer.mergeAll(Cas.layerMemoryLive, layerDiskFs)
const utf8 = new TextEncoder()

interface ValueCase {
  readonly label: string
  readonly value: unknown
  readonly verdict: "accept" | "refuse"
}

interface CodeCase {
  readonly name: string
  readonly note: string
  readonly payload: string
  readonly denotes: boolean
  readonly verdict: "admit" | "refuse"
  readonly refusal?: string
  readonly values: ReadonlyArray<ValueCase>
}

interface Corpus {
  readonly revision: number
  readonly restrictions: ReadonlyArray<string>
  readonly counts: {
    readonly acceptValues: number
    readonly admittedCodes: number
    readonly codes: number
    readonly refuseValues: number
    readonly refusedCodes: number
    readonly values: number
  }
  readonly cases: ReadonlyArray<CodeCase>
}

const corpus = readFixtureString("../cas/conformance/schema-verdicts.json").pipe(
  Effect.orDie,
  Effect.map((text) => JSON.parse(text) as Corpus),
)

/** The disagreements that are RULINGS, not defects: each is a place
 * where the two doors really answer differently and the estate has not
 * yet decided which answer is canonical. Keys are `<case>` for an
 * admission verdict and `<case>/<label>` for a value verdict. */
const knownDisagreements: ReadonlyMap<string, string> = new Map([
  [
    "struct-empty/excess",
    "UPSTREAM EFFECT DEFECT, found by this corpus (2026-08-29): Effect's decoder skips the excess-property check entirely when an `Objects` node has zero property signatures and zero index signatures, so `Schema.Struct({})` accepts `{\"a\":1}` even under `onExcessProperty: \"error\"`, while the same schema with one field refuses it. Lean's `decodeFields [] (_ :: _)` answers `none`, so the empty struct is exactly where the two doors part. Not a wf question — the CODE is well-formed and both doors admit it — so no gate on the admission path can close it; it is Effect's own validator semantics. Sibling of ruling-queue item 13: report upstream, and decide whether the estate admits the empty struct at all.",
  ],
])

const key = (name: string, label?: string): string =>
  label === undefined ? name : `${name}/${label}`

/** What the TypeScript door does with one payload, in the three
 * outcomes that matter. `defect` is deliberately not folded into
 * `refuse`: a door that throws where the Lean door names a refusal is
 * not agreeing, it is failing differently. */
const admission = (payload: string) =>
  M.fromPayload(utf8.encode(payload)).pipe(
    Effect.exit,
    Effect.map((exit): "admit" | "refuse" | "defect" => {
      if (Exit.isSuccess(exit)) return "admit"
      return Exit.hasDies(exit) ? "defect" : "refuse"
    }),
  )

it.effect("the corpus is what it says it is", () =>
  Effect.gen(function* () {
    const { cases, counts, restrictions, revision } = yield* corpus
    expect(revision).toBe(Cas.CanonicalSchema.Revision)
    expect(restrictions.length).toBeGreaterThan(0)
    expect(cases.length).toBe(counts.codes)
    expect(cases.filter((one) => one.verdict === "admit").length)
      .toBe(counts.admittedCodes)
    expect(cases.filter((one) => one.verdict === "refuse").length)
      .toBe(counts.refusedCodes)
    const values = cases.flatMap((one) => one.values)
    expect(values.length).toBe(counts.values)
    expect(values.filter((one) => one.verdict === "accept").length)
      .toBe(counts.acceptValues)

    // The corpus restriction, checked on the consuming side too: a row
    // Lean holds no values of carries no value triples, and a refused
    // code carries none either.
    for (const one of cases) {
      const carried = `${one.name} ${one.values.length > 0}`
      expect(carried).toBe(`${one.name} ${one.values.length > 0 && one.denotes}`)
      if (one.verdict === "refuse") {
        expect(`${one.name} ${one.values.length}`).toBe(`${one.name} 0`)
        expect(typeof one.refusal).toBe("string")
      }
    }
  }).pipe(Effect.provide(layerDiskFs)))

it.effect("the TypeScript door admits exactly the codes the Lean door admits", () =>
  Effect.gen(function* () {
    const { cases } = yield* corpus
    const disagreements: Array<string> = []
    for (const one of cases) {
      const actual = yield* admission(one.payload)
      if (knownDisagreements.has(key(one.name))) continue
      if (actual !== one.verdict) {
        disagreements.push(
          `${one.name}: Lean ${one.verdict}${
            one.refusal === undefined ? "" : ` (${one.refusal})`
          }, TypeScript ${actual} — ${one.note}`,
        )
      }
    }
    expect(disagreements).toEqual([])
  }).pipe(Effect.provide(layer)))

it.effect("a refused code is refused BY NAME, and by the same name", () =>
  Effect.gen(function* () {
    const { cases } = yield* corpus
    const mismatches: Array<string> = []
    for (const one of cases) {
      if (one.verdict !== "refuse") continue
      if (knownDisagreements.has(key(one.name))) continue
      // `result` keeps TYPED failures in hand; a defect would still blow
      // this statement, which is the reading we want — the door refuses,
      // it does not explode.
      const outcome = yield* Effect.result(M.fromPayload(utf8.encode(one.payload)))
      if (outcome._tag === "Success") continue // the admission statement owns this
      const issue = String((outcome.failure as Cas.ProjectionCodecFailure).issue)
      const named = /SchemaRefusal: (\w+):/.exec(issue)
      if (named === null) {
        mismatches.push(`${one.name}: refused without a name — ${issue.slice(0, 200)}`)
        continue
      }
      if (named[1] !== one.refusal) {
        mismatches.push(
          `${one.name}: Lean names ${one.refusal}, TypeScript names ${named[1]}`,
        )
      }
    }
    expect(mismatches).toEqual([])
  }).pipe(Effect.provide(layer)))

it.effect("the materialized validator agrees with decode on every candidate", () =>
  Effect.gen(function* () {
    const { cases } = yield* corpus
    const disagreements: Array<string> = []
    for (const one of cases) {
      if (one.values.length === 0) continue
      const materialized = yield* M.fromPayload(utf8.encode(one.payload))
      const validate = M.validator(materialized)
      for (const candidate of one.values) {
        if (knownDisagreements.has(key(one.name, candidate.label))) continue
        const exit = yield* Effect.exit(validate(candidate.value))
        const actual = Exit.isSuccess(exit) ? "accept" : "refuse"
        if (actual !== candidate.verdict) {
          disagreements.push(
            `${one.name}/${candidate.label}: Lean ${candidate.verdict}, TypeScript ${actual} — ${
              JSON.stringify(candidate.value)
            }`,
          )
        }
      }
    }
    expect(disagreements).toEqual([])
  }).pipe(Effect.provide(layer)))

it.effect("every pinned disagreement still disagrees", () =>
  Effect.gen(function* () {
    const { cases } = yield* corpus
    const settled: Array<string> = []
    for (const [pin, cause] of knownDisagreements) {
      const [name, label] = pin.split("/") as [string, string | undefined]
      const one = cases.find((row) => row.name === name)
      if (one === undefined) {
        settled.push(`${pin}: no such case in the corpus`)
        continue
      }
      if (label === undefined) {
        const actual = yield* admission(one.payload)
        if (actual === one.verdict) settled.push(`${pin}: now agrees — ${cause}`)
        continue
      }
      const candidate = one.values.find((row) => row.label === label)
      if (candidate === undefined) {
        settled.push(`${pin}: no such candidate in the corpus`)
        continue
      }
      const materialized = yield* M.fromPayload(utf8.encode(one.payload))
      const exit = yield* Effect.exit(M.validator(materialized)(candidate.value))
      const actual = Exit.isSuccess(exit) ? "accept" : "refuse"
      if (actual === candidate.verdict) settled.push(`${pin}: now agrees — ${cause}`)
    }
    // A pin that has stopped disagreeing is a ruling that landed: retire
    // the pin rather than leaving a lie in the file.
    expect(settled).toEqual([])
  }).pipe(Effect.provide(layer)))
