/**
 * Assertion-shape rule (ratified): `toEqual` for values — an added field
 * is a real difference — and `toMatchObject` only where a payload is
 * deliberately partial (error evidence whose incidental fields are not
 * under test). The case-labeled `expect({ case, ... }).toEqual({ case,
 * ... })` form below is the house shape for row-driven suites.
 */
import { expect } from "@effect/vitest"
import { Effect, Equal, Schema } from "effect"
import { layerDiskFs } from "../fixtures/diskFs.ts"
import { readFixtureString } from "../fixtures/read.ts"
import { ManifestModel } from "./suiteIndex.ts"

/** The committed manifest index lives in the one suite-structure seam
 * (`./suiteIndex.ts`); re-exported so consumers keep one import. */
export { ManifestModel, manifestIndexNames } from "./suiteIndex.ts"

/** A manifest that could not be read or decoded — tagged so harness
 * failures stay distinct in the error channel. */
export class ManifestReadError extends Schema.TaggedError<ManifestReadError>()(
  "ManifestReadError",
  { cause: Schema.Defect() },
) {}

type ContextFreeSchema = Schema.Top & {
  readonly DecodingServices: never
  readonly EncodingServices: never
}

export type FamilyBinding<
  Family extends string,
  RowSchema extends ContextFreeSchema,
> = {
  readonly family: Family
  readonly model: typeof ManifestModel
  readonly row: RowSchema
} & (
  | { readonly hasOracle: false }
  | { readonly hasOracle: true; readonly oracle: string }
)

type RowWithExpectation = {
  readonly case: string
  readonly expect: unknown
}

export type LoadedFamily<Row> = {
  readonly family: string
  readonly meaning: string
  readonly model: typeof ManifestModel
  readonly rows: ReadonlyArray<Row>
  readonly oracle?: string
}

const manifestSchema = <
  Family extends string,
  RowSchema extends ContextFreeSchema,
>(
  binding: FamilyBinding<Family, RowSchema>,
): Schema.Decoder<LoadedFamily<RowSchema["Type"]>, never> => {
  if (binding.hasOracle) {
    return Schema.Struct({
      family: Schema.Literal(binding.family),
      meaning: Schema.String,
      model: Schema.Literal(binding.model),
      oracle: Schema.Literal(binding.oracle),
      rows: Schema.Array(binding.row),
    })
  }
  return Schema.Struct({
    family: Schema.Literal(binding.family),
    meaning: Schema.String,
    model: Schema.Literal(binding.model),
    rows: Schema.Array(binding.row),
  })
}

/** Load only a committed, model-pinned manifest through a closed envelope. */
export const loadFamily = <
  Family extends string,
  RowSchema extends ContextFreeSchema,
>(
  binding: FamilyBinding<Family, RowSchema>,
): Effect.Effect<
  LoadedFamily<RowSchema["Type"]>,
  ManifestReadError | Schema.SchemaError
> => Effect.gen(function* () {
  const json = yield* readFixtureString(
    `archive/lean-model-0.3/conformance/manifest/${binding.family}.json`,
  ).pipe(
    Effect.map((text) => JSON.parse(text) as unknown),
    Effect.mapError((cause) => new ManifestReadError({ cause })),
    Effect.provide(layerDiskFs),
  )
  const decoded = yield* Schema.decodeUnknownEffect(manifestSchema(binding))(json, {
    onExcessProperty: "error",
  })
  return {
    family: decoded.family,
    meaning: decoded.meaning,
    model: decoded.model,
    rows: decoded.rows,
    ...(binding.hasOracle ? { oracle: binding.oracle } : {}),
  }
})

export type RowEvaluator<Row, Actual> = (
  row: Row,
) => Effect.Effect<Actual>

export interface HarnessCase<Input, Expected> {
  readonly case: string
  readonly input: Input
  readonly expect: Expected
}

/**
 * Run a closed engineering case table with the same named structural report
 * used for committed family rows. These observations are not model evidence.
 */
export const assertCaseTable = <Input, Expected, Error, Services>(
  cases: ReadonlyArray<HarnessCase<Input, Expected>>,
  evaluate: (
    input: Input,
    caseName: string,
  ) => Effect.Effect<Expected, Error, Services>,
): Effect.Effect<void, Error, Services> => Effect.gen(function* () {
  if (cases.length === 0) {
    return yield* Effect.die(new Error("harness case table must be non-empty"))
  }
  for (const item of cases) {
    const actual = yield* evaluate(item.input, item.case)
    expect({ case: item.case, result: actual }).toEqual({
      case: item.case,
      result: item.expect,
    })
  }
})

/** Compare every row structurally; an empty vector family is a harness error. */
export const assertFamilyRows = <
  Family extends string,
  RowSchema extends ContextFreeSchema & { readonly Type: RowWithExpectation },
  Actual,
>(
  binding: FamilyBinding<Family, RowSchema>,
  evaluate: RowEvaluator<RowSchema["Type"], Actual>,
) => Effect.gen(function* () {
  const manifest = yield* loadFamily(binding)
  if (manifest.rows.length === 0) {
    return yield* Effect.die(new Error(`${binding.family}: manifest rows must be non-empty`))
  }
  for (const row of manifest.rows) {
    const actual = yield* evaluate(row)
    expect({ case: row.case, result: actual }).toEqual({
      case: row.case,
      result: row.expect,
    })
  }
})

/** Pure structural witness extraction, exported only for the harness self-test. */
export const findKillWitnesses = <Row extends RowWithExpectation, Actual>(
  rows: ReadonlyArray<Row>,
  evaluate: (row: Row) => Actual,
): ReadonlyArray<string> => rows
  .filter((row) => !Equal.equals(evaluate(row), row.expect))
  .map((row) => row.case)

/** Assert direction-2 red and return the case ids that kill the mutant. */
export const assertFamilyRed = <
  Family extends string,
  RowSchema extends ContextFreeSchema & { readonly Type: RowWithExpectation },
  Actual,
>(
  binding: FamilyBinding<Family, RowSchema>,
  mutant: RowEvaluator<RowSchema["Type"], Actual>,
) => Effect.gen(function* () {
  const manifest = yield* loadFamily(binding)
  if (manifest.rows.length === 0) {
    return yield* Effect.die(new Error(`${binding.family}: manifest rows must be non-empty`))
  }
  const witnesses: Array<string> = []
  for (const row of manifest.rows) {
    const actual = yield* mutant(row)
    if (!Equal.equals(actual, row.expect)) witnesses.push(row.case)
  }
  expect(
    witnesses.length,
    `${binding.family} kill witnesses: ${witnesses.join(", ")}`,
  ).toBeGreaterThan(0)
  return witnesses
})
