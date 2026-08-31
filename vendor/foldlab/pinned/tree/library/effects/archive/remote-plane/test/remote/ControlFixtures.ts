import { Effect, Schema } from "effect"
import { decodeCapabilityResult } from "../../src/internal/remoteControl.ts"
import { ManifestModel } from "../conformance/harness.ts"

const Byte = Schema.Int.check(Schema.isBetween({ minimum: 0, maximum: 0xff }))
const Limits = Schema.Struct({
  maxBatchKeys: Schema.Int.check(Schema.isBetween({ minimum: 0, maximum: 0xffff_ffff })),
  maxBlobBytes: Schema.Int.check(Schema.isBetween({ minimum: 0, maximum: 0xffff_ffff })),
})
const ControlResult = Schema.Union([
  Schema.Struct({ _tag: Schema.Literal("Decoded"), limits: Limits }),
  Schema.Struct({ _tag: Schema.Literal("Rejected") }),
])

export const ControlRowSchema = Schema.Struct({
  case: Schema.String,
  expect: ControlResult,
  input: Schema.Struct({ bytes: Schema.Array(Byte) }),
})
export type ControlRow = typeof ControlRowSchema.Type

export const ControlOracle = "Capability documents are eight canonical bytes — two big-endian 32-bit naturals, the key-count limit then the blob-byte limit — parsed by a closed decoder that rejects truncation and trailing content; a successful decode's input is exactly the canonical encoding of its result."

export const controlBinding = {
  family: "RMT-014" as const,
  model: ManifestModel,
  row: ControlRowSchema,
  hasOracle: true as const,
  oracle: ControlOracle,
}

export const runControlRow = (row: ControlRow) =>
  Effect.succeed(decodeCapabilityResult(row.input.bytes))
