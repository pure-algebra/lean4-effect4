/**
 * Private M4 storage carriers for histories and witnesses.
 *
 * These Schemas validate values after the project-owned binary reader has
 * decoded them. They do not encode digest bytes, and this binary format is an
 * in-memory-adapter detail with no public stability or canonicality claim.
 */
import { Encoding, Predicate, Schema } from "effect"
import { ContentId } from "../cas/Node.ts"

const ReplayMode = Schema.Literals(["record", "replay"])
const MismatchCategory = Schema.Literals([
  "OperationMismatch",
  "RevisionMismatch",
  "RequestMismatch",
  "HistoryExhausted",
  "UnconsumedSuffix",
  "OutcomeInadmissible",
  "DelegationOutstanding",
  "UnsolicitedOutcome",
])

const StoredOutcome = Schema.Union([
  Schema.TaggedStruct("Success", { value: Schema.String }),
  Schema.TaggedStruct("Failure", { error: Schema.String }),
])

export const StoredHistoryEntry = Schema.Struct({
  op: Schema.String,
  revision: Schema.Natural,
  request: Schema.String,
  outcome: StoredOutcome,
})
export type StoredHistoryEntry = typeof StoredHistoryEntry.Type

const StoredTerminalValue = Schema.Union([
  Schema.String,
  Schema.TaggedStruct("Unrepresentable", {}),
])

const StoredTerminal = Schema.Union([
  Schema.TaggedStruct("Succeeded", { value: StoredTerminalValue }),
  Schema.TaggedStruct("Failed", { error: StoredTerminalValue }),
])

const StoredSessionOutcome = Schema.Union([
  Schema.TaggedStruct("Completed", { terminal: StoredTerminal }),
  Schema.TaggedStruct("Rejected", {
    category: MismatchCategory,
    at: Schema.Natural,
    terminalSoFar: Schema.optionalKey(StoredTerminal),
  }),
  Schema.TaggedStruct("Violated", {
    service: Schema.Literals(["Clock", "Random"]),
  }),
  Schema.TaggedStruct("Aborted", {
    reason: Schema.Literals(["Defect", "Interrupted"]),
  }),
])

const StoredDecision = Schema.Union([
  Schema.TaggedStruct("LiveDelegation", {
    operation: Schema.String,
    at: Schema.Natural,
  }),
  Schema.TaggedStruct("OccurrenceAppended", {
    operation: Schema.String,
    at: Schema.Natural,
  }),
  Schema.TaggedStruct("RecordedSubstitution", {
    operation: Schema.String,
    at: Schema.Natural,
  }),
  Schema.TaggedStruct("HistoryConsumed", { at: Schema.Natural }),
  Schema.TaggedStruct("TypedRejection", {
    category: MismatchCategory,
    at: Schema.Natural,
  }),
  Schema.TaggedStruct("Completed", { consumed: Schema.Natural }),
])

export const StoredWitness = Schema.Struct({
  mode: ReplayMode,
  executionId: Schema.String,
  consumed: Schema.Natural,
  trace: Schema.Array(StoredDecision),
  outcome: StoredSessionOutcome,
  historyRoot: Schema.optionalKey(ContentId),
})
export type StoredWitness = typeof StoredWitness.Type

export class InternalStorageError extends Error {
  readonly name = "InternalStorageError"
}

const textEncoder = new TextEncoder()
const textDecoder = new TextDecoder("utf-8", { fatal: true })

class Writer {
  private buffer = new Uint8Array(256)
  private length = 0

  private reserve(additional: number): void {
    const required = this.length + additional
    if (required <= this.buffer.length) return
    let capacity = this.buffer.length
    while (capacity < required) capacity *= 2
    const grown = new Uint8Array(capacity)
    grown.set(this.buffer)
    this.buffer = grown
  }

  byte(value: number): void {
    this.reserve(1)
    this.buffer[this.length] = value & 0xff
    this.length += 1
  }

  uint32(value: number): void {
    if (!Number.isSafeInteger(value) || value < 0 || value > 0xffff_ffff) {
      throw new InternalStorageError(`Length is outside uint32: ${value}`)
    }
    this.reserve(4)
    this.buffer[this.length] = value >>> 24
    this.buffer[this.length + 1] = value >>> 16
    this.buffer[this.length + 2] = value >>> 8
    this.buffer[this.length + 3] = value
    this.length += 4
  }

  raw(bytes: Uint8Array): void {
    this.reserve(bytes.length)
    this.buffer.set(bytes, this.length)
    this.length += bytes.length
  }

  framed(bytes: Uint8Array): void {
    this.uint32(bytes.length)
    this.raw(bytes)
  }

  string(value: string): void {
    this.framed(textEncoder.encode(value))
  }

  number(value: number): void {
    if (!Number.isFinite(value)) {
      throw new InternalStorageError("Non-finite numbers are not storable")
    }
    const bytes = new Uint8Array(8)
    new DataView(bytes.buffer).setFloat64(0, value)
    this.raw(bytes)
  }

  finish(): Uint8Array {
    return this.buffer.slice(0, this.length)
  }
}

class Reader {
  private offset = 0

  constructor(readonly bytes: Uint8Array) {}

  get done(): boolean {
    return this.offset === this.bytes.length
  }

  byte(): number {
    const value = this.bytes[this.offset]
    if (value === undefined) throw new InternalStorageError("Unexpected end of input")
    this.offset += 1
    return value
  }

  uint32(): number {
    return this.byte() * 0x1000000
      + this.byte() * 0x10000
      + this.byte() * 0x100
      + this.byte()
  }

  raw(length: number): Uint8Array {
    const end = this.offset + length
    if (end > this.bytes.length) throw new InternalStorageError("Truncated frame")
    const value = this.bytes.slice(this.offset, end)
    this.offset = end
    return value
  }

  framed(): Uint8Array {
    return this.raw(this.uint32())
  }

  string(): string {
    try {
      return textDecoder.decode(this.framed())
    } catch (cause) {
      throw new InternalStorageError(`Invalid UTF-8: ${String(cause)}`)
    }
  }

  number(): number {
    return new DataView(this.raw(8).buffer).getFloat64(0)
  }
}

/** The closed universe the binary reader can produce: every decoded
 * carrier value is one of these shapes and nothing else. The writer
 * still accepts `unknown` — feeding it arbitrary values and throwing on
 * unsupported ones is its contract (the terminal-encoding path relies
 * on exactly that). */
type StoredValue =
  | null
  | boolean
  | number
  | string
  | bigint
  | Uint8Array
  | ReadonlyArray<StoredValue>
  | { readonly [key: string]: StoredValue }

const writeValue = (writer: Writer, value: unknown): void => {
  if (value === null) {
    writer.byte(0)
    return
  }
  if (value === false) {
    writer.byte(1)
    return
  }
  if (value === true) {
    writer.byte(2)
    return
  }
  if (Predicate.isNumber(value)) {
    writer.byte(3)
    writer.number(value)
    return
  }
  if (Predicate.isString(value)) {
    writer.byte(4)
    writer.string(value)
    return
  }
  if (Array.isArray(value)) {
    writer.byte(5)
    writer.uint32(value.length)
    for (const item of value) writeValue(writer, item)
    return
  }
  if (value instanceof Uint8Array) {
    writer.byte(6)
    writer.framed(value)
    return
  }
  if (Predicate.isBigInt(value)) {
    writer.byte(7)
    writer.string(value.toString(10))
    return
  }
  if (Predicate.isObject(value)) {
    const prototype = Object.getPrototypeOf(value)
    if (prototype !== Object.prototype && prototype !== null) {
      throw new InternalStorageError("Stored objects must have a plain prototype")
    }
    writer.byte(8)
    const entries = Object.entries(value).sort(([left], [right]) =>
      left < right ? -1 : left > right ? 1 : 0)
    writer.uint32(entries.length)
    for (const [key, entry] of entries) {
      writer.string(key)
      writeValue(writer, entry)
    }
    return
  }
  throw new InternalStorageError(`Unsupported stored value: ${typeof value}`)
}

const readValue = (reader: Reader): StoredValue => {
  switch (reader.byte()) {
    case 0:
      return null
    case 1:
      return false
    case 2:
      return true
    case 3:
      return reader.number()
    case 4:
      return reader.string()
    case 5: {
      const output: Array<StoredValue> = []
      const length = reader.uint32()
      for (let index = 0; index < length; index += 1) output.push(readValue(reader))
      return output
    }
    case 6:
      return reader.framed()
    case 7:
      try {
        return BigInt(reader.string())
      } catch (cause) {
        throw new InternalStorageError(`Invalid bigint: ${String(cause)}`)
      }
    case 8: {
      const output: Record<string, StoredValue> = {}
      const length = reader.uint32()
      for (let index = 0; index < length; index += 1) {
        Object.defineProperty(output, reader.string(), {
          value: readValue(reader),
          enumerable: true,
          configurable: true,
          writable: true,
        })
      }
      return output
    }
    default:
      throw new InternalStorageError("Unknown internal value tag")
  }
}

const CarrierMagic = Uint8Array.from([0x46, 0x4c, 0x52, 0x50, 0x01])
const HistoryCarrier = 1
const WitnessCarrier = 2

const encodeCarrier = (
  carrier: number,
  value: StoredHistoryEntry | StoredWitness,
): Uint8Array => {
  const writer = new Writer()
  writer.raw(CarrierMagic)
  writer.byte(carrier)
  writeValue(writer, value)
  return writer.finish()
}

const decodeCarrier = (carrier: number, bytes: Uint8Array): StoredValue => {
  const reader = new Reader(bytes)
  for (const expected of CarrierMagic) {
    if (reader.byte() !== expected) throw new InternalStorageError("Wrong carrier prefix")
  }
  if (reader.byte() !== carrier) throw new InternalStorageError("Wrong carrier kind")
  const value = readValue(reader)
  if (!reader.done) throw new InternalStorageError("Trailing carrier bytes")
  return value
}

export const encodeStoredValue = (value: unknown): string => {
  const writer = new Writer()
  writeValue(writer, value)
  return Encoding.encodeHex(writer.finish())
}

export const decodeStoredValue = (encoded: string): unknown => {
  const bytes = Encoding.decodeHex(encoded)
  if (bytes._tag === "Failure") {
    throw new InternalStorageError("Stored value is not hexadecimal")
  }
  const reader = new Reader(bytes.success)
  const value = readValue(reader)
  if (!reader.done) throw new InternalStorageError("Trailing stored-value bytes")
  return value
}

export const encodeHistoryEntry = (entry: StoredHistoryEntry): Uint8Array =>
  encodeCarrier(HistoryCarrier, entry)

export const decodeHistoryEntry = (bytes: Uint8Array): unknown =>
  decodeCarrier(HistoryCarrier, bytes)

export const encodeWitness = (witness: StoredWitness): Uint8Array =>
  encodeCarrier(WitnessCarrier, witness)

export const decodeWitness = (bytes: Uint8Array): unknown =>
  decodeCarrier(WitnessCarrier, bytes)
