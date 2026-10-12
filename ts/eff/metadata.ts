/** Structural Ty metadata. The signature and wire tags come from the existing Lean family.
 * This source adapter refuses unsupported syntax and inexact JavaScript naturals.
 * The unrestricted structural retraction is proved in Laws/Codegen/Metadata.lean. */
import { Schema } from "effect"
import { Ty } from "./eff.gen.ts"
import { metadataFrameTags, typeMetadataConstructors, type TypeMetadataShape } from "./wire.gen.ts"
import type { Expr } from "./read.ts"

const isTy = Schema.is(Ty)
const textEncoder = new TextEncoder()
const textDecoder = new TextDecoder("utf-8", { fatal: true })

const array = (expression: Expr): ReadonlyArray<Expr> | undefined =>
  expression._tag === "arr" ? expression.items : undefined

/** Canonical base-256 digits, with an exact safe-integer result or an explicit refusal. */
const natural = (expression: Expr): number | undefined => {
  const digits = array(expression)
  if (digits === undefined) return undefined
  let value = 0
  for (const [index, digit] of digits.entries()) {
    if (digit._tag !== "int" || !Number.isInteger(digit.value) || Object.is(digit.value, -0) ||
        digit.value < 0 || digit.value > 255 || (index === 0 && digit.value === 0)) return undefined
    value = value * 256 + digit.value
    if (!Number.isSafeInteger(value)) return undefined
  }
  return value
}

const frame = (expression: Expr, tag: number, length: number): ReadonlyArray<Expr> | undefined => {
  const items = array(expression)
  return items?.length === length && items[0]?._tag === "int" && items[0].value === tag ? items : undefined
}

/** A structure's fields: constructor 0 with exactly `length` fields. */
const structure = (expression: Expr, length: number): ReadonlyArray<Expr> | undefined => {
  const items = frame(expression, metadataFrameTags.ctor, 3)
  const fields = items && natural(items[1]!) === 0 ? array(items[2]!) : undefined
  return fields?.length === length ? fields : undefined
}

/** A one-natural structure's value: a key's name or service code. */
const code = (expression: Expr): number | undefined => {
  const fields = structure(expression, 1)
  return fields && (readShape({ kind: "nat" }, fields[0]!) as number | undefined)
}

type Key = { readonly name: { readonly value: number }; readonly service: { readonly value: number } }

/** `ServiceKey.Lt`: by name, then by service. */
const keyBefore = (a: unknown, b: unknown): boolean => {
  const x = a as Key, y = b as Key
  return x.name.value < y.name.value || (x.name.value === y.name.value && x.service.value < y.service.value)
}

const readShape = (shape: TypeMetadataShape, expression: Expr): unknown => {
  switch (shape.kind) {
    case "nat": {
      const items = frame(expression, metadataFrameTags.nat, 2)
      return items && natural(items[1]!)
    }
    case "bool": {
      const items = frame(expression, metadataFrameTags.bool, 2)
      return items?.[1]?._tag === "bool" ? items[1].value : undefined
    }
    case "string": {
      const items = frame(expression, metadataFrameTags.string, 2)
      if (items?.[1]?._tag !== "str") return undefined
      const value = items[1].value
      return textDecoder.decode(textEncoder.encode(value)) === value ? value : undefined
    }
    case "ty": return readRawType(expression)
    // a service key: the structure of its two codes (`Effect4.ServiceKey`, constructor 0)
    case "key": {
      const fields = structure(expression, 2)
      const name = fields && code(fields[0]!), service = fields && code(fields[1]!)
      return name === undefined || service === undefined ? undefined : { name: { value: name }, service: { value: service } }
    }
    case "list": {
      const items = frame(expression, metadataFrameTags.list, 2)
      const values = items && array(items[1]!)
      if (values === undefined) return undefined
      const result: unknown[] = []
      for (const item of values) {
        const value = readShape(shape.inner, item)
        if (value === undefined) return undefined
        result.push(value)
      }
      // a row of keys decodes only strictly ascending (`Store/Domain/RowCanonical.lean`)
      if (shape.inner.kind === "key" && !result.every((key, index) => index === 0 || keyBefore(result[index - 1], key))) return undefined
      return result
    }
    case "pair": {
      const items = frame(expression, metadataFrameTags.pair, 3)
      if (items === undefined) return undefined
      const left = readShape(shape.left, items[1]!)
      const right = readShape(shape.right, items[2]!)
      return left === undefined || right === undefined ? undefined : [left, right]
    }
  }
}

const readRawType = (expression: Expr): unknown => {
  const items = frame(expression, metadataFrameTags.ctor, 3)
  if (items === undefined) return undefined
  const tag = natural(items[1]!)
  const fields = array(items[2]!)
  const constructor = typeMetadataConstructors.find(candidate => candidate.tag === tag)
  if (constructor === undefined || fields?.length !== constructor.fields.length) return undefined
  const result: Record<string, unknown> = { _tag: constructor.name }
  for (const [index, field] of constructor.fields.entries()) {
    const value = readShape(field.shape, fields[index]!)
    if (value === undefined) return undefined
    result[field.name] = value
  }
  return result
}

/** Reconstruct raw declaration data; formation and type normalization remain separate. */
export const readTypeMetadata = (expression: Expr): Ty | undefined => {
  const value = readRawType(expression)
  return isTy(value) ? value : undefined
}
