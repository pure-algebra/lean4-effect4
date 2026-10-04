/** Source-side annotation comparison for Codegen.Types.ofTy.
 * Ty remains the generated carrier. Policy tables retain their Lean owners.
 * Cross-language fixtures measure this adapter; they do not prove a simulation. */
import type { Ty } from "./eff.gen.ts"
import { typeMetadataConstructors, typeLeafEdges, typeVariances, targetReservedIdentifiers } from "./wire.gen.ts"

const unrecognized = (_type: never): never => { throw new Error("unknown generated Ty constructor") }
const bytes = (text: string): number[] => [...new TextEncoder().encode(text)]
const compare = (left: readonly number[], right: readonly number[]): number => {
  for (let index = 0; index < Math.min(left.length, right.length); index++) {
    const delta = left[index]! - right[index]!
    if (delta !== 0) return delta
  }
  return left.length - right.length
}
const code = (type: Ty): number => {
  const entry = typeMetadataConstructors.find(entry => entry.name === type._tag)
  if (entry === undefined) throw new Error(`missing generated type constructor ${type._tag}`)
  return entry.keyTag
}
const prefixed = (values: number[]): number[] => [values.length, ...values]
const itemKeys = (items: readonly Ty[]): number[] => [...items.flatMap(item => [1, ...prefixed(key(item))]), 0]

/** Ty.key, whose numeric prefix is read from the core key function. */
export const key = (type: Ty): number[] => {
  const head = code(type)
  switch (type._tag) {
    case "handle": return [head, ...bytes(type.target)]
    case "lit": return [head, ...bytes(type.value)]
    case "var": return [head, type.index]
    case "option": case "list": return [head, ...key(type.inner)]
    case "causeOf": return [head, ...key(type.error)]
    case "refOf": return [head, ...key(type.value)]
    case "prod": case "union": return [head, ...prefixed(key(type.left)), ...key(type.right)]
    case "except": return [head, ...prefixed(key(type.error)), ...key(type.value)]
    case "exitOf": case "fiberOf": case "deferredOf": return [head, ...prefixed(key(type.value)), ...key(type.error)]
    case "map": return [head, ...prefixed(key(type.key)), ...key(type.value)]
    case "record": return [head, ...type.fields.flatMap(([name, [optional, value]]) =>
      [1, ...prefixed(bytes(name)), optional ? 1 : 0, ...prefixed(key(value))]), 0]
    case "tuple": return [head, ...itemKeys(type.items)]
    case "app": return [head, ...prefixed(bytes(type.name)), ...itemKeys(type.args)]
    case "never": case "unit": case "nat": case "int": case "string": case "bool":
    case "unknown": case "null": case "undefined": case "number": case "bytes": return [head]
    default: return unrecognized(type)
  }
}
const equal = (left: Ty, right: Ty): boolean => compare(key(left), key(right)) === 0
const canonicalFields = (fields: Extract<Ty, { _tag: "record" }>["fields"]): typeof fields => {
  const seen = new Set<string>()
  return fields.filter(([name]) => !seen.has(name) && (seen.add(name), true))
    .sort((a, b) => compare(bytes(a[0]), bytes(b[0])))
}
const leafBelow = (left: string, right: string): boolean => {
  if (left === right) return false
  const seen = new Set([left])
  const pending = [left]
  while (pending.length > 0) {
    const head = pending.pop()!
    for (const [from, to] of typeLeafEdges) {
      if (from !== head || seen.has(to)) continue
      if (to === right) return true
      seen.add(to); pending.push(to)
    }
  }
  return false
}

/** Ty.sub on raw inputs, including exact record heads and invariant map keys. */
export const subtype = (a: Ty, b: Ty): boolean => {
  if (equal(a, b) || leafBelow(a._tag, b._tag) || a._tag === "never") return true
  if (a._tag === "union") return subtype(a.left, b) && subtype(a.right, b)
  if (b._tag === "union") return subtype(a, b.left) || subtype(a, b.right)
  if (b._tag === "unknown") return true
  switch (a._tag) {
    case "option": return b._tag === "option" && subtype(a.inner, b.inner)
    case "list": return b._tag === "list" && subtype(a.inner, b.inner)
    case "prod": return b._tag === "prod" && subtype(a.left, b.left) && subtype(a.right, b.right)
    case "except": return b._tag === "except" && subtype(a.error, b.error) && subtype(a.value, b.value)
    case "exitOf": return b._tag === "exitOf" && subtype(a.value, b.value) && subtype(a.error, b.error)
    case "fiberOf": return b._tag === "fiberOf" && subtype(a.value, b.value) && subtype(a.error, b.error)
    case "causeOf": return b._tag === "causeOf" && subtype(a.error, b.error)
    case "refOf": return b._tag === "refOf" && subtype(a.value, b.value) && subtype(b.value, a.value)
    case "deferredOf": return b._tag === "deferredOf" && subtype(a.value, b.value) && subtype(b.value, a.value) &&
      subtype(a.error, b.error) && subtype(b.error, a.error)
    case "record": {
      if (b._tag !== "record") return false
      const left = canonicalFields(a.fields), right = canonicalFields(b.fields)
      return left.length === right.length && left.every(([name, [optional, value]], index) => {
        const other = right[index]!
        return name === other[0] && optional === other[1][0] && subtype(value, other[1][1])
      })
    }
    case "map": return b._tag === "map" && subtype(a.key, b.key) && subtype(b.key, a.key) && subtype(a.value, b.value)
    case "tuple": return b._tag === "tuple" && a.items.length === b.items.length &&
      a.items.every((value, index) => subtype(value, b.items[index]!))
    case "app": return b._tag === "app" && a.name === b.name && a.args.length === b.args.length &&
      a.args.every((value, index) => {
        const other = b.args[index]!, variance = typeVariances[a.name]?.[index] ?? "inv"
        return variance === "co" ? subtype(value, other) : variance === "contra" ? subtype(other, value) :
          subtype(value, other) && subtype(other, value)
      })
    default: return false
  }
}
const members = (type: Ty): Ty[] => type._tag === "never" ? [] :
  type._tag === "union" ? [...members(type.left), ...members(type.right)] : [type]
const factors = (type: Ty): Ty[] => type._tag === "never" ? [type] : members(type)
const union = (values: readonly Ty[]): Ty => {
  const sorted = [...values].sort((a, b) => compare(key(a), key(b)))
  const unique = sorted.filter((value, index) => index === 0 || !equal(value, sorted[index - 1]!))
  const maximal = unique.filter(value => !unique.some(other => subtype(value, other) && !subtype(other, value)))
  if (maximal.length === 0) return { _tag: "never" }
  return maximal.slice(0, -1).reduceRight<Ty>((right, left) => ({ _tag: "union", left, right }), maximal.at(-1)!)
}
const product = (left: Ty, right: Ty): Ty => union(factors(left).flatMap(a =>
  factors(right).map((b): Ty => ({ _tag: "prod", left: a, right: b }))))

/** Deep canonicalization mirrors Ty.normalize, including distributed two-item tuples. */
export const normalize = (type: Ty): Ty => {
  switch (type._tag) {
    case "option": case "list": return { ...type, inner: normalize(type.inner) }
    case "causeOf": return { ...type, error: normalize(type.error) }
    case "refOf": return { ...type, value: normalize(type.value) }
    case "prod": return product(normalize(type.left), normalize(type.right))
    case "union": return union([...members(normalize(type.left)), ...members(normalize(type.right))])
    case "except": case "exitOf": case "fiberOf": case "deferredOf":
      return { ...type, value: normalize(type.value), error: normalize(type.error) }
    case "record": return { _tag: "record", fields: canonicalFields(type.fields.map(([name, [optional, value]]) =>
      [name, [optional, normalize(value)]] as const)) }
    case "map": return { _tag: "map", key: normalize(type.key), value: normalize(type.value) }
    case "tuple": {
      const items = type.items.map(normalize)
      return items.length === 2 ? product(items[0]!, items[1]!) : { _tag: "tuple", items }
    }
    case "app": return type.args.length === 0 ? { _tag: "handle", target: type.name } : { ...type, args: type.args.map(normalize) }
    case "never": case "unit": case "nat": case "int": case "string": case "bool":
    case "unknown": case "null": case "undefined": case "number": case "bytes":
    case "handle": case "lit": case "var": return type
    default: return unrecognized(type)
  }
}

export const targetIdentifier = (name: string): boolean =>
  /^[A-Za-z_$][A-Za-z0-9_$]*$/.test(name) && !targetReservedIdentifiers.includes(name)
export const quoteType = (text: string): string =>
  `"${text.replace(/\\/g, "\\\\").replace(/"/g, '\\"').replace(/\n/g, "\\n").replace(/\r/g, "\\r").replace(/\t/g, "\\t")}"`
export const recordKeyForm = (names: readonly string[]): "plain" | "quoted" | "computed" =>
  names.includes("__proto__") ? "computed" : names.every(targetIdentifier) ? "plain" : "quoted"

/** Flatten only top-level union spelling; quoted text and nested type arguments stay intact. */
export const unionParts = (text: string): string[] => {
  const parts: string[] = []
  let depth = 0, quote = "", escaped = false, start = 0
  for (let index = 0; index < text.length; index++) {
    const character = text[index]!
    if (quote !== "") {
      if (escaped) escaped = false
      else if (character === "\\") escaped = true
      else if (character === quote) quote = ""
    } else if (character === "\"" || character === "'") quote = character
    else if ("<([{ ".trim().includes(character)) depth++
    else if (">)]}".includes(character)) depth--
    else if (character === "|" && depth === 0) { parts.push(text.slice(start, index).trim()); start = index + 1 }
  }
  parts.push(text.slice(start).trim())
  return parts
}

/** The target renderer returns a refusal when Codegen.Types has no structural projection. */
export const targetType = (raw: Ty, legacy: (text: string) => string | undefined): string | undefined => {
  const render = (type: Ty): string | undefined => {
    const generic = (head: string, args: readonly Ty[]): string | undefined => {
      const values = args.map(render)
      return values.some(value => value === undefined) ? undefined : `${head}<${values.join(", ")}>`
    }
    const tuple = (items: readonly Ty[]): string | undefined => {
      const values = items.map(render)
      return values.some(value => value === undefined) ? undefined : `readonly [${values.join(", ")}]`
    }
    switch (type._tag) {
      case "never": case "unknown": case "string": case "null": case "undefined": return type._tag
      case "unit": return "void"
      case "nat": case "int": case "number": return "number"
      case "bool": return "boolean"
      case "bytes": return "Uint8Array"
      case "lit": return quoteType(type.value)
      case "handle": return legacy(type.target)
      case "option": return generic("Option.Option", [type.inner])
      case "list": return generic("ReadonlyArray", [type.inner])
      case "prod": return tuple([type.left, type.right])
      case "except": return generic("Result.Result", [type.value, type.error])
      case "exitOf": return generic("Exit.Exit", [type.value, type.error])
      case "fiberOf": return generic("Fiber.Fiber", [type.value, type.error])
      case "causeOf": return generic("Cause.Cause", [type.error])
      case "refOf": return generic("Ref.Ref", [type.value])
      case "deferredOf": return generic("Deferred.Deferred", [type.value, type.error])
      case "tuple": return tuple(type.items)
      case "map": {
        if (type.key._tag !== "string") return undefined
        const value = render(type.value)
        return value === undefined ? undefined : `Readonly<Record<string, ${value}>>`
      }
      case "record": {
        const fields = type.fields.map(([name, [optional, value]]) => {
          const target = render(value)
          return target === undefined ? undefined : `readonly ${targetIdentifier(name) ? name : quoteType(name)}${optional ? "?" : ""}: ${target}`
        })
        return fields.some(field => field === undefined) ? undefined : fields.length === 0 ? "{}" : `{ ${fields.join("; ")} }`
      }
      case "union": {
        const values = members(type).map(render)
        if (values.some(value => value === undefined)) return undefined
        return [...new Set(values.flatMap(value => unionParts(value!)))].join(" | ")
      }
      case "var": case "app": return undefined
      default: return unrecognized(type)
    }
  }
  return render(normalize(raw))
}


/** The same limited legacy grammar as Codegen.Types.parseLegacy, without source evaluation. */
export const legacyType = (source: string): string | undefined => {
  let position = 0
  const space = () => { while (/[ \t\r\n]/.test(source[position] ?? "\uFFFF")) position++ }
  const take = (token: string): boolean => { space(); if (source[position] !== token) return false; position++; return true }
  const identifier = (): string | undefined => {
    space()
    const found = /^[A-Za-z_$][A-Za-z0-9_$]*/.exec(source.slice(position))
    if (!found) return undefined
    position += found[0].length
    return found[0]
  }
  const hex = (count: number): number | undefined => {
    const digits = source.slice(position, position + count)
    if (digits.length !== count || !/^[0-9A-Fa-f]+$/.test(digits)) return undefined
    position += count
    return Number.parseInt(digits, 16)
  }
  const literal = (): string | undefined => {
    space()
    const quote = source[position++]!
    let value = ""
    while (position < source.length) {
      const character = source[position++]!
      if (character === quote) {
        return new TextDecoder().decode(new TextEncoder().encode(value)) === value ? quoteType(value) : undefined
      }
      if (character === "\r" || character === "\n") return undefined
      if (character !== "\\") { value += character; continue }
      const escaped = source[position++]
      if (escaped === undefined) return undefined
      const simple: Readonly<Record<string, string>> = {"\"": "\"", "'": "'", "\\": "\\", "/": "/", "b": "\b", "f": "\f", "n": "\n", "r": "\r", "t": "\t", "v": "\u000b"}
      if (Object.hasOwn(simple, escaped)) { value += simple[escaped]; continue }
      if (escaped === "\n") continue
      if (escaped === "\r") { if (source[position] === "\n") position++; continue }
      if (escaped === "0") {
        if (/[0-9]/.test(source[position] ?? "")) return undefined
        value += "\0"; continue
      }
      if (escaped !== "x" && escaped !== "u") return undefined
      let scalar: number | undefined
      if (escaped === "u" && source[position] === "{") {
        position++
        const digits = /^[0-9A-Fa-f]+/.exec(source.slice(position))?.[0]
        if (digits === undefined) return undefined
        position += digits.length
        if (source[position++] !== "}") return undefined
        scalar = Number.parseInt(digits, 16)
      } else {
        scalar = hex(escaped === "x" ? 2 : 4)
        if (scalar !== undefined && scalar >= 0xd800 && scalar <= 0xdbff) {
          if (source.slice(position, position + 2) !== "\\u") return undefined
          position += 2
          const low = hex(4)
          if (low === undefined || low < 0xdc00 || low > 0xdfff) return undefined
          scalar = 0x10000 + (scalar - 0xd800) * 0x400 + low - 0xdc00
        }
      }
      if (scalar === undefined || scalar >= 0x110000 || (scalar >= 0xd800 && scalar <= 0xdfff)) return undefined
      value += String.fromCodePoint(scalar)
    }
    return undefined
  }
  const list = (closing: string, empty: boolean): string[] | undefined => {
    space()
    if (take(closing)) return empty ? [] : undefined
    const first = type()
    if (first === undefined) return undefined
    if (take(closing)) return [first]
    if (!take(",")) return undefined
    const rest = list(closing, true)
    return rest === undefined ? undefined : [first, ...rest]
  }
  const primitives = new Set(["any", "unknown", "never", "void", "undefined", "null", "number", "string", "boolean", "object", "symbol", "bigint"])
  const atom = (): string | undefined => {
    space()
    if (source[position] === '"' || source[position] === "'") return literal()
    if (take("(")) { const inner = type(); return inner !== undefined && take(")") ? inner : undefined }
    if (take("[")) { const items = list("]", true); return items && `[${items.join(", ")}]` }
    const first = identifier()
    if (first === undefined) return undefined
    if (first === "readonly") {
      if (!take("[")) return undefined
      const items = list("]", true)
      return items && `readonly [${items.join(", ")}]`
    }
    if (primitives.has(first)) return first
    if (!targetIdentifier(first) || ["keyof", "infer", "unique"].includes(first)) return undefined
    const names = [first]
    while (take(".")) {
      const next = identifier()
      if (next === undefined || !targetIdentifier(next)) return undefined
      names.push(next)
    }
    if (!take("<")) return names.join(".")
    const args = list(">", false)
    return args && `${names.join(".")}<${args.join(", ")}>`
  }
  const type = (): string | undefined => {
    const first = atom()
    if (first === undefined) return undefined
    const members = unionParts(first)
    while (take("|")) {
      const next = atom()
      if (next === undefined) return undefined
      members.push(...unionParts(next))
    }
    return [...new Set(members)].join(" | ")
  }
  const result = type()
  space()
  return position === source.length ? result : undefined
}
