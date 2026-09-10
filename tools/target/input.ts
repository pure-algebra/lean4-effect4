/** Local declarative query input. Parsing is strict; compilation never evaluates imported values. */
import type { Axis, Query } from "./oracle.ts"
const axes: Axis[] = ["A", "E", "R", "request", "receiver"]
const isAxis = (x: unknown): x is Axis => typeof x === "string" && axes.some(a => a === x)
const object = (x: unknown): Record<string, unknown> => {
  if (!x || typeof x !== "object" || Array.isArray(x)) throw new Error("query: expected object")
  return x as Record<string, unknown>
}
const string = (x: unknown): string => {
  if (typeof x !== "string" || !x.trim()) throw new Error("query: expected nonempty string")
  return x
}
export function decodeQueries(value: unknown): Query[] {
  if (!Array.isArray(value) || !value.length) throw new Error("query: expected nonempty selection")
  return value.map(raw => {
    const o = object(raw)
    if (Object.keys(o).some(k => !["id", "source", "imports", "subject", "kind", "receiver", "expected", "allowUnknown"].includes(k))) throw new Error("query: unrecognized field")
    if (o.kind !== "effect" && o.kind !== "function") throw new Error("query: unsupported kind")
    if (!Array.isArray(o.imports)) throw new Error("query: imports must be an array")
    const q: Query = { id: string(o.id), source: string(o.source), imports: o.imports.map(string), subject: string(o.subject), kind: o.kind, expected: {} }
    for (const [k, v] of Object.entries(object(o.expected))) {
      if (!isAxis(k)) throw new Error(`query: unknown axis ${k}`)
      q.expected[k] = string(v)
    }
    if (o.receiver !== undefined) q.receiver = string(o.receiver)
    if (o.allowUnknown !== undefined) {
      if (!Array.isArray(o.allowUnknown) || !o.allowUnknown.every(isAxis)) throw new Error("query: unknown allowUnknown axis")
      q.allowUnknown = o.allowUnknown
    }
    return q
  })
}
