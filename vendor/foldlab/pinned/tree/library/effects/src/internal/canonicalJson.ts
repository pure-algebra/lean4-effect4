/**
 * The canonical JSON printer (CAS-004), on its own with no imports —
 * MOVED here verbatim from `src/cas/Value.ts`, which re-exports it, so
 * the one spelling stays one spelling. The move exists because the
 * printer is pure leaf machinery that seams below the store law (the
 * word log) also speak, and importing it through `Value.ts` — which
 * imports the store — made the dependency a cycle.
 */

/** Codepoint order — equal to UTF-8 byte order, the language-neutral
 * key ordering CAS-004 pins. Default string comparison is UTF-16
 * code-unit order, which disagrees on astral-plane keys. */
const compareCodepoints = (left: string, right: string): number => {
  const a = Array.from(left)
  const b = Array.from(right)
  const shorter = Math.min(a.length, b.length)
  for (let index = 0; index < shorter; index += 1) {
    const delta = a[index]!.codePointAt(0)! - b[index]!.codePointAt(0)!
    if (delta !== 0) return delta
  }
  return a.length - b.length
}

/** The canonical value encoding (CAS-004): compact JSON with
 * codepoint-sorted keys, integer-only numbers, and the exact
 * `JSON.stringify` escape set. The UTF-8 bytes of this string are what
 * a value node's content identity is computed over; integers-only is
 * the ruling that keeps those bytes language-neutral. Exported for the
 * conformance binding — the model's vectors are the authority. */
export const canonicalJson = (
  value: unknown,
  ancestors: ReadonlySet<object> = new Set(),
): string => {
  if (value === null) return "null"
  switch (typeof value) {
    case "boolean":
      return value ? "true" : "false"
    case "string":
      return JSON.stringify(value)
    case "number":
      if (!Number.isSafeInteger(value)) {
        throw new TypeError(
          "Canonical JSON numbers must be safe integers — fractional and unsafe values have no language-neutral encoding",
        )
      }
      return JSON.stringify(value)
    case "object": {
      if (ancestors.has(value)) throw new TypeError("Canonical JSON cannot encode cycles")
      const nextAncestors = new Set([...ancestors, value])
      if (Array.isArray(value)) {
        if (
          Object.getOwnPropertySymbols(value).length > 0
          || Object.keys(value).length !== value.length
        ) {
          throw new TypeError("Canonical JSON arrays must be dense and unadorned")
        }
        const items: Array<string> = []
        for (let index = 0; index < value.length; index += 1) {
          items.push(canonicalJson(value[index], nextAncestors))
        }
        return `[${items.join(",")}]`
      }
      const prototype = Object.getPrototypeOf(value)
      if (prototype !== Object.prototype && prototype !== null) {
        throw new TypeError("Canonical JSON objects must have a plain prototype")
      }
      if (Object.getOwnPropertySymbols(value).length > 0) {
        throw new TypeError("Canonical JSON objects cannot have symbol keys")
      }
      const fields = Object.entries(value)
        .toSorted(([left], [right]) => compareCodepoints(left, right))
        .map(([key, item]) => `${JSON.stringify(key)}:${canonicalJson(item, nextAncestors)}`)
      return `{${fields.join(",")}}`
    }
    default:
      throw new TypeError(`Canonical JSON cannot encode ${typeof value}`)
  }
}
