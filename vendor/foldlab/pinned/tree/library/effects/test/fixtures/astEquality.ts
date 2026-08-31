/**
 * Structural AST equality, quotienting function identity.
 *
 * Effect builds a fresh closure every time a filter is constructed
 * (`Schema.isInt()` allocates its own `run`, `toCode`, and
 * `toJsonSchema`), so two ASTs that agree in every datum still differ by
 * reference and no `deepStrictEqual` can be used on them. Functions are
 * required here to be functions of the same name at the same path;
 * every other value, the check identities included, must match exactly.
 *
 * This is the closure quotient the schema-materialization suite
 * established; it lives here because the P6 differential compares two
 * independently generated schemas with it, and one definition of "the
 * same schema" is the point of the differential.
 */

/** Every path at which two values differ, function identity aside.
 * An empty answer is "these are the same schema". */
export const astDifferences = (
  left: unknown,
  right: unknown,
  path: string,
): ReadonlyArray<string> => {
  const found: Array<string> = []
  const walk = (a: unknown, b: unknown, at: string): void => {
    if (Object.is(a, b)) return
    if (typeof a === "function" && typeof b === "function") {
      if (a.name !== b.name) {
        found.push(`${at}: function ${a.name} vs function ${b.name}`)
      }
      return
    }
    if (
      typeof a !== "object" || typeof b !== "object" || a === null || b === null
    ) {
      found.push(`${at}: ${String(a)} vs ${String(b)}`)
      return
    }
    if (Object.getPrototypeOf(a) !== Object.getPrototypeOf(b)) {
      found.push(`${at}: differing prototypes`)
      return
    }
    for (const key of new Set([...Reflect.ownKeys(a), ...Reflect.ownKeys(b)])) {
      walk(Reflect.get(a, key), Reflect.get(b, key), `${at}.${String(key)}`)
    }
  }
  walk(left, right, path)
  return found
}
