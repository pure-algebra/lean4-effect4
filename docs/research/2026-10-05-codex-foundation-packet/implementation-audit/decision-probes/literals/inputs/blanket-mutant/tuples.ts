/** Static tuple projection. Literal string keys avoid number rounding in generated syntax.
 * Ordinary arrays lack the required tuple position; impossible receivers retain never. */
export const tupleAt = <I extends string>(index: I) =>
  <const T extends readonly unknown[] & { readonly [K in I]: unknown }>(target: T): T[I] => target[index]
