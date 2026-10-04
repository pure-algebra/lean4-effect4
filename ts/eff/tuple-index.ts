/** The host reifier stores a Nat as a JavaScript number. Refuse rounding explicitly.
 * Lean structural tuple syntax has no such bound: it retains the canonical decimal string. */
export const readTupleIndex = (text: string): number | undefined => {
  if (!/^(0|[1-9][0-9]*)$/.test(text)) return undefined
  const index = Number(text)
  return Number.isSafeInteger(index) && index >= 0 && String(index) === text ? index : undefined
}
