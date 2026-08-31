/** The model's declared toy digest for vector fixtures: 32 lanes, each
 * a byte-weighted accumulator — deterministic, collision-visible, and
 * cheap enough to recompute in every row. */
export const toyAddr = (
  bytes: ReadonlyArray<number>,
): ReadonlyArray<number> => Array.from({ length: 32 }, (_, lane) => {
  let accumulator = lane + bytes.length
  for (const byte of bytes) accumulator += byte * (lane + 3)
  return accumulator % 256
})
