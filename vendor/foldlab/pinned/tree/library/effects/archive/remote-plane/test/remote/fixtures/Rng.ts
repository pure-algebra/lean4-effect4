/**
 * Deterministic seeded workload fixtures: the pseudo-random source.
 *
 * A hand-rolled splitmix32 generator over one caller-supplied numeric seed.
 * No `Math.random`, no clock, no ambient state: every draw sequence is a
 * pure function of the seed, so a generated workload regenerates
 * byte-identically from its parameters.
 *
 * Evidence class: G4 sampled evidence only. These fixtures model production
 * sync loads for exploratory and regression tests; they are NEVER a
 * substitute for the ratified conformance vectors under
 * `conformance/manifest`.
 */

/** Draw surface handed to a generator. Created inside one generation call
 * and never escapes it, so generators stay pure functions of their seed. */
export interface WorkloadRng {
  /** Next uniform draw in [0, 2^32). */
  readonly nextUint32: () => number
  /** Uniform integer in the inclusive range. Small modulo bias is accepted
   * for workload sampling; draws stay deterministic per seed. */
  readonly int: (minInclusive: number, maxInclusive: number) => number
  /** Uniform fraction in [0, 1). */
  readonly fraction: () => number
  /** A payload of `length` uniform bytes. */
  readonly bytes: (length: number) => Uint8Array
}

/** Splitmix32: golden-ratio increment with two multiply-xorshift finalizer
 * rounds. Exact 32-bit arithmetic (`Math.imul`, `>>>`) on every host. */
export const makeRng = (seed: number): WorkloadRng => {
  let state = seed >>> 0

  const nextUint32 = (): number => {
    state = (state + 0x9e3779b9) >>> 0
    let mixed = state
    mixed ^= mixed >>> 16
    mixed = Math.imul(mixed, 0x21f0aaad)
    mixed ^= mixed >>> 15
    mixed = Math.imul(mixed, 0x735a2d97)
    mixed ^= mixed >>> 15
    return mixed >>> 0
  }

  const int = (minInclusive: number, maxInclusive: number): number => {
    if (maxInclusive < minInclusive) {
      throw new Error(`empty draw range [${minInclusive}, ${maxInclusive}]`)
    }
    const span = maxInclusive - minInclusive + 1
    return minInclusive + (nextUint32() % span)
  }

  const fraction = (): number => nextUint32() / 0x1_0000_0000

  const bytes = (length: number): Uint8Array => {
    const drawn = new Uint8Array(length)
    for (let index = 0; index < length; index += 1) {
      drawn[index] = nextUint32() & 0xff
    }
    return drawn
  }

  return { nextUint32, int, fraction, bytes }
}

/** Derive an independent stream seed from a parent seed and a label, so one
 * profile seed can feed several generators without draw interference. */
export const deriveSeed = (seed: number, label: string): number => {
  let hash = (seed ^ 0x811c9dc5) >>> 0
  for (let index = 0; index < label.length; index += 1) {
    hash = Math.imul(hash ^ label.charCodeAt(index), 0x01000193) >>> 0
  }
  let mixed = (hash + 0x9e3779b9) >>> 0
  mixed ^= mixed >>> 16
  mixed = Math.imul(mixed, 0x21f0aaad)
  mixed ^= mixed >>> 15
  return mixed >>> 0
}
