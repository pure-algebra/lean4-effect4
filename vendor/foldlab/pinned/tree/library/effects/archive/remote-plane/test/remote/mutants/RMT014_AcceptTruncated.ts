import {
  decodeCapabilityResult,
  type CapabilityDecodeResult,
} from "../../../src/internal/remoteControl.ts"

export const represents = "Killing this mutant demonstrates the vectors notice a decoder that accepts truncated capability documents by padding them — control state parsed open instead of fail-closed."

export const mutantDecodeCapabilityResult = (
  input: ReadonlyArray<number>,
): CapabilityDecodeResult => {
  if (input.length >= 8) return decodeCapabilityResult(input)
  const padded = new Uint8Array(8)
  padded.set(input)
  return decodeCapabilityResult(padded)
}
