/**
 * Foldkit kind vocabulary — SKETCH, mirrors scratch/CasGrammar.lean.
 *
 * Tags 8/9/10 are the profile's blob kinds; the others are illustrative and
 * would enter the real registry through Pass A. Version byte is scheme 0.
 */
export const KindTag = {
  value: 1,
  chunk: 8,
  tree: 9,
  manifest: 10,
  file: 11,
  entry: 12,
  context: 13,
  folder: 14,
} as const

export type KindName = keyof typeof KindTag

export const sortOf = (tag: number): KindName | undefined =>
  (Object.keys(KindTag) as ReadonlyArray<KindName>).find((k) => KindTag[k] === tag)

const encoder = new TextEncoder()
const decoder = new TextDecoder("utf-8", { fatal: false })

export const utf8 = (text: string): Uint8Array => encoder.encode(text)
export const textOf = (bytes: Uint8Array): string => decoder.decode(bytes)
