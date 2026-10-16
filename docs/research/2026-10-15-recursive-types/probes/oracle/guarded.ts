// Guardedness on the TypeScript face (seat RECTYPES): tsgo 7 refuses each unguarded alias,
// the probe's three red tables (TyDecls.guarded refuses the same three). Run with the pinned tsgo:
//   harness/truth/node_modules/.bin/tsgo --noEmit --strict --target es2022 --moduleResolution bundler --module esnext guarded.ts
export type A = A
export type B = B | string
export type C = D | number
export type D = C | string
// guarded: the recursive occurrence is under a value constructor; S is guarded and empty
export type L = { readonly head: number; readonly tail: L | null }
export type S = { readonly head: number; readonly next: S }
export const l: L = { head: 1, tail: { head: 2, tail: null } }
