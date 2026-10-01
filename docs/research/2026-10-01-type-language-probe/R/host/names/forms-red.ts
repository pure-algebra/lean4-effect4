// Seat R, question 2: red twins. Each line must be refused by tsgo.
export {}
type T1 = { readonly a: number; readonly b: string }
const r1: T1 = { b: "x", a: 1 }
export const e1: string = r1.c                         // unknown name (TS2339)
export const e2: number = r1.b                         // wrong field type (TS2322)
const r1b: T1 = { a: 1 }                               // missing field (TS2741)
const r1c: T1 = { a: 1, b: "x", c: 2 }                 // excess property in a literal (TS2353)
type T3 = { readonly __proto__: string }
const r3f: T3 = Object.fromEntries([["__proto__", "x"]])  // fromEntries loses the type
export const r1bUsed = r1b; export const r1cUsed = r1c; export const r3fUsed = r3f
