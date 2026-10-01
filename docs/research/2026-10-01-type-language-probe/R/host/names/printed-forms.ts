// Seat R, question 2: the exact strings `Q2Faces.lean` renders (its §8 #guards), placed at the
// record types they print at, under tsgo; then run under node (as .mjs after type stripping is
// not needed: plain JavaScript below the type annotations). Must type-check and must run.
type T1 = { readonly a: number; readonly b: string }
type T2 = { readonly "a-b": number; readonly default: boolean }
type T3 = { readonly __proto__: string; readonly a: number }
type T4 = { readonly "名前": string }
const r1: T1 = { b: "x", a: 1 }
const r2: T2 = { "a-b": 1, "default": true }
const r3: T3 = { ["__proto__"]: "x", ["a"]: 1 }
const r4: T4 = { "名前": "n" }
const a0 = r2
export const g1: number = a0["a-b"]
export const g2: boolean = a0.default
const a1 = r3
export const g3: string = a1["__proto__"]
const a2 = r4
export const g4: string = a2["名前"]
export const g5: string = r1.b
export const own: boolean = Object.hasOwn(r3, "__proto__")
console.log(JSON.stringify({ g1, g2, g3, g4, g5, own, r3: JSON.stringify(r3) }))
