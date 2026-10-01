// Seat R, question 2: the printed images of record construction and projection the printer
// chooses, per class of field name. Must type-check (tsgo exit 0).
export {}
// identifier names: an unquoted literal in written order (here permuted), dot access
type T1 = { readonly a: number; readonly b: string }
const r1: T1 = { b: "x", a: 1 }
export const p1: string = r1.b
// non-identifier names: every key quoted (the renderer's objectQuoted), bracket access
type T2 = { readonly "a-b": number; readonly "a\"b": string; readonly default: boolean; readonly "": number; readonly "1": number }
const r2: T2 = { "a-b": 1, "a\"b": "s", "default": true, "": 0, "1": 5 }
export const p2a: number = r2["a-b"]
export const p2b: string = r2["a\"b"]
export const p2c: boolean = r2["default"]
export const p2d: number = r2[""]
export const p2e: number = r2["1"]
// __proto__: a computed key (an own property at run time, field-names.cjs), bracket access
type T3 = { readonly __proto__: string; readonly a: number }
const r3: T3 = { ["__proto__"]: "x", a: 1 }
export const p3: string = r3["__proto__"]
// Unicode names: outside the ASCII identifier profile (`targetIdentifier`), so quoted
type T4 = { readonly "naïve": number; readonly "名前": string }
const r4: T4 = { "naïve": 1, "名前": "n" }
export const p4: string = r4["名前"]
// nested records and a record in an option-like union
type T5 = { readonly user: { readonly id: number; readonly name: string }; readonly status: number }
const r5: T5 = { status: 200, user: { name: "bob", id: 2 } }
export const p5: string = r5.user.name
