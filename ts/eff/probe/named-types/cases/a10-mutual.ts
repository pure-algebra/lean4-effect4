// expect: none
// Mutual recursion through record fields.
export type Even = { readonly _tag: "Zero" } | { readonly _tag: "SuccE"; readonly pred: Odd }
export type Odd = { readonly _tag: "SuccO"; readonly pred: Even }
export const two: Even = { _tag: "SuccE", pred: { _tag: "SuccO", pred: { _tag: "Zero" } } }
