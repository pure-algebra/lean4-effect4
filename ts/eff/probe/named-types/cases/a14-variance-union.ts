// expect: TS2637
// A variance annotation on an alias whose body is a union.
export type Opt<out A> = { readonly _tag: "None" } | { readonly _tag: "Some"; readonly value: A }
