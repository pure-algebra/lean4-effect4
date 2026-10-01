// Seat R, question 2: a spelling tsgo may accept although the run differs (field-names.cjs:
// the plain `__proto__` key sets the prototype and creates no own property).
export {}
type T3 = { readonly __proto__: string }
export const trap: T3 = { __proto__: "x" }
