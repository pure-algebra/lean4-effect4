// expect: none
// Declared variances printed as TypeScript variance annotations; tsgo checks them against the body.
export type Box<out A> = { readonly value: A }
export type Sink<in A> = { readonly put: (a: A) => void }
export type Cell<in out A> = { value: A }
