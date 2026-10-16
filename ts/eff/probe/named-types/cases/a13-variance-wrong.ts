// expect: TS2636 TS2636
// A variance table that disagrees with the body: tsgo refuses the annotation.
export type Box<in A> = { readonly value: A }
export type Sink<out A> = { readonly put: (a: A) => void }
