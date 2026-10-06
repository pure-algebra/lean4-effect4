type Wide<T> = T extends number ? number : T extends boolean ? boolean : T
export const pair = <const A, const B>(a: A, b: B): readonly [Wide<A>, Wide<B>] => [a, b] as readonly [Wide<A>, Wide<B>]
export const tuple = <const A extends readonly unknown[]>(...items: A): { readonly [I in keyof A]: Wide<A[I]> } => items as { readonly [I in keyof A]: Wide<A[I]> }
