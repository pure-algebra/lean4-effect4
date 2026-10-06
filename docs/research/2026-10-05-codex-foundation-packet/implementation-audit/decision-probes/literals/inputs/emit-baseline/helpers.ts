export const pair = <const A, const B>(a: A, b: B): readonly [A, B] => [a, b]
export const tuple = <const A extends readonly unknown[]>(...items: A): A => items
