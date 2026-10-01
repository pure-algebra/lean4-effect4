// Seat T fixture for the recursion, Record<K, V> and tuple-arity splits; counts in recursion-records.expected.tsv.
type Json = string | number | boolean | null | ReadonlyArray<Json> | { readonly [k: string]: Json }
interface Tree { readonly value: number; readonly children: ReadonlyArray<Tree> }
type DeepPartial<T> = { [K in keyof T]?: DeepPartial<T[K]> }
interface Builder { add(n: number): Builder; readonly done: () => Builder }
type Plain = { readonly a: number }
type Bag = Record<string, unknown>
type Scores = Record<string, number>
type Fixed = Record<"a" | "b", number>
type Keyed = Record<number, string>
type P2 = readonly [number, string]
type P3 = [number, string, boolean]
type P0 = []
