// Seat R, question 3: the term forms of the wave's other formers (probe T's set), printed as the
// faces would print them, under tsgo. Must type-check.
import { Data, Effect, Option, Queue } from "effect"

// tuple (n-ary): construction is an array literal, projection an element access at a literal index
type T3 = readonly [number, string, boolean]
const t: T3 = [1, "a", true]
export const t2: boolean = t[2]

// map at string keys: construction from entries (an index-signature type), lookup through a prelude
// atom that answers an Option and reads own properties only
type M = Readonly<Record<string, number>>
const m: M = Object.fromEntries([["a", 1], ["__proto__", 2]])
export const mapGet = <V>(map: Readonly<Record<string, V>>, key: string): Option.Option<V> =>
  Object.hasOwn(map, key) ? Option.some(map[key] as V) : Option.none()
export const got: Option.Option<number> = mapGet(m, "a")
export const mapSet = <V>(map: Readonly<Record<string, V>>, key: string, value: V): Readonly<Record<string, V>> =>
  Object.fromEntries([...Object.entries(map), [key, value]])

// a nominal reference: `Name<Args>` with a record argument
export type Jobs = Queue.Dequeue<{ readonly id: number; readonly payload: string }>

// a tagged error payload: one class per tagged payload type, constructed with `new`
export class NotFound extends Data.TaggedError("NotFound")<{ readonly id: number }> {}
export const fails: Effect.Effect<never, NotFound> = Effect.fail(new NotFound({ id: 2 }))
export const caught: Effect.Effect<string> =
  Effect.catchTag(fails, "NotFound", (e) => Effect.succeed(`no user ${e.id}`))

// a record update by spread keeps the record type when the field type is kept
type W = { readonly used: number; readonly admitted: number }
const w: W = { used: 1, admitted: 0 }
export const w2: W = { ...w, used: w.used + 1 }
