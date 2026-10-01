// Seat T fixture for form_census.ts: every count in forms.expected.tsv is hand-counted from this file.
import { Brand, Data, Effect, Option, Schema } from "effect"

interface Account {
  readonly id: string
  readonly balance: number
  note?: string
  onChange: (n: number) => void
  close(): void
}

type Entry =
  | { readonly _tag: "Deposit"; readonly amount: number }
  | { readonly _tag: "Withdraw"; readonly amount: number }

type Point = { x: number; y?: number }

type Role = "admin" | "member"

type MaybeName = string | undefined | null

type Tree = { readonly value: number; readonly children: ReadonlyArray<Tree> }

interface Node { readonly next: Node | undefined }

type UserId = string & Brand.Brand<"UserId">

type Pair = readonly [string, number]
type Rest = [string, ...number[]]
type Opt = [a: string, b?: number]

type Names = readonly string[]
type Mutable = Array<number>

type Big = bigint
type Sym = unique symbol
type Key = `user-${string}`
type Lookup = { [key: string]: number }
type Dict = Record<string, number>
type Odd = 1 | -1 | 10n | true

const generic = <A>(a: A): A => a
function decodeWith<S extends Schema.Top>(schema: S): S { return schema }
function run(schema: Schema.Schema<number>): void {}

class NotFound extends Data.TaggedError("NotFound")<{ readonly id: number }> {}
class Plain extends Error {}
class Other {}

enum Color { Red, Green }

const User = Schema.Struct({ id: Schema.Number })
type User = typeof User.Type

type K = keyof Account
type V = Account["id"]
type M = { readonly [P in keyof Account]: Account[P] }
type C<T> = T extends string ? 1 : 0

const program = Effect.gen(function* () {
  const d = new Date()
  const now = Date.now()
  const s = Symbol.for("k")
  const m = new Map<string, number>()
  const set = new Set([1])
  const j = JSON.parse("{}")
  const t = JSON.stringify({ a: 1 })
  const r = Math.max(1.5, -2, 10n > 0n ? 1 : 0)
  const o = { ...{ a: 1 }, ["k"]: 2, b: null, c: undefined }
  const msg = `id ${r}`
  const opt = Option.some(1)
  yield* Effect.sleep("10 millis")
  return [d, now, s, m, set, j, t, o, msg, opt]
})

const failed = Effect.fail(new NotFound({ id: 1 }))
