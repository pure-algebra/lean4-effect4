import { Effect, Option, Ref } from "effect"
import { pair, tuple } from "./prelude-atoms.gen.ts"
declare const cell: Ref.Ref<number>
declare const answer: Option.Option<number>
const tupleCallback: Effect.Effect<Option.Option<number>> = Ref.modify(cell, state => tuple(answer, state))
const pairCallback: Effect.Effect<Option.Option<number>> = Ref.modify(cell, state => pair(answer, state))
type Chunk = readonly ["Chunk", ReadonlyArray<number>]
type End = readonly ["End", void]
type Pull = Chunk | End
type Product = readonly [Chunk, Chunk] | readonly [Chunk, End] | readonly [End, Chunk] | readonly [End, End]
declare const a: Pull
declare const b: Pull
const joinedTuple: Product = tuple<Pull, Pull>(a, b)
const joinedPair: Product = pair<readonly [Pull, Pull]>(a, b)
// @ts-expect-error ordinary tuple inference retains the original factored result
const ordinaryTuple: Product = tuple(a, b)
// @ts-expect-error ordinary pair inference retains the original factored result
const ordinaryPair: Product = pair(a, b)
// @ts-expect-error wrong checked tuple payload
const tuplePayload: Product = tuple<Pull, Pull>(a, 1)
// @ts-expect-error wrong checked pair payload
const pairPayload: Product = pair<readonly [Pull, Pull]>(a, 1)
// @ts-expect-error checked tuple overload requires exactly two slots
const extraSlot: Product = tuple<Pull, Pull>(a, b, 1)
const literals: readonly [number, "tag", boolean] = tuple(1, "tag", true)
const literalPair: readonly ["tag", number] = pair("tag", 1)
declare const impossible: never
const retainedNever: readonly [never, Pull] = tuple<never, Pull>(impossible, a)

declare const flag: boolean
const booleanJoin: readonly [boolean, Chunk] | readonly [boolean, End] = tuple<boolean, Pull>(flag, a)
const booleanPairJoin: readonly [boolean, Chunk] | readonly [boolean, End] = pair<readonly [boolean, Pull]>(flag, a)
// @ts-expect-error checked Boolean literal slots still widen to boolean
const booleanLiteral: readonly [true, Chunk] | readonly [true, End] = tuple<true, Pull>(true, a)
const rightNever: readonly [Pull, never] = tuple<Pull, never>(a, impossible)
const pairNever: readonly [never, Pull] = pair<readonly [never, Pull]>(impossible, a)
declare const handles: ReadonlyArray<Ref.Ref<number>> | ReadonlyArray<Ref.Ref<string>>
const handleJoin: readonly [ReadonlyArray<Ref.Ref<number>>, Chunk] | readonly [ReadonlyArray<Ref.Ref<number>>, End] |
  readonly [ReadonlyArray<Ref.Ref<string>>, Chunk] | readonly [ReadonlyArray<Ref.Ref<string>>, End] =
  tuple<typeof handles, Pull>(handles, a)
const oldPairArgs: readonly [Option.Option<number>, number] = pair<Option.Option<number>, number>(answer, 1)
const oldTupleArgs: readonly [Option.Option<number>, number] = tuple<readonly [Option.Option<number>, number]>(answer, 1)
const oldCallbackArgs: Effect.Effect<Option.Option<number>> = Ref.modify(cell, state => tuple<readonly [Option.Option<number>, number]>(answer, state))

// Exact full typed-printer expression; row arguments constrain callback union inference.
declare const a0: number | string
declare const a1: Ref.Ref<number>
const checkedUnionReply: Effect.Effect<number | string> = Ref.modify<number, number | string>(a1, (a2) => tuple<number | string, number>(a0, a2))
// @ts-expect-error an isolated checked term without its checked row metadata loses callback inference
const bareUnionReply: Effect.Effect<number | string> = Ref.modify(a1, (a2) => tuple<number | string, number>(a0, a2))
// @ts-expect-error the complete checked row refuses an incorrect cell type
const wrongConsumer: Effect.Effect<number | string> = Ref.modify<string, number | string>(a1, (a2) => tuple<number | string, string>(a0, a2))
