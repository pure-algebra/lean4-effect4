import { tuple } from "./prelude-atoms.gen.ts"
import { tupleAt } from "./tuples.ts"

// A number or a Boolean in an immediate slot of `tuple` widens, and a string literal keeps its
// literal type (decisions row 256; `literals.typecheck.ts` holds the rule's controls). Until
// that repair six pins below read `7` and `true`: `singleton`, `pair`, `larger`, `first`,
// `third` and `nested`.
const empty: readonly [] = tuple()
const singleton: readonly [number] = tuple(7)
const pair: readonly [number, "x"] = tuple(7, "x")
const larger: readonly [number, "x", boolean] = tuple(7, "x", true)
const first: number = tupleAt<"0">("0")(pair)
const second: "x" = tupleAt<"1">("1")(pair)
const third: boolean = tupleAt<"2">("2")(larger)
const nested: number = tupleAt<"0">("0")(tupleAt<"0">("0")(tuple(pair)))
// The earlier pins of `first` and `third`, as refusals on the constructor's own answer: a wider
// pin alone would also hold of a helper that kept the literal's type.
// @ts-expect-error The projection of a number slot is `number`, not the literal `7`.
const literalFirst: 7 = tupleAt<"0">("0")(tuple(7, "x"))
// @ts-expect-error The projection of a Boolean slot is `boolean`, not the literal `true`.
const literalThird: true = tupleAt<"2">("2")(tuple(7, "x", true))
const unionRead = (value: readonly [7, "x"] | readonly [true, 9]): 7 | true => tupleAt<"0">("0")(value)
const impossible = (value: never): never => tupleAt<"123456789012345678901234567890">("123456789012345678901234567890")(value)
const nestedImpossible = (value: never): never => tupleAt<"0">("0")(tupleAt<"1">("1")(value))

// @ts-expect-error An empty tuple has no first position.
tupleAt<"0">("0")(empty)
// @ts-expect-error A singleton has no second position.
tupleAt<"1">("1")(singleton)
// @ts-expect-error A missing pair position refuses.
tupleAt<"2">("2")(pair)
// @ts-expect-error An ordinary array has no statically present tuple key.
tupleAt<"0">("0")([] as readonly number[])
// @ts-expect-error A record with a numeric property is not a tuple.
tupleAt<"0">("0")({ "0": 7 })
// @ts-expect-error The two literal markers must agree.
tupleAt<"0">("1")(pair)
// @ts-expect-error Every union alternative must contain the requested position.
const unionMissing = (value: readonly [7] | readonly []): 7 => tupleAt<"0">("0")(value)
void [first, second, third, nested, literalFirst, literalThird, unionRead, impossible, nestedImpossible, unionMissing]
