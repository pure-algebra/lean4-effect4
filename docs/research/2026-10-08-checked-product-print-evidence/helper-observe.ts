import { Effect, Ref } from "effect"
import { pair, tuple } from "./prelude-atoms.gen.ts"
const numeric = Effect.runSync(Ref.make(7))
const textual = Effect.runSync(Ref.make("seven"))
const numericArray = [numeric]
const textualArray = [textual]
const payload: typeof numericArray | typeof textualArray = numericArray
const marker: number | string = "retained"
const checkedTuple = tuple<typeof payload, typeof marker>(payload, marker)
const checkedPair = pair<readonly [typeof payload, typeof marker]>(payload, marker)
const ordinaryTuple = tuple(payload, marker)
const ordinaryPair = pair(payload, marker)
if (![checkedTuple, checkedPair, ordinaryTuple, ordinaryPair].every(value => value[0] === payload && value[1] === marker)) {
  throw new Error("Tuple or pair changed the selected payload reference")
}
if (checkedTuple[0][0] !== numeric || checkedPair[0][0] !== numeric) throw new Error("Nested Ref identity changed")
console.log(JSON.stringify({ values: [Effect.runSync(Ref.get(numeric)), Effect.runSync(Ref.get(textual))],
  checkedAndOrdinarySlotsRetained: true, nestedRefIdentityRetained: true }))
