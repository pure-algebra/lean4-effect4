import { Effect, Option, Ref } from "effect"
import { add, pair } from "./prelude.ts"

declare const cell: Ref.Ref<number>
declare const captured: number
const callback: Effect.Effect<number> = Ref.modify(cell, current => pair(41, add(current, captured)))
const optional: Effect.Effect<number> = Ref.modifySome(cell, current => pair(41, Option.some(current)))
// @ts-expect-error The inferred current value is a number, with no string methods.
Ref.modify(cell, current => pair(current.toUpperCase(), current))
// @ts-expect-error A string capture does not satisfy a numeric callback input.
Ref.update(cell, current => add(current, "wrong capture"))
// @ts-expect-error The next cell value must remain a number.
Ref.modify(cell, current => pair(41, "wrong next cell"))
// @ts-expect-error modifySome requires an optional next cell value.
Ref.modifySome(cell, current => pair(41, current))
void callback
void optional
