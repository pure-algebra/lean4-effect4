import { Effect, Option, Ref } from "effect"
import { add, pair } from "./prelude.ts"

declare const cell: Ref.Ref<number>
declare const captured: number
const callback: Effect.Effect<number> = Ref.modify(cell, current => pair(41, add(current, captured)))
const optional: Effect.Effect<number> = Ref.modifySome(cell, current => pair(41, Option.some(current)))

Ref.modify(cell, current => pair(current.toUpperCase(), current))

Ref.update(cell, current => add(current, "wrong capture"))

Ref.modify(cell, current => pair(41, "wrong next cell"))

Ref.modifySome(cell, current => pair(41, current))
void callback
void optional
