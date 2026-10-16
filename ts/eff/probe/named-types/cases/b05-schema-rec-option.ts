// expect: none
// A recursive Schema through Option, with the alias in its deferring spelling.
import { Option, Schema } from "effect"
export type Peano = Option.None<Peano> | Option.Some<Peano>
export const Peano = Schema.Option(Schema.suspend((): Schema.Codec<Peano> => Peano))
export const two: Peano = Schema.decodeUnknownSync(Peano)(Option.some(Option.some(Option.none())))
