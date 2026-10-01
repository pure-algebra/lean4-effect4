// Seat S, question 2: what tsgo infers for the QUOTED "__proto__" key, which rc.112 drops at run
// time (q2-edges E8b: the property list is empty). If the inferred type keeps the field, the
// static type and the run-time schema disagree for that spelling.
import * as Schema from "effect/Schema"
type Equal<A, B> = (<T>() => T extends A ? 1 : 2) extends (<T>() => T extends B ? 1 : 2) ? true : false
type Assert<T extends true> = T
export const QP = Schema.Struct({ "__proto__": Schema.Number })
export type KeepsField = Assert<Equal<typeof QP.Type, { readonly "__proto__": number }>>
