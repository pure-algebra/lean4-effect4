// Seat R, question 3: the spellings that break B-print. Each `mutual(true)` below must be refused.
import { Schema } from "effect"
declare const mutual: <A, B>(a: [A] extends [B] ? ([B] extends [A] ? true : false) : false) => void
const OP = Schema.Struct({ a: Schema.optional(Schema.Number) })
mutual<{ readonly a?: number }, typeof OP.Type>(true)              // optional printed without | undefined
const RecordSchema = Schema.Record(Schema.String, Schema.Number)
mutual<ReadonlyMap<string, number>, typeof RecordSchema.Type>(true) // a Map for an object record
const User = Schema.Struct({ id: Schema.Number, name: Schema.String })
mutual<{ readonly id: number }, typeof User.Type>(true)            // width: not mutual
mutual<readonly [number, string], typeof User.Type>(true)          // today's pair spelling
