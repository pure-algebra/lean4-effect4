/** RED CONTROL (must fail): a field of the wrong type at the Schema.Class, and a different tag. */
import { Data, Schema } from "effect"
class Person extends Schema.Class<Person>("Person")({ name: Schema.String }) {}
export const r1: Person = { name: 1 }
class A1 extends Data.TaggedError("Same")<{ readonly n: number }> {}
class B1 extends Data.TaggedError("Other")<{ readonly n: number }> {}
export const r2: A1 = new B1({ n: 1 })
