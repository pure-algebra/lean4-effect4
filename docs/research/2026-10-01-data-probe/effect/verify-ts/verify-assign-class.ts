/**
 * Verifier of seat EFFECT (2026-10-01): is TypeScript's refusal of an object literal at a class
 * type nominal, or structural? The seat read TS2740 at two Error-derived classes as evidence for a
 * nominal marker (EFF-11, S-a3). This file is GREEN if every line compiles under the pinned tsgo
 * with the pass's flags; lines marked `@ts-expect-error` must be errors (else TS2578).
 */
import { Data, Schema } from "effect"

// Q1. A Schema.Class (not an error): is an object literal with exactly its fields accepted?
class Person extends Schema.Class<Person>("Person")({ name: Schema.String }) {}
export const q1: Person = { name: "a" }

// Q2. Data.Class: the same question. Refused, and the reason tsgo gives is structural: the
// literal lacks `pipe` (Pipeable), a member, not a brand. (Run 1 expected acceptance: wrong.)
class P2 extends Data.Class<{ readonly name: string }> {}
// @ts-expect-error
export const q2: P2 = { name: "a" }

// Q3. Two distinct Data.TaggedError classes with the same tag and the same fields.
class A1 extends Data.TaggedError("Same")<{ readonly n: number }> {}
class A2 extends Data.TaggedError("Same")<{ readonly n: number }> {}
export const q3a: A1 = new A2({ n: 1 })
export const q3b: A2 = new A1({ n: 1 })

// Q4. Two distinct Schema.TaggedError classes with the same tag and the same fields.
class S1 extends Schema.TaggedError<S1>()("Same", { n: Schema.Number }) {}
class S2 extends Schema.TaggedError<S2>()("Same", { n: Schema.Number }) {}
export const q4a: S1 = new S2({ n: 1 })
export const q4b: S2 = new S1({ n: 1 })

// Q5. A Data.TaggedError instance is accepted where a plain Error-shaped record with the same tag
// and fields is expected: the class type is that record plus Error's members (width).
declare const s1: S1
export const q5: { readonly _tag: "Same"; readonly n: number; readonly message: string } = s1

// Q6. The refusal is about missing members: an object literal at an Error-derived class type is
// refused (TS2740), as the seat found.
// @ts-expect-error
export const q6: A1 = { _tag: "Same", n: 1 }
