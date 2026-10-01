// Seat T RED CONTROL for class-names.ts: two tagged error classes with the same tag and different
// fields are not mutually assignable; asserting they are must fail (TS2322 at the one line).
import { Data } from "effect"
type Mutual<A, B> = [A] extends [B] ? ([B] extends [A] ? true : false) : false
class NotFound extends Data.TaggedError("NotFound")<{ readonly id: number }> {}
class Wider extends Data.TaggedError("NotFound")<{ readonly id: number; readonly url: string }> {}
export const n4: Mutual<NotFound, Wider> = true
