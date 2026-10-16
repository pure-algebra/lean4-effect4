// expect: TS2456
// Recursion through Exit.Exit (`Exit.ts:59`), an alias: refused (E1). Through Cause.Cause, Ref.Ref,
// Fiber.Fiber and Deferred.Deferred, interfaces: accepted.
import type { Cause, Deferred, Exit, Fiber, Ref } from "effect"
export type E1 = Exit.Exit<E1, string>
export type C1 = Cause.Cause<C1>
export type R1 = { readonly next: Ref.Ref<R1> }
export type F1 = Fiber.Fiber<F1, never>
export type D1 = Deferred.Deferred<D1, never>
