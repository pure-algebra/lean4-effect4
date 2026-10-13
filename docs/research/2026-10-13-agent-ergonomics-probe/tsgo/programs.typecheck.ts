import { Effect, Fiber } from "effect"
import { add, length } from "../../../../harness/truth/prelude.ts"
import { Db, Todos } from "./approws.ts"
export const a: Effect.Effect<number, never, never> = Effect.flatMap(Todos.add("milk"), (a0) => Effect.succeed(length(a0)))
export const b: Effect.Effect<string, never, never> = Effect.scoped(Effect.flatMap(Effect.acquireRelease(Db.open("db"), (a0, a1) => Db.close(a0)), (a0) => Db.query(a0)))
export const c: Effect.Effect<number, never, never> = Effect.flatMap(Effect.forkChild(Effect.succeed(1), { startImmediately: false, uninterruptible: "inherit" }), (a0) => Effect.flatMap(Effect.forkChild(Effect.succeed(2), { startImmediately: false, uninterruptible: "inherit" }), (a1) => Effect.flatMap(Fiber.join(a0), (a2) => Effect.flatMap(Fiber.join(a1), (a3) => Effect.succeed(add(a2, a3))))))
// the reader refuses these two; does tsgo?
export const c2 = Effect.flatMap(Effect.forkChild(Effect.succeed(1)), (a0) => Fiber.join(a0))
export const b1 = Effect.scoped(Effect.flatMap(Effect.acquireRelease(Db.open("db"), (conn) => Db.close(conn)), (conn) => Db.query(conn)))
// a type error tsgo should catch
export const bad = Effect.flatMap(Todos.add("milk"), (a0) => Effect.succeed(add(a0, 1)))
