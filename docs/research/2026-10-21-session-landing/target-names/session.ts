/**

 */
import { Context, Effect, Layer } from "effect"
import { caseTag, optionCase } from "./prelude/prelude.ts"

export const sessionMake = (a0: void): Effect.Effect<number, never, never> => Effect.suspend(() => Effect.succeed(5))

export const sessionRead = (a0: number): Effect.Effect<number, never, never> => Effect.suspend(() => Effect.succeed(a0))

export const Session = Context.Service<"Session", { readonly read: () => Effect.Effect<number, never, never> }>("Session")

export const SessionLayer = Layer.effect(Session, Effect.map(sessionMake(), (a0) => {
  return { read: () => sessionRead(a0) }
}))

export const main: Effect.Effect<void, never, never> = Effect.flatMap(sessionMake(), (a0) => Effect.suspend(() => {
  let a1 = true
  return Effect.map(Effect.whileLoop({
    while: () => a1,
    body: () => Effect.flatMap(Session.next(), (a2) => optionCase(a2, () => Effect.succeed(false), (a3) => caseTag(a3, "read", (a4) => Effect.flatMap(Effect.exit(sessionRead(a0)), (a5) => Effect.flatMap(Session.reply_read(a5), (a6) => Effect.succeed(true))), (a4) => Effect.succeed(false)))),
    step: (a2) => {
      a1 = a2
    },
  }), () => undefined)
}))
