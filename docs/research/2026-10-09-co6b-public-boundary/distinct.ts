/**

 */
import { Effect, Context, Layer } from "effect"

export const mkS = (a0: void): Effect.Effect<number, never, never> => Effect.suspend(() => Effect.succeed(1))

export const readS = (a0: number): Effect.Effect<number, never, never> => Effect.suspend(() => Effect.succeed(a0))

export const mkT = (a0: void): Effect.Effect<number, never, never> => Effect.suspend(() => Effect.succeed(2))

export const readT = (a0: number): Effect.Effect<number, never, never> => Effect.suspend(() => Effect.succeed(a0))

export const S = Context.Service<"S", { readonly get: () => Effect.Effect<number, never, never> }>("S")

export const SLayer = Layer.effect(S, Effect.map(mkS(), (a0) => {
  return { get: () => readS(a0) }
}))

export const T = Context.Service<"T", { readonly get: () => Effect.Effect<number, never, never> }>("T")

export const TLayer = Layer.effect(T, Effect.map(mkT(), (a0) => {
  return { get: () => readT(a0) }
}))

export const main: Effect.Effect<number, never, never> = Effect.succeed(0)
