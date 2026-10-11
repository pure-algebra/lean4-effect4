import { Context, Effect, Layer } from "effect"
const mkS = (_a0: void): Effect.Effect<number, never, never> => Effect.succeed(1)
const readS = (a0: number): Effect.Effect<number, never, never> => Effect.succeed(a0)
const mkT = (_a0: void): Effect.Effect<number, never, never> => Effect.succeed(2)
const readT = (a0: number): Effect.Effect<number, never, never> => Effect.succeed(a0)
export const S = Context.Service<"S", { readonly __proto__: () => Effect.Effect<number, never, never> }>("S")

export const SLayer = Layer.effect(S, Effect.map(mkS(), (a0) => {
  return { ["__proto__"]: () => readS(a0) }
}))

export const T = Context.Service<"T", { readonly get: () => Effect.Effect<number, never, never> }>("T")

export const TLayer = Layer.effect(T, Effect.map(mkT(), (a0) => {
  return { get: () => readT(a0) }
}))
