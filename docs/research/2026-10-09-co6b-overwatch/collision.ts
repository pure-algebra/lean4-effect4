import { Context, Effect, Layer } from "effect"
const mkS = (_a0: void): Effect.Effect<number, never, never> => Effect.succeed(1)
const readS = (a0: number): Effect.Effect<number, never, never> => Effect.succeed(a0)
const mkT = (_a0: void): Effect.Effect<number, never, never> => Effect.succeed(2)
const readT = (a0: number): Effect.Effect<number, never, never> => Effect.succeed(a0)
export const S = Context.Service<"S", { readonly get: () => Effect.Effect<number, never, never> }>("S")

export const SLayer = Layer.effect(S, Effect.map(mkS(), (a0) => {
  return { get: () => readS(a0) }
}))

export const SLayer = Context.Service<"SLayer", { readonly get: () => Effect.Effect<number, never, never> }>("SLayer")

export const SLayerLayer = Layer.effect(SLayer, Effect.map(mkT(), (a0) => {
  return { get: () => readT(a0) }
}))
