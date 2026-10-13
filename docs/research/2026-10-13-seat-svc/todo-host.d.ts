// The host's rows for the check, before the module declares their service keys.
import type { Effect, Option } from "effect"

declare global {
  const TodoRepo: { readonly insert: (request: string) => Effect.Effect<{ readonly done: boolean; readonly id: number; readonly title: string }, readonly ["SqlError", string]>; readonly all: () => Effect.Effect<ReadonlyArray<{ readonly done: boolean; readonly id: number; readonly title: string }>, readonly ["SqlError", string]>; readonly setDone: (request: readonly [number, boolean]) => Effect.Effect<Option.Option<{ readonly done: boolean; readonly id: number; readonly title: string }>, readonly ["SqlError", string]>; readonly delete: (request: number) => Effect.Effect<boolean, readonly ["SqlError", string]> }
}

export {}
