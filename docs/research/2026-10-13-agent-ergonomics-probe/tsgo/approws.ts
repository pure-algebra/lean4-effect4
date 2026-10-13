import type { Effect } from "effect"
// What a generated declaration of the application's rows would say (written by hand here).
export declare const Db: {
  open: (request: string) => Effect.Effect<number, never, never>
  close: (request: number) => Effect.Effect<void, never, never>
  query: (request: number) => Effect.Effect<string, never, never>
}
export declare const Todos: { add: (request: string) => Effect.Effect<ReadonlyArray<string>, never, never> }
