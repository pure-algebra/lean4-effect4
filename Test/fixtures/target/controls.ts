/** Independent type claims used to test the target checker, never production expected types. */
import type * as Effect from "../../../ts/eff/node_modules/effect/dist/Effect.js"

export interface R1 { readonly requirement: "R1" }
export interface R2 { readonly requirement: "R2" }
export interface Receiver1 { readonly receiver: "one" }
export interface Receiver2 { readonly receiver: "two" }
export declare const program: Effect.Effect<number, "E1", R1>
export declare const unitProgram: Effect.Effect<void, never, never>
export declare const anyProgram: Effect.Effect<any, never, never>
export declare const nestedAnyProgram: Effect.Effect<{ values: ReadonlyArray<any> }, never, never>
export declare const unknownProgram: Effect.Effect<unknown, never, never>
export declare const method: (text: string, count?: number, ...rest: boolean[]) => Effect.Effect<number, "E1", R1>
export declare function overloaded(text: string): Effect.Effect<number, never, never>
export declare function overloaded(count: number): Effect.Effect<number, never, never>
export declare function generic<T>(value: T): Effect.Effect<T, never, never>

export declare const notEffect: number
export declare const neverSubject: never
