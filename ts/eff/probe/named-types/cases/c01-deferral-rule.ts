// expect: TS2456 TS2456 TS2456 TS2456 TS2456 TS2456 TS2456 TS2315
// tsgo's deferral rule. A recursive alias is refused (TS2456) when a cycle passes only through
// union members and the arguments of type alias instantiations (Option.Option, Result.Result,
// Exit.Exit, Readonly<Record<...>>, a parameterized declared name). An object type, a tuple, and
// the argument of an interface (ReadonlyArray, Cause, Ref, Fiber, Deferred) defer the cycle.
import type { Exit, Option, Result } from "effect"
// refused: seven aliases on six cycles that pass only through unions and alias arguments (P1 also
// reads as not generic, TS2315, once its own alias is circular)
export type U1 = Option.Option<U1> | number
export type U2 = Result.Result<number, U2>
export type U3 = Exit.Exit<number, U3>
export type U4 = Option.Option<U5>
export type U5 = Option.Option<U4>
export type U6 = Readonly<Record<string, U6 | number>>
export type P1<A> = Option.Option<P1<A>>
// accepted: each cycle passes through a deferring position
export type D1 = { readonly a: Option.Option<D1> }
export type D2 = ReadonlyArray<Option.Option<D2>>
export type D3 = Option.Option<ReadonlyArray<D3>>
export type D4 = Readonly<Record<string, ReadonlyArray<D4>>>
export type D5 = Result.Result<readonly [D5, number], string>
export type D6 = Option.Option<{ readonly next: D6 }>
export type P2<A> = Option.Option<readonly [A, P2<A>]>
export type D7 = Readonly<{ readonly [key: string]: D7 }>
