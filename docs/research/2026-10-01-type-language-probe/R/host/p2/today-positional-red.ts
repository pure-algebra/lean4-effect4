// GENERATED for the data probe from ProbeTodayP2.log by a one-off script; not in the tree.
// The prelude atoms and `optionCase` the printed module calls, copied from
// harness/truth/prelude-atoms.gen.ts (lines 34, 49, 58, 63, 68, 108, 116-117, 201) and
// harness/truth/prelude.ts:54-60, so this check needs no harness import.
import { Effect, Option } from "effect"
export const not = (b: boolean): boolean => !b
export const eq = (a: number | string, b: number | string): boolean => a === b
export const pair = <const A, const B>(a: A, b: B): readonly [A, B] => [a, b]
export const fst = <P extends readonly [unknown, unknown]>(p: P): P[0] => p[0]
export const snd = <P extends readonly [unknown, unknown]>(p: P): P[1] => p[1]
export const and = (a: boolean, b: boolean): boolean => a && b
export const tagIs = (tag: string, e: unknown): boolean =>
  Array.isArray(e) && e.length === 2 && e[0] === tag
export const concat = (a: string, b: string): string => a + b
export const optionCase = <S, A0, E0, R0, A1, E1, R1>(
  scrutinee: Option.Option<S>,
  onNone: () => Effect.Effect<A0, E0, R0>,
  onSome: (value: S) => Effect.Effect<A1, E1, R1>
): Effect.Effect<A0 | A1, E0 | E1, R0 | R1> =>
  Effect.suspend((): Effect.Effect<A0 | A1, E0 | E1, R0 | R1> =>
    Option.match(scrutinee, { onNone, onSome }))
// RED CONTROL: the same printed module linked against the idiomatic service signatures of
// p2-handler-layers.ts:26-45 (records as objects, tagged error classes). The printed program
// projects by position, so it must not type-check here.
interface User { readonly id: number; readonly name: string; readonly role: "admin" | "member" }
interface AppConfigShape { readonly adminToken: string; readonly pageSize: number }
declare class SqlError { readonly _tag: "SqlError"; readonly message: string }
declare const AppConfig: { readonly get: () => Effect.Effect<AppConfigShape> }
declare const UserRepo: { readonly findById: (id: number) => Effect.Effect<Option.Option<User>, SqlError> }

// The printed module, verbatim from ProbeTodayP2.log.
export const handle: Effect.Effect<readonly [number, string], readonly [string, string]> = Effect.catchIf(Effect.catchIf(Effect.flatMap(Effect.flatMap(AppConfig.get(), (a0) => Effect.suspend(() => not(eq("secret", fst(a0))) ? Effect.fail(pair("Unauthorized", "bad token")) : Effect.flatMap(Effect.flatMap(UserRepo.findById(1), (a1) => optionCase(a1, () => Effect.fail(pair("NotFound", "1")), (a2) => Effect.succeed(a2))), (a1) => Effect.suspend(() => and(not(eq(snd(snd(a1)), "admin")), not(eq(fst(a1), 2))) ? Effect.fail(pair("Unauthorized", "not yours")) : Effect.flatMap(UserRepo.findById(2), (a2) => optionCase(a2, () => Effect.fail(pair("NotFound", "2")), (a3) => Effect.succeed(a3))))))), (a0) => Effect.succeed(pair(200, fst(snd(a0))))), (a0) => tagIs("Unauthorized", a0), (a0) => Effect.succeed(pair(401, snd(a0))), undefined), (a0) => tagIs("NotFound", a0), (a0) => Effect.succeed(pair(404, concat("no user ", snd(a0)))), undefined)
