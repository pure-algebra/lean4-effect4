import { Effect, Option } from "effect"
// The prelude atoms and `optionCase` the printed module calls, as the data probe's programs seat
// copied them (harness/truth/prelude-atoms.gen.ts; harness/truth/prelude.ts:54-60).
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
// RED: the same rows without DB-15's error adapter: the repository fails with rc.112's class.
interface User { readonly id: number; readonly name: string; readonly role: "admin" | "member" }
interface AppConfigShape { readonly adminToken: string; readonly pageSize: number }
declare class SqlError { readonly _tag: "SqlError"; readonly message: string }
declare const AppConfig: { readonly get: () => Effect.Effect<AppConfigShape> }
declare const UserRepo: { readonly findById: (id: number) => Effect.Effect<Option.Option<User>, SqlError> }
// The module commit 8 must print (seat R's target): ProbeTodayP2.log's printed module with the
// record forms of Q2 (`a0.adminToken`, `a1.role`, `a1.id`, `a0.name`, `{ status: …, body: … }` in
// written order) and the declared answer type in canonical order.
export const handle: Effect.Effect<{ readonly body: string; readonly status: number }, readonly [string, string]> = Effect.catchIf(Effect.catchIf(Effect.flatMap(Effect.flatMap(AppConfig.get(), (a0) => Effect.suspend(() => not(eq("secret", a0.adminToken)) ? Effect.fail(pair("Unauthorized", "bad token")) : Effect.flatMap(Effect.flatMap(UserRepo.findById(1), (a1) => optionCase(a1, () => Effect.fail(pair("NotFound", "1")), (a2) => Effect.succeed(a2))), (a1) => Effect.suspend(() => and(not(eq(a1.role, "admin")), not(eq(a1.id, 2))) ? Effect.fail(pair("Unauthorized", "not yours")) : Effect.flatMap(UserRepo.findById(2), (a2) => optionCase(a2, () => Effect.fail(pair("NotFound", "2")), (a3) => Effect.succeed(a3))))))), (a0) => Effect.succeed({ status: 200, body: a0.name })), (a0) => tagIs("Unauthorized", a0), (a0) => Effect.succeed({ status: 401, body: snd(a0) }), undefined), (a0) => tagIs("NotFound", a0), (a0) => Effect.succeed({ status: 404, body: concat("no user ", snd(a0)) }), undefined)
