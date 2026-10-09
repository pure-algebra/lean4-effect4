/** Printed list-fold and select heads, shared by truth and finite emitted packets. */
import { Effect, Option } from "effect"

// ---- the list fold's printed head (`Codegen/ListFold.lean`, decisions row 228) -------------

/** `Term.fold accTy list init body`, printed `fold(list, init, (acc, x) => body)`: the body
 * runs once for each element, from the head, and the empty list answers `init` (`evalTerm`'s
 * clause, `src/Effect4/Machine/Term.lean`). `reduce` with an initial value has that order.
 *
 * Without a type argument both parameters are inferred: `B` from `init`, where a fresh literal
 * widens as Lean's literal rule does, and `A` from the list. The ordinary printer writes a
 * stated accumulator as `fold<B>(…)`. TypeScript then uses the default `any` for `A`.
 * At a joined input, the typed printer supplies both checked arguments, `fold<B, A>(…)`.
 * Lean's checker types the element in either case (`argTy`'s fold arm). */
export const fold = <B, A = any>(xs: ReadonlyArray<A>, init: B, step: (acc: B, x: A) => B): B =>
  xs.reduce(step, init)

// ---- `select`'s printed heads (`Codegen/Print.lean`, `Head.optionCase`/`Head.caseTag`) ----

/** Boolean selection evaluates its condition and constructs only its selected arm at execution.
 * Independent arm columns retain their success, error, and service unions. */
export const ifCase = <A0, E0, R0, A1, E1, R1>(
  condition: () => boolean,
  onTrue: () => Effect.Effect<A0, E0, R0>,
  onFalse: () => Effect.Effect<A1, E1, R1>
): Effect.Effect<A0 | A1, E0 | E1, R0 | R1> =>
  Effect.suspend((): Effect.Effect<A0 | A1, E0 | E1, R0 | R1> => { const yes = onTrue(); const no = onFalse(); return condition() ? yes : no })

/** `Eff.select s .option a0 a1`: `none` runs the first arm, `some a` the second with `a`
 * bound (`Decision.decide .option`). The scrutinee is evaluated once, by the caller; the
 * chosen arm is built inside the suspension, as `branch`'s printed image does. */
export const optionCase = <S, A0, E0, R0, A1, E1, R1>(
  scrutinee: Option.Option<S>,
  onNone: () => Effect.Effect<A0, E0, R0>,
  onSome: (value: S) => Effect.Effect<A1, E1, R1>
): Effect.Effect<A0 | A1, E0 | E1, R0 | R1> =>
  Effect.suspend((): Effect.Effect<A0 | A1, E0 | E1, R0 | R1> =>
    Option.match(scrutinee, { onNone, onSome }))

/** `Eff.select s (.tag t) a0 a1`: a pair `[t, payload]` runs the first arm on the payload,
 * every other value the second arm on the whole value (`Decision.decide (.tag t)`,
 * `Val.tagPayload?`). The test only selects; the arm types come from the conditional types
 * on `T`: `Extract` is the selected members, its `[1]` is `Ty.payloadTy`, `Exclude` is
 * `Ty.diffTag`. They narrow exactly on a union of literal-tagged pairs and scalars
 * (`Ty.taggedColumn`). */
export const caseTag = <T, K extends string, A0, E0, R0, A1, E1, R1>(
  value: T,
  tag: K,
  hit: (payload: Extract<T, readonly [K, unknown]>[1]) => Effect.Effect<A0, E0, R0>,
  miss: (rest: Exclude<T, readonly [K, unknown]>) => Effect.Effect<A1, E1, R1>
): Effect.Effect<A0 | A1, E0 | E1, R0 | R1> =>
  Effect.suspend((): Effect.Effect<A0 | A1, E0 | E1, R0 | R1> =>
    Array.isArray(value) && value.length === 2 && value[0] === tag
      ? hit((value as any)[1])
      : miss(value as any))

