/** Record term and selection helpers emitted by the structural target printer.
 * Metadata retains the original declaration for reading; it does not validate a host object.
 * Checked program admission owns formation and typing before target execution. */
import { Effect, Option } from "effect"

/** The declared type supplies contextual typing, including absent optional fields. */
export const recordValue = <T>(_metadata: unknown, value: T): T => value

/** Required lookup retains never for an impossible receiver. */
export const recordRequired = <K extends PropertyKey>(key: K) =>
  <R extends { readonly [P in K]: unknown }>(target: R): R[K] => target[key]

type OptionalResult<R, K extends keyof R> =
  R extends unknown ? Option.Option<Required<R>[K]> : never

/** Own-property presence distinguishes absence from Some(undefined).
 * Required<R> removes only the optional flag under exactOptionalPropertyTypes. */
export const recordOptional = <K extends PropertyKey>(key: K) =>
  <R extends { readonly [P in K]?: unknown }>(target: R): OptionalResult<R, K> =>
    (Object.prototype.hasOwnProperty.call(target, key)
      ? Option.some(target[key]) : Option.none()) as OptionalResult<R, K>

type Overwrite<R, K extends PropertyKey, V> =
  R extends object ? Omit<R, K> & { readonly [P in K]: V } : never

/** Copy the target before evaluating the replacement, then write an own computed key.
 * The conditional result distributes over unions and retains an impossible receiver. */
export const recordSet = <K extends PropertyKey>(key: K) => <R extends object>(target: R) => {
  const snapshot = { ...target }
  return <const V>(value: V): Overwrite<R, K, V> =>
    ({ ...snapshot, [key]: value }) as unknown as Overwrite<R, K, V>
}

/** Whole-record selection on checked unions of required literal _tag fields.
 * Each branch receives the original object when invoked; only the chosen branch is invoked.
 * Broad string or optional discriminants are outside the checked decision fragment. */
export const caseTagR = <T, K extends string, A0, E0, R0, A1, E1, R1>(
  value: T,
  tag: K,
  hit: (record: Extract<T, { readonly _tag: K }>) => Effect.Effect<A0, E0, R0>,
  miss: (record: Exclude<T, { readonly _tag: K }>) => Effect.Effect<A1, E1, R1>
): Effect.Effect<A0 | A1, E0 | E1, R0 | R1> =>
  Effect.suspend((): Effect.Effect<A0 | A1, E0 | E1, R0 | R1> =>
    typeof value === "object" && value !== null && Object.prototype.hasOwnProperty.call(value, "_tag") &&
      (value as { readonly _tag?: unknown })._tag === tag
      ? hit(value as Extract<T, { readonly _tag: K }>)
      : miss(value as Exclude<T, { readonly _tag: K }>))
