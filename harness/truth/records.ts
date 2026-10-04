/** Record helpers emitted by Codegen.Record. These are ordinary values, not effects.
 * Metadata retains the original declaration for reading; it does not validate a host object.
 * Checked program admission owns formation and typing before target execution. */
import { Effect, Option } from "effect"

/** The declared type supplies contextual typing, including absent optional fields. */
export const recordValue = <T>(_metadata: unknown, value: T): T => value

/** Presence uses an own property. A present undefined value remains Some(undefined).
 * Required<T> removes only the optional flag under exactOptionalPropertyTypes. */
export const recordOptional = <K extends PropertyKey>(key: K) =>
  <T extends { readonly [P in K]?: unknown }>(target: T): Option.Option<Required<T>[K]> =>
    Object.prototype.hasOwnProperty.call(target, key)
      ? Option.some(target[key] as Required<T>[K])
      : Option.none()

/** The object spread already performs the overwrite, evaluating target then replacement.
 * Const inference retains literal field types; the type-level key identifies the stored form. */
export const recordSet = <K extends PropertyKey>() =>
  <const R extends { readonly [P in K]: unknown }>(result: R): R => result

/** Whole-record selection on checked unions of required literal _tag fields.
 * Both callbacks receive the original object; only the selected callback is constructed.
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
