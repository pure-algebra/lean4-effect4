/** Record helpers emitted by Codegen.Record. These are ordinary values, not effects.
 * Metadata retains the original declaration for reading; it does not validate a host object.
 * Checked program admission owns formation and typing before target execution. */
import { Option } from "effect"

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
