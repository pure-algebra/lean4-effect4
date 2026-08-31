/**
 * The decision trace: the primary observable (ruling GR-8; plan section 3).
 *
 * The TAG menu below is the ratified minimum — live delegation, record-mode
 * occurrence append, recorded substitution, history consumption, typed
 * rejection, completion. The payload shapes are frozen with the M3 reducer;
 * "whether a live adapter was requested" is a derived projection of the
 * trace, never a separate Boolean oracle.
 */
import type { MismatchCategory } from "./Session.ts"

export type Decision =
  | { readonly _tag: "LiveDelegation"; readonly operation: string; readonly at: number }
  | { readonly _tag: "OccurrenceAppended"; readonly operation: string; readonly at: number }
  | { readonly _tag: "RecordedSubstitution"; readonly operation: string; readonly at: number }
  | { readonly _tag: "HistoryConsumed"; readonly at: number }
  | { readonly _tag: "TypedRejection"; readonly category: MismatchCategory; readonly at: number }
  | { readonly _tag: "Completed"; readonly consumed: number }

export type DecisionTrace = ReadonlyArray<Decision>
