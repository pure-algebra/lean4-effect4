/**
 * The replay plane, one front door. The session runtime, the pure reducer,
 * operation description, and the replayable service kit re-exported under one
 * namespace. The reducer's clause helpers stay module-internal in
 * `src/replay/Reducer.ts`: they exist for file-by-file correspondence with the
 * Lean model, not for callers.
 */

// The session runtime over a CAS store. `Service` aliases the tag so the
// composed name reads `Replay.Service`, matching the Cas namespace rule.
export {
  layerReplay as layer,
  record,
  Replay,
  Replay as Service,
  replay,
  session,
} from "./replay/Replay.ts"
export type { ReplayShape as Shape } from "./replay/Replay.ts"

// The pure reducer — the model-correspondence artifact.
export { reduce } from "./replay/Reducer.ts"

// Session vocabulary shared by the reducer and the runtime.
export {
  isWellFormed,
  MismatchCategory,
  RecordedOutcome,
  ReplayMode,
} from "./replay/Session.ts"
export type {
  AmbientService,
  HistoryEntry,
  Input,
  Invocation,
  Outcome,
  SessionOutcome,
  SessionOptions,
  SessionResult,
  SessionState,
  SessionStatus,
  StepOut,
  StepResult,
  Terminal,
  TerminalSchemas,
} from "./replay/Session.ts"

// Decision traces observed by sessions.
export type { Decision, DecisionTrace } from "./replay/Decision.ts"

// Operation description.
export { describeService } from "./replay/Operation.ts"
export type {
  AnyOperationDescription,
  LeafReplay,
  MethodDescription,
  OperationDescription,
  OperationSchema,
  ServiceDescriptions,
} from "./replay/Operation.ts"

// The replayable service kit.
export { DoubleWrap, replayable } from "./replay/ServiceAdapter.ts"
export type {
  Live,
  ReplayableKit,
  ReplayableLayerKit,
  ReplayableValueKit,
} from "./replay/ServiceAdapter.ts"

// The abort-path witness receipt sink. Defaults to a drop sink;
// production compositions override the reference.
export { WitnessSink } from "./replay/WitnessSink.ts"
export type { WitnessReceipt, WitnessSinkShape } from "./replay/WitnessSink.ts"

// Eager service hydration from typed CAS value projections — the
// replayable kits' companion (lowercase `service`, a factory; the
// capitalized `Service` above is the session tag).
export { service } from "./replay/Service.ts"
export type {
  CasService,
  EffectServiceOptions,
  SyncServiceOptions,
} from "./replay/Service.ts"
