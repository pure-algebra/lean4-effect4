/**
 * Total synchronous replay reducer mirrored from Effects/Replay/Reducer.lean.
 * Helper names and branch order intentionally follow the model file so the
 * correspondence review can align them line by line.
 */
import type {
  Input,
  Invocation,
  MismatchCategory,
  Outcome,
  SessionState,
  StepOut,
  Terminal,
} from "./Session.ts"

/** Absorb an input: no state change and no emitted decisions. */
export const absorb = <Op extends string, Req extends string, Val, Err>(
  state: SessionState<Op, Req, Val, Err>,
): StepOut<Op, Req, Val, Err> => ({
  result: { _tag: "Absorbed" },
  state,
  decisions: [],
})

/** Reject at the current cursor, freezing history, discarding any
 * outstanding delegation, and aborting the session. */
export const rejectStep = <Op extends string, Req extends string, Val, Err>(
  state: SessionState<Op, Req, Val, Err>,
  category: MismatchCategory,
): StepOut<Op, Req, Val, Err> => ({
  result: { _tag: "Rejected", category, at: state.cursor },
  state: { ...state, status: "aborted", pending: undefined },
  decisions: [{ _tag: "TypedRejection", category, at: state.cursor }],
})

/** Record mode, invocation: register the outstanding delegation and
 * request live execution; the occurrence is not claimed until the outcome
 * arrives. Delegation is exclusive — a second invocation while one is
 * outstanding is the interleaving the sequential protocol refuses. */
export const invokeRecord = <Op extends string, Req extends string, Val, Err>(
  state: SessionState<Op, Req, Val, Err>,
  invocation: Invocation<Op, Req>,
): StepOut<Op, Req, Val, Err> => {
  if (state.pending !== undefined) {
    return rejectStep(state, "DelegationOutstanding")
  }
  return {
    result: { _tag: "Delegated" },
    state: { ...state, pending: invocation },
    decisions: [{
      _tag: "LiveDelegation",
      operation: invocation.op,
      at: state.cursor,
    }],
  }
}

/** Record mode, outcome arrived: append the occurrence the outstanding
 * delegation solicited and clear it. An outcome nobody solicited — none
 * outstanding, or a different invocation than registered — is refused. */
export const appendRecord = <Op extends string, Req extends string, Val, Err>(
  state: SessionState<Op, Req, Val, Err>,
  invocation: Invocation<Op, Req>,
  outcome: Outcome<Val, Err>,
): StepOut<Op, Req, Val, Err> => {
  const pending = state.pending
  if (pending === undefined) return rejectStep(state, "UnsolicitedOutcome")
  if (
    pending.op !== invocation.op ||
    pending.revision !== invocation.revision ||
    pending.request !== invocation.request
  ) {
    return rejectStep(state, "UnsolicitedOutcome")
  }
  return {
    result: { _tag: "Appended" },
    state: {
      ...state,
      pending: undefined,
      history: [...state.history, { ...invocation, outcome }],
      cursor: state.cursor + 1,
    },
    decisions: [{
      _tag: "OccurrenceAppended",
      operation: invocation.op,
      at: state.cursor,
    }],
  }
}

/** Record mode, append refused: abort without recording the occurrence,
 * discarding the outstanding delegation. */
export const abortRecord = <Op extends string, Req extends string, Val, Err>(
  state: SessionState<Op, Req, Val, Err>,
): StepOut<Op, Req, Val, Err> => ({
  result: { _tag: "Aborted" },
  state: { ...state, status: "aborted", pending: undefined },
  decisions: [],
})

/** Complete exactly at the end of history; otherwise reject the unconsumed
 * suffix and retain the program terminal in the session outcome. */
export const completeStep = <Op extends string, Req extends string, Val, Err>(
  state: SessionState<Op, Req, Val, Err>,
  terminal: Terminal<Val, Err>,
): StepOut<Op, Req, Val, Err> => {
  if (state.cursor === state.history.length) {
    return {
      result: {
        _tag: "SessionOutcome",
        outcome: { _tag: "Completed", terminal },
      },
      state,
      decisions: [{ _tag: "Completed", consumed: state.cursor }],
    }
  }

  return {
    result: {
      _tag: "SessionOutcome",
      outcome: {
        _tag: "Rejected",
        category: "UnconsumedSuffix",
        at: state.cursor,
        terminalSoFar: terminal,
      },
    },
    state: { ...state, status: "aborted", pending: undefined },
    decisions: [{
      _tag: "TypedRejection",
      category: "UnconsumedSuffix",
      at: state.cursor,
    }],
  }
}

/** Replay mode, invocation: match operation, revision, then request at the
 * cursor. A mismatch consumes nothing and aborts; an exact match substitutes
 * the recorded outcome and consumes exactly one occurrence. */
export const invokeReplay = <Op extends string, Req extends string, Val, Err>(
  state: SessionState<Op, Req, Val, Err>,
  invocation: Invocation<Op, Req>,
): StepOut<Op, Req, Val, Err> => {
  const entry = state.history[state.cursor]
  if (entry === undefined) return rejectStep(state, "HistoryExhausted")
  if (entry.op !== invocation.op) return rejectStep(state, "OperationMismatch")
  if (entry.revision !== invocation.revision) return rejectStep(state, "RevisionMismatch")
  if (entry.request !== invocation.request) return rejectStep(state, "RequestMismatch")

  return {
    result: { _tag: "Substituted", outcome: entry.outcome },
    state: { ...state, cursor: state.cursor + 1 },
    decisions: [
      {
        _tag: "RecordedSubstitution",
        operation: invocation.op,
        at: state.cursor,
      },
      { _tag: "HistoryConsumed", at: state.cursor },
    ],
  }
}

/** The total, synchronous, pure replay reducer. The branch order mirrors
 * Effects.Replay.reduce so the implementation can be reviewed rule by rule. */
export const reduce = <Op extends string, Req extends string, Val, Err>(
  state: SessionState<Op, Req, Val, Err>,
  input: Input<Op, Req, Val, Err>,
): StepOut<Op, Req, Val, Err> => {
  if (state.status === "aborted") return absorb(state)

  if (state.mode === "record") {
    switch (input._tag) {
      case "Invoke":
        return invokeRecord(state, input.invocation)
      case "Recorded":
        return appendRecord(state, input.invocation, input.outcome)
      case "AppendFailed":
        return abortRecord(state)
      case "Complete":
        return completeStep(state, input.terminal)
    }
  }

  switch (input._tag) {
    case "Invoke":
      return invokeReplay(state, input.invocation)
    case "Recorded":
    case "AppendFailed":
      return absorb(state)
    case "Complete":
      return completeStep(state, input.terminal)
  }
}
