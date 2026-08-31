/**
 * Total sans-io remote client machine mirrored from
 * Effects/Remote/Machine.lean.
 *
 * Helper names and branch order intentionally follow the Lean source so the
 * correspondence review can align both files rule by rule. This module owns
 * no Effect service and performs no I/O.
 */
import { Equal, HashMap, HashSet, Match, Option, pipe } from "effect"

export interface Budgets {
  readonly maxBytes: number
  readonly maxKeys: number
}

export interface Params<K, B> {
  readonly budgets: Budgets
  readonly size: (bytes: B) => number
  readonly verify: (key: K, bytes: B) => boolean
}

export type OpId = number

export type OpState<K, B> =
  | { readonly _tag: "Loading"; readonly key: K }
  | { readonly _tag: "FindingMissing"; readonly keys: ReadonlyArray<K> }
  | { readonly _tag: "Uploading"; readonly key: K; readonly bytes: B }
  | { readonly _tag: "Publishing"; readonly key: K }

export type Op<K, B> =
  | { readonly _tag: "Load"; readonly key: K }
  | { readonly _tag: "FindMissing"; readonly keys: ReadonlyArray<K> }
  | { readonly _tag: "Upload"; readonly key: K; readonly bytes: B }
  | { readonly _tag: "PublishRoot"; readonly key: K; readonly closure: ReadonlyArray<K> }
  | { readonly _tag: "Attest"; readonly key: K; readonly bytes: B }

export type KeyStatus<K, B> =
  | { readonly _tag: "Found"; readonly key: K; readonly bytes: B }
  | { readonly _tag: "Missing"; readonly key: K }
  | { readonly _tag: "Failed"; readonly key: K }

export type Event<K, B> =
  | { readonly _tag: "Ok"; readonly declared: number; readonly bytes: B }
  | { readonly _tag: "Absent" }
  | { readonly _tag: "Truncated" }
  | { readonly _tag: "Reset" }
  | { readonly _tag: "Silence" }
  | { readonly _tag: "Unauthenticated" }
  | { readonly _tag: "Denied" }
  | { readonly _tag: "RateLimited"; readonly retryAfter?: number }
  | { readonly _tag: "Capacity" }
  | { readonly _tag: "Redirected" }
  | { readonly _tag: "IntegrityMismatch" }
  | { readonly _tag: "BatchResult"; readonly results: ReadonlyArray<KeyStatus<K, B>> }
  | {
    readonly _tag: "Capabilities"
    readonly limits: { readonly maxBatchKeys: number; readonly maxBlobBytes: number }
  }
  | { readonly _tag: "Interrupted" }

export type MInput<K, B> =
  | { readonly _tag: "Request"; readonly id: OpId; readonly op: Op<K, B> }
  | { readonly _tag: "FromWire"; readonly id: OpId; readonly event: Event<K, B> }

export type Command<K, B> =
  | { readonly _tag: "ProbeCapabilities" }
  | { readonly _tag: "Load"; readonly key: K }
  | { readonly _tag: "FindMissing"; readonly keys: ReadonlyArray<K> }
  | { readonly _tag: "Upload"; readonly key: K; readonly bytes: B }
  | { readonly _tag: "QueryCommitted"; readonly key: K }
  | { readonly _tag: "PublishRoot"; readonly key: K }

export type MResult<K, B> =
  | { readonly _tag: "Commanded" }
  | { readonly _tag: "Delivered"; readonly key: K; readonly bytes: B }
  | { readonly _tag: "Uploaded"; readonly key: K }
  | { readonly _tag: "NotFound"; readonly key: K }
  | { readonly _tag: "BudgetRejected"; readonly key: K }
  | { readonly _tag: "IntegrityRejected"; readonly key: K }
  | { readonly _tag: "RepeatRefused"; readonly key: K }
  | { readonly _tag: "TransportFailed"; readonly key: K }
  | { readonly _tag: "AuthFailed"; readonly key: K }
  | { readonly _tag: "DuplicateId" }
  | { readonly _tag: "BatchAnswered"; readonly found: ReadonlyArray<K>; readonly missing: ReadonlyArray<K> }
  | { readonly _tag: "BatchRejected" }
  | { readonly _tag: "BatchFailed" }
  | { readonly _tag: "KeyBudgetRejected" }
  | { readonly _tag: "Published"; readonly key: K }
  | { readonly _tag: "OrderingRefused"; readonly key: K }
  | { readonly _tag: "PublishFailed"; readonly key: K }
  | { readonly _tag: "Attested"; readonly key: K }
  | { readonly _tag: "AttestRefused"; readonly key: K }
  | { readonly _tag: "Absorbed" }

export type RDecision<K, B> =
  | { readonly _tag: "Issued"; readonly command: Command<K, B> }
  | { readonly _tag: "Verified"; readonly key: K }
  | { readonly _tag: "Cached"; readonly key: K }
  | { readonly _tag: "Returned"; readonly key: K }
  | { readonly _tag: "BudgetRejected"; readonly key: K }
  | { readonly _tag: "IntegrityRejected"; readonly key: K }
  | { readonly _tag: "RepeatRefused"; readonly key: K }
  | { readonly _tag: "GaveUp"; readonly key: K }
  | { readonly _tag: "PresenceNoted"; readonly found: ReadonlyArray<K>; readonly missing: ReadonlyArray<K> }
  | { readonly _tag: "BatchRejected" }
  | { readonly _tag: "BatchGaveUp" }
  | { readonly _tag: "Published"; readonly key: K }
  | { readonly _tag: "OrderingRefused"; readonly key: K }
  | { readonly _tag: "ConfirmedByAttestation"; readonly key: K }
  | { readonly _tag: "AttestationRefused"; readonly key: K }

export interface TaggedCommand<K, B> {
  readonly op: OpId
  readonly command: Command<K, B>
}

export interface TaggedDecision<K, B> {
  readonly op: OpId
  readonly decision: RDecision<K, B>
}

export interface MachineState<K, B> {
  readonly inFlight: HashMap.HashMap<OpId, OpState<K, B>>
  readonly cache: HashSet.HashSet<K>
  readonly rejected: HashSet.HashSet<readonly [K, B]>
  readonly reportedPresent: HashSet.HashSet<K>
  readonly reportedMissing: HashSet.HashSet<K>
  readonly confirmed: HashSet.HashSet<K>
  readonly published: HashSet.HashSet<K>
}

export interface StepOut<K, B> {
  readonly result: MResult<K, B>
  readonly state: MachineState<K, B>
  readonly commands: ReadonlyArray<TaggedCommand<K, B>>
  readonly decisions: ReadonlyArray<TaggedDecision<K, B>>
}

export interface RunOut<K, B> {
  readonly state: MachineState<K, B>
  readonly results: ReadonlyArray<MResult<K, B>>
  readonly decisions: ReadonlyArray<TaggedDecision<K, B>>
  readonly commands: ReadonlyArray<TaggedCommand<K, B>>
}

export const initialMachineState = <K, B>(): MachineState<K, B> => ({
  inFlight: HashMap.empty(),
  cache: HashSet.empty(),
  rejected: HashSet.empty(),
  reportedPresent: HashSet.empty(),
  reportedMissing: HashSet.empty(),
  confirmed: HashSet.empty(),
  published: HashSet.empty(),
})

/** Absorb an uncorrelated or unexpected input. */
export const absorbOut = <K, B>(state: MachineState<K, B>): StepOut<K, B> => ({
  result: { _tag: "Absorbed" },
  state,
  commands: [],
  decisions: [],
})

/** Handle a load's correlated wire event. */
export const loadEvent = <K, B>(
  params: Params<K, B>,
  state: MachineState<K, B>,
  id: OpId,
  key: K,
  event: Event<K, B>,
): StepOut<K, B> => {
  if (event._tag === "Ok") {
    if (event.declared > params.budgets.maxBytes) {
      return {
        result: { _tag: "BudgetRejected", key },
        state: { ...state, inFlight: HashMap.remove(state.inFlight, id) },
        commands: [],
        decisions: [
          { op: id, decision: { _tag: "BudgetRejected", key } },
          { op: id, decision: { _tag: "GaveUp", key } },
        ],
      }
    }
    if (params.verify(key, event.bytes)) {
      return {
        result: { _tag: "Delivered", key, bytes: event.bytes },
        state: {
          ...state,
          inFlight: HashMap.remove(state.inFlight, id),
          cache: HashSet.add(state.cache, key),
          confirmed: HashSet.add(state.confirmed, key),
        },
        commands: [],
        decisions: [
          { op: id, decision: { _tag: "Verified", key } },
          { op: id, decision: { _tag: "Cached", key } },
          { op: id, decision: { _tag: "Returned", key } },
        ],
      }
    }
    return {
      result: { _tag: "IntegrityRejected", key },
      state: { ...state, inFlight: HashMap.remove(state.inFlight, id) },
      commands: [],
      decisions: [
        { op: id, decision: { _tag: "IntegrityRejected", key } },
        { op: id, decision: { _tag: "GaveUp", key } },
      ],
    }
  }

  if (event._tag === "Absent") {
    return {
      result: { _tag: "NotFound", key },
      state: { ...state, inFlight: HashMap.remove(state.inFlight, id) },
      commands: [],
      decisions: [{ op: id, decision: { _tag: "GaveUp", key } }],
    }
  }

  if (event._tag === "Unauthenticated") {
    return {
      result: { _tag: "AuthFailed", key },
      state: { ...state, inFlight: HashMap.remove(state.inFlight, id) },
      commands: [],
      decisions: [{ op: id, decision: { _tag: "GaveUp", key } }],
    }
  }

  if (event._tag === "Denied") {
    return {
      result: { _tag: "AuthFailed", key },
      state: { ...state, inFlight: HashMap.remove(state.inFlight, id) },
      commands: [],
      decisions: [{ op: id, decision: { _tag: "GaveUp", key } }],
    }
  }

  return {
    result: { _tag: "TransportFailed", key },
    state: { ...state, inFlight: HashMap.remove(state.inFlight, id) },
    commands: [],
    decisions: [{ op: id, decision: { _tag: "GaveUp", key } }],
  }
}

/** Handle an upload's correlated wire event. */
export const uploadEvent = <K, B>(
  params: Params<K, B>,
  state: MachineState<K, B>,
  id: OpId,
  key: K,
  bytes: B,
  event: Event<K, B>,
): StepOut<K, B> => {
  if (event._tag === "Ok") {
    if (params.verify(key, bytes)) {
      return {
        result: { _tag: "Uploaded", key },
        state: {
          ...state,
          inFlight: HashMap.remove(state.inFlight, id),
          cache: HashSet.add(state.cache, key),
          confirmed: HashSet.add(state.confirmed, key),
        },
        commands: [],
        decisions: [{ op: id, decision: { _tag: "Cached", key } }],
      }
    }
    return {
      result: { _tag: "IntegrityRejected", key },
      state: {
        ...state,
        inFlight: HashMap.remove(state.inFlight, id),
        rejected: HashSet.add<readonly [K, B]>(state.rejected, [key, bytes]),
      },
      commands: [],
      decisions: [
        { op: id, decision: { _tag: "IntegrityRejected", key } },
        { op: id, decision: { _tag: "GaveUp", key } },
      ],
    }
  }

  if (event._tag === "IntegrityMismatch") {
    return {
      result: { _tag: "IntegrityRejected", key },
      state: {
        ...state,
        inFlight: HashMap.remove(state.inFlight, id),
        rejected: HashSet.add<readonly [K, B]>(state.rejected, [key, bytes]),
      },
      commands: [],
      decisions: [
        { op: id, decision: { _tag: "IntegrityRejected", key } },
        { op: id, decision: { _tag: "GaveUp", key } },
      ],
    }
  }

  if (event._tag === "Unauthenticated") {
    return {
      result: { _tag: "AuthFailed", key },
      state: { ...state, inFlight: HashMap.remove(state.inFlight, id) },
      commands: [],
      decisions: [{ op: id, decision: { _tag: "GaveUp", key } }],
    }
  }

  if (event._tag === "Denied") {
    return {
      result: { _tag: "AuthFailed", key },
      state: { ...state, inFlight: HashMap.remove(state.inFlight, id) },
      commands: [],
      decisions: [{ op: id, decision: { _tag: "GaveUp", key } }],
    }
  }

  return {
    result: { _tag: "TransportFailed", key },
    state: { ...state, inFlight: HashMap.remove(state.inFlight, id) },
    commands: [],
    decisions: [{ op: id, decision: { _tag: "GaveUp", key } }],
  }
}

/** Whether batch results account for the requested keys exactly, in request order. */
export const accountsFor = <K, B>(
  keys: ReadonlyArray<K>,
  results: ReadonlyArray<KeyStatus<K, B>>,
): boolean => {
  if (keys.length !== results.length) return false
  return keys.every((key, index) => {
    const result = results[index]
    return result !== undefined && Equal.equals(key, result.key)
  })
}

interface PresenceNote<K, B> {
  readonly state: MachineState<K, B>
  readonly found: ReadonlyArray<K>
  readonly missing: ReadonlyArray<K>
}

/** Record advisory presence data without admitting or negatively caching anything. */
export const notePresence = <K, B>(
  state: MachineState<K, B>,
  results: ReadonlyArray<KeyStatus<K, B>>,
): PresenceNote<K, B> => {
  let reportedPresent = state.reportedPresent
  let reportedMissing = state.reportedMissing
  const found: Array<K> = []
  const missing: Array<K> = []

  for (const result of results) {
    if (result._tag === "Found") {
      reportedPresent = HashSet.add(reportedPresent, result.key)
      found.push(result.key)
    } else if (result._tag === "Missing") {
      reportedMissing = HashSet.add(reportedMissing, result.key)
      missing.push(result.key)
    }
  }

  return {
    state: { ...state, reportedPresent, reportedMissing },
    found,
    missing,
  }
}

/** Handle a find-missing operation's correlated wire event. */
export const batchEvent = <K, B>(
  state: MachineState<K, B>,
  id: OpId,
  keys: ReadonlyArray<K>,
  event: Event<K, B>,
): StepOut<K, B> => {
  if (event._tag === "BatchResult") {
    if (accountsFor(keys, event.results)) {
      const noted = notePresence(state, event.results)
      return {
        result: { _tag: "BatchAnswered", found: noted.found, missing: noted.missing },
        state: {
          ...noted.state,
          inFlight: HashMap.remove(noted.state.inFlight, id),
        },
        commands: [],
        decisions: [{
          op: id,
          decision: { _tag: "PresenceNoted", found: noted.found, missing: noted.missing },
        }],
      }
    }
    return {
      result: { _tag: "BatchRejected" },
      state: { ...state, inFlight: HashMap.remove(state.inFlight, id) },
      commands: [],
      decisions: [{ op: id, decision: { _tag: "BatchRejected" } }],
    }
  }

  return {
    result: { _tag: "BatchFailed" },
    state: { ...state, inFlight: HashMap.remove(state.inFlight, id) },
    commands: [],
    decisions: [{ op: id, decision: { _tag: "BatchGaveUp" } }],
  }
}

/** Handle a publish operation's correlated wire event. */
export const publishEvent = <K, B>(
  state: MachineState<K, B>,
  id: OpId,
  key: K,
  event: Event<K, B>,
): StepOut<K, B> => {
  if (event._tag === "Ok") {
    return {
      result: { _tag: "Published", key },
      state: {
        ...state,
        inFlight: HashMap.remove(state.inFlight, id),
        published: HashSet.add(state.published, key),
      },
      commands: [],
      decisions: [{ op: id, decision: { _tag: "Published", key } }],
    }
  }

  return {
    result: { _tag: "PublishFailed", key },
    state: { ...state, inFlight: HashMap.remove(state.inFlight, id) },
    commands: [],
    decisions: [{ op: id, decision: { _tag: "GaveUp", key } }],
  }
}

/** Whether a root and every member of its declared closure stand confirmed. */
export const publishEntitled = <K, B>(
  state: MachineState<K, B>,
  key: K,
  closure: ReadonlyArray<K>,
): boolean => HashSet.has(state.confirmed, key)
  && closure.every((member) => HashSet.has(state.confirmed, member))

/** The total remote client step. */
export const step = <K, B>(
  params: Params<K, B>,
  state: MachineState<K, B>,
  input: MInput<K, B>,
): StepOut<K, B> => {
  if (input._tag === "Request") {
    if (Option.isSome(HashMap.get(state.inFlight, input.id))) {
      return { result: { _tag: "DuplicateId" }, state, commands: [], decisions: [] }
    }

    if (input.op._tag === "Load") {
      const command: Command<K, B> = { _tag: "Load", key: input.op.key }
      return {
        result: { _tag: "Commanded" },
        state: {
          ...state,
          inFlight: HashMap.set(state.inFlight, input.id, {
            _tag: "Loading",
            key: input.op.key,
          }),
        },
        commands: [{ op: input.id, command }],
        decisions: [{ op: input.id, decision: { _tag: "Issued", command } }],
      }
    }

    if (input.op._tag === "FindMissing") {
      if (input.op.keys.length > params.budgets.maxKeys) {
        return {
          result: { _tag: "KeyBudgetRejected" },
          state,
          commands: [],
          decisions: [{ op: input.id, decision: { _tag: "BatchRejected" } }],
        }
      }
      const command: Command<K, B> = { _tag: "FindMissing", keys: input.op.keys }
      return {
        result: { _tag: "Commanded" },
        state: {
          ...state,
          inFlight: HashMap.set(state.inFlight, input.id, {
            _tag: "FindingMissing",
            keys: input.op.keys,
          }),
        },
        commands: [{ op: input.id, command }],
        decisions: [{ op: input.id, decision: { _tag: "Issued", command } }],
      }
    }

    if (input.op._tag === "Upload") {
      const { bytes, key } = input.op
      if (params.size(bytes) > params.budgets.maxBytes) {
        return {
          result: { _tag: "BudgetRejected", key },
          state,
          commands: [],
          decisions: [{ op: input.id, decision: { _tag: "BudgetRejected", key } }],
        }
      }
      if (HashSet.has<readonly [K, B]>(state.rejected, [key, bytes])) {
        return {
          result: { _tag: "RepeatRefused", key },
          state,
          commands: [],
          decisions: [{ op: input.id, decision: { _tag: "RepeatRefused", key } }],
        }
      }
      if (params.verify(key, bytes)) {
        if (HashSet.has(state.cache, key)) {
          return {
            result: { _tag: "Uploaded", key },
            state,
            commands: [],
            decisions: [{ op: input.id, decision: { _tag: "Verified", key } }],
          }
        }
        const command: Command<K, B> = { _tag: "Upload", key, bytes }
        return {
          result: { _tag: "Commanded" },
          state: {
            ...state,
            inFlight: HashMap.set(state.inFlight, input.id, {
              _tag: "Uploading",
              key,
              bytes,
            }),
          },
          commands: [{ op: input.id, command }],
          decisions: [
            { op: input.id, decision: { _tag: "Verified", key } },
            { op: input.id, decision: { _tag: "Issued", command } },
          ],
        }
      }
      return {
        result: { _tag: "IntegrityRejected", key },
        state: {
          ...state,
          rejected: HashSet.add<readonly [K, B]>(state.rejected, [key, bytes]),
        },
        commands: [],
        decisions: [
          { op: input.id, decision: { _tag: "IntegrityRejected", key } },
          { op: input.id, decision: { _tag: "GaveUp", key } },
        ],
      }
    }

    if (input.op._tag === "Attest") {
      // Attested presence confirms for publish (RMT-017): the peer
      // reported the key present and the client verifies the held bytes
      // locally — the cache is never touched, so presence stays planning
      // data for every read path.
      const { key, bytes } = input.op
      if (params.verify(key, bytes) && HashSet.has(state.reportedPresent, key)) {
        return {
          result: { _tag: "Attested", key },
          state: { ...state, confirmed: HashSet.add(state.confirmed, key) },
          commands: [],
          decisions: [{
            op: input.id,
            decision: { _tag: "ConfirmedByAttestation", key },
          }],
        }
      }
      return {
        result: { _tag: "AttestRefused", key },
        state,
        commands: [],
        decisions: [{
          op: input.id,
          decision: { _tag: "AttestationRefused", key },
        }],
      }
    }

    if (!publishEntitled(state, input.op.key, input.op.closure)) {
      return {
        result: { _tag: "OrderingRefused", key: input.op.key },
        state,
        commands: [],
        decisions: [{
          op: input.id,
          decision: { _tag: "OrderingRefused", key: input.op.key },
        }],
      }
    }
    const command: Command<K, B> = { _tag: "PublishRoot", key: input.op.key }
    return {
      result: { _tag: "Commanded" },
      state: {
        ...state,
        inFlight: HashMap.set(state.inFlight, input.id, {
          _tag: "Publishing",
          key: input.op.key,
        }),
      },
      commands: [{ op: input.id, command }],
      decisions: [{ op: input.id, decision: { _tag: "Issued", command } }],
    }
  }

  const current = HashMap.get(state.inFlight, input.id)
  if (Option.isNone(current)) return absorbOut(state)
  if (current.value._tag === "Loading") {
    return loadEvent(params, state, input.id, current.value.key, input.event)
  }
  if (current.value._tag === "FindingMissing") {
    return batchEvent(state, input.id, current.value.keys, input.event)
  }
  if (current.value._tag === "Uploading") {
    return uploadEvent(
      params,
      state,
      input.id,
      current.value.key,
      current.value.bytes,
      input.event,
    )
  }
  return publishEvent(state, input.id, current.value.key, input.event)
}

/** RMT-001's entitlement guard. */
export const entitledToCache = <K, B>(
  params: Params<K, B>,
  state: MachineState<K, B>,
  input: MInput<K, B>,
): boolean => {
  if (input._tag !== "FromWire" || input.event._tag !== "Ok") return false
  const current = HashMap.get(state.inFlight, input.id)
  if (Option.isNone(current)) return false
  if (current.value._tag === "Loading") {
    return !(input.event.declared > params.budgets.maxBytes)
      && params.verify(current.value.key, input.event.bytes)
  }
  return current.value._tag === "Uploading"
    && params.verify(current.value.key, current.value.bytes)
}

/** RMT-002's declared-budget guard. */
export const overBudget = <K, B>(
  params: Params<K, B>,
  state: MachineState<K, B>,
  input: MInput<K, B>,
): boolean =>
  pipe(
    Match.type<MInput<K, B>>(),
    Match.tagsExhaustive({
      Request: (request) =>
        request.op._tag === "Upload"
          && Option.isNone(HashMap.get(state.inFlight, request.id))
          && params.size(request.op.bytes) > params.budgets.maxBytes,
      FromWire: (fromWire) => {
        if (fromWire.event._tag !== "Ok") return false
        const current = HashMap.get(state.inFlight, fromWire.id)
        return Option.isSome(current)
          && current.value._tag === "Loading"
          && fromWire.event.declared > params.budgets.maxBytes
      },
    }),
  )(input)

/** Whether a result is the budget rejection. */
export const isBudgetRejection = <K, B>(result: MResult<K, B>): boolean =>
  result._tag === "BudgetRejected"

/** Run the machine over an input list. */
export const run = <K, B>(
  params: Params<K, B>,
  state: MachineState<K, B>,
  inputs: ReadonlyArray<MInput<K, B>>,
): RunOut<K, B> => {
  const [input, ...restInputs] = inputs
  if (input === undefined) {
    return { state, results: [], decisions: [], commands: [] }
  }
  const output = step(params, state, input)
  const rest = run(params, output.state, restInputs)
  return {
    state: rest.state,
    results: [output.result, ...rest.results],
    decisions: [...output.decisions, ...rest.decisions],
    commands: [...output.commands, ...rest.commands],
  }
}
