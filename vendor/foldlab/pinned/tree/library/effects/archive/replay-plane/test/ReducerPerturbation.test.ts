/**
 * The paired-perturbation reducer sweep: every generated lawful script
 * runs green, and every one-edit unlawful twin must reject with the
 * exact category at the exact position, freeze the history, and absorb
 * everything after. The lawful half keeps the generator honest — a
 * sweep whose seeds drifted into trivially-rejected scripts would turn
 * red on its own assertions, not silently prove nothing.
 */
import { expect, it } from "@effect/vitest"
import { Effect } from "effect"
import { reduce } from "../src/replay/Reducer.ts"
import type {
  HistoryEntry,
  Input,
  Invocation,
  MismatchCategory,
  Outcome,
  SessionState,
} from "../src/replay/Session.ts"

type St = SessionState<string, string, string, string>
type In = Input<string, string, string, string>

/** splitmix32 — deterministic structural generator for the sweep. */
const splitmix32 = (seed: number) => () => {
  seed = (seed + 0x9e3779b9) | 0
  let z = seed
  z = Math.imul(z ^ (z >>> 16), 0x21f0aaad)
  z = Math.imul(z ^ (z >>> 15), 0x735a2d97)
  z = z ^ (z >>> 15)
  return (z >>> 0) / 0x1_0000_0000
}

const pick = <A>(rng: () => number, items: ReadonlyArray<A>): A =>
  items[Math.floor(rng() * items.length)] as A

const OPS = ["acme/Rates/get", "acme/Fx/list", "acme/Docs/put"] as const

interface CallPair {
  readonly invocation: Invocation<string, string>
  readonly outcome: Outcome<string, string>
}

const generatePairs = (rng: () => number): ReadonlyArray<CallPair> => {
  const count = 1 + Math.floor(rng() * 6)
  return Array.from({ length: count }, (_, index) => ({
    invocation: {
      op: pick(rng, OPS),
      revision: 1 + Math.floor(rng() * 3),
      request: `req-${index}-${Math.floor(rng() * 100)}`,
    },
    outcome: rng() < 0.5
      ? { _tag: "Success", value: `ok-${index}` }
      : { _tag: "Failure", error: `err-${index}` },
  }))
}

const recordScript = (pairs: ReadonlyArray<CallPair>): ReadonlyArray<In> =>
  pairs.flatMap((pair): ReadonlyArray<In> => [
    { _tag: "Invoke", invocation: pair.invocation },
    { _tag: "Recorded", invocation: pair.invocation, outcome: pair.outcome },
  ])

const cleanRecord: St = {
  mode: "record",
  status: "active",
  history: [],
  cursor: 0,
  pending: undefined,
}

const runAll = (start: St, script: ReadonlyArray<In>) => {
  let state = start
  const results = []
  for (const input of script) {
    const out = reduce(state, input)
    state = out.state
    results.push(out.result)
  }
  return { state, results }
}

/** Run a perturbed script and observe the one rejection the sweep
 * expects: its category, its step index, the frozen history length,
 * and that every later step is absorbed. */
const observeRejection = (start: St, script: ReadonlyArray<In>) => {
  let state = start
  let rejection:
    | { readonly category: MismatchCategory; readonly step: number }
    | undefined
  let absorbedAfter = true
  for (let index = 0; index < script.length; index += 1) {
    const out = reduce(state, script[index] as In)
    state = out.state
    const result = out.result
    if (rejection === undefined) {
      if (result._tag === "Rejected") {
        rejection = { category: result.category, step: index }
      } else if (
        result._tag === "SessionOutcome" && result.outcome._tag === "Rejected"
      ) {
        rejection = { category: result.outcome.category, step: index }
      }
    } else if (result._tag !== "Absorbed") {
      absorbedAfter = false
    }
  }
  return { absorbedAfter, historyLength: state.history.length, rejection }
}

interface Perturbation {
  readonly name: string
  /** Build the twin. `j` indexes the pair the one edit lands on. */
  readonly twin: (pairs: ReadonlyArray<CallPair>, j: number) => ReadonlyArray<In>
  readonly category: MismatchCategory
  /** The step index the rejection must land on. */
  readonly step: (j: number) => number
  /** Pairs fully appended before the rejection freezes the history. */
  readonly frozenAt: (j: number) => number
}

const foreign: Invocation<string, string> =
  { op: "acme/Intruder/call", revision: 9, request: "req-x" }

const recordPerturbations: ReadonlyArray<Perturbation> = [
  {
    name: "interleaved invoke while one is outstanding",
    twin: (pairs, j) => {
      const script = [...recordScript(pairs)]
      script.splice(2 * j + 1, 0, { _tag: "Invoke", invocation: foreign })
      return script
    },
    category: "DelegationOutstanding",
    step: (j) => 2 * j + 1,
    frozenAt: (j) => j,
  },
  {
    name: "outcome whose invoke was dropped",
    twin: (pairs, j) => {
      const script = [...recordScript(pairs)]
      script.splice(2 * j, 1)
      return script
    },
    category: "UnsolicitedOutcome",
    step: (j) => 2 * j,
    frozenAt: (j) => j,
  },
  {
    name: "outcome cross-wired beside its outstanding invocation",
    twin: (pairs, j) => recordScript(pairs).map((input, index) =>
      index === 2 * j + 1 && input._tag === "Recorded"
        ? { ...input, invocation: { ...input.invocation, request: "req-wired" } }
        : input),
    category: "UnsolicitedOutcome",
    step: (j) => 2 * j + 1,
    frozenAt: (j) => j,
  },
  {
    name: "duplicated outcome after the pending slot cleared",
    twin: (pairs, j) => {
      const script = [...recordScript(pairs)]
      script.splice(2 * j + 2, 0, script[2 * j + 1] as In)
      return script
    },
    category: "UnsolicitedOutcome",
    step: (j) => 2 * j + 2,
    frozenAt: (j) => j + 1,
  },
  {
    name: "outcome reordered before its invoke",
    twin: (pairs, j) => {
      const script = [...recordScript(pairs)]
      const invoke = script[2 * j] as In
      script[2 * j] = script[2 * j + 1] as In
      script[2 * j + 1] = invoke
      return script
    },
    category: "UnsolicitedOutcome",
    step: (j) => 2 * j,
    frozenAt: (j) => j,
  },
]

it.effect("every generated lawful record script appends in invocation order", () =>
  Effect.sync(() => {
    for (let seed = 1; seed <= 64; seed += 1) {
      const pairs = generatePairs(splitmix32(seed))
      const { results, state } = runAll(cleanRecord, recordScript(pairs))
      expect({
        seed,
        history: state.history.map((entry) => ({
          op: entry.op,
          request: entry.request,
        })),
        cursor: state.cursor,
        status: state.status,
        pending: state.pending,
        results: results.map((result) => result._tag),
      }).toEqual({
        seed,
        history: pairs.map((pair) => ({
          op: pair.invocation.op,
          request: pair.invocation.request,
        })),
        cursor: pairs.length,
        status: "active",
        pending: undefined,
        results: pairs.flatMap(() => ["Delegated", "Appended"]),
      })
    }
  }))

it.effect("every one-edit unlawful record twin rejects exactly and freezes the history", () =>
  Effect.sync(() => {
    for (let seed = 1; seed <= 64; seed += 1) {
      const rng = splitmix32(seed)
      const pairs = generatePairs(rng)
      const j = Math.floor(rng() * pairs.length)
      for (const perturbation of recordPerturbations) {
        const observed = observeRejection(
          cleanRecord,
          perturbation.twin(pairs, j),
        )
        expect({ seed, name: perturbation.name, observed }).toEqual({
          seed,
          name: perturbation.name,
          observed: {
            absorbedAfter: true,
            historyLength: perturbation.frozenAt(j),
            rejection: {
              category: perturbation.category,
              step: perturbation.step(j),
            },
          },
        })
      }
    }
  }))

const replayStart = (history: ReadonlyArray<HistoryEntry>): St => ({
  mode: "replay",
  status: "active",
  history,
  cursor: 0,
  pending: undefined,
})

const replayScript = (pairs: ReadonlyArray<CallPair>): ReadonlyArray<In> => [
  ...pairs.map((pair): In => ({ _tag: "Invoke", invocation: pair.invocation })),
  { _tag: "Complete", terminal: { _tag: "Succeeded", value: "done" } },
]

const editInvocation = (
  script: ReadonlyArray<In>,
  j: number,
  edit: (invocation: Invocation<string, string>) => Invocation<string, string>,
): ReadonlyArray<In> => script.map((input, index) =>
  index === j && input._tag === "Invoke"
    ? { _tag: "Invoke", invocation: edit(input.invocation) }
    : input)

it.effect("every replayed script substitutes in order and every one-edit twin rejects by clause", () =>
  Effect.sync(() => {
    for (let seed = 1; seed <= 64; seed += 1) {
      const rng = splitmix32(seed)
      const pairs = generatePairs(rng)
      const recorded = runAll(cleanRecord, recordScript(pairs)).state.history
      const j = Math.floor(rng() * pairs.length)
      const lawful = replayScript(pairs)

      const green = runAll(replayStart(recorded), lawful)
      expect({
        seed,
        results: green.results.map((result) =>
          result._tag === "Substituted"
            ? { _tag: result._tag, outcome: result.outcome }
            : { _tag: result._tag }),
      }).toEqual({
        seed,
        results: [
          ...pairs.map((pair) => ({
            _tag: "Substituted",
            outcome: pair.outcome,
          })),
          { _tag: "SessionOutcome" },
        ],
      })

      const twins: ReadonlyArray<{
        readonly name: string
        readonly script: ReadonlyArray<In>
        readonly category: MismatchCategory
        readonly step: number
      }> = [
        {
          name: "operation swapped",
          script: editInvocation(lawful, j, (invocation) => ({
            ...invocation,
            op: "acme/Other/call",
          })),
          category: "OperationMismatch",
          step: j,
        },
        {
          name: "revision bumped",
          script: editInvocation(lawful, j, (invocation) => ({
            ...invocation,
            revision: invocation.revision + 1,
          })),
          category: "RevisionMismatch",
          step: j,
        },
        {
          name: "request mutated",
          script: editInvocation(lawful, j, (invocation) => ({
            ...invocation,
            request: `${invocation.request}-edited`,
          })),
          category: "RequestMismatch",
          step: j,
        },
        {
          name: "extra invoke past the history",
          script: [
            ...lawful.slice(0, -1),
            { _tag: "Invoke", invocation: foreign },
          ],
          category: "HistoryExhausted",
          step: pairs.length,
        },
        {
          name: "completion before the suffix is consumed",
          script: [...lawful.slice(0, -2), lawful[lawful.length - 1] as In],
          category: "UnconsumedSuffix",
          step: pairs.length - 1,
        },
      ]

      for (const twin of twins) {
        const observed = observeRejection(replayStart(recorded), twin.script)
        expect({ seed, name: twin.name, observed }).toEqual({
          seed,
          name: twin.name,
          observed: {
            absorbedAfter: true,
            historyLength: recorded.length,
            rejection: { category: twin.category, step: twin.step },
          },
        })
      }
    }
  }))
