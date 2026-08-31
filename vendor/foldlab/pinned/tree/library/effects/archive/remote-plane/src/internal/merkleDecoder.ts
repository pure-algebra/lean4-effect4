/**
 * Total sans-io verified-streaming decoder mirrored from
 * Effects/Merkle/Decoder.lean.
 */
import { Equal, Result } from "effect"
import type { Bytes } from "./merkleChunk.ts"
import { generateStream } from "./merkleGraph.ts"
import type { GenerateStreamInput, Range } from "./merkleGraph.ts"
import { pow2Below, type HP } from "./merkleTree.ts"

export type DInput<A> =
  | { readonly _tag: "ParentNode"; readonly left: A; readonly right: A }
  | { readonly _tag: "ChunkNode"; readonly bytes: Bytes }
  | { readonly _tag: "SkipNode" }

export interface Frame<A> {
  readonly expected: A
  readonly base: number
  readonly count: number
}

export type DStatus = "active" | "rejected" | "done"

export interface DState<A> {
  readonly stack: ReadonlyArray<Frame<A>>
  readonly status: DStatus
}

export interface DParams<A> {
  readonly P: HP<A>
  readonly total: number
  readonly expectedRoot: A
  readonly lo: number
  readonly hi: number
}

export type DDecision =
  | { readonly _tag: "Emitted"; readonly index: number; readonly bytes: Bytes }
  | { readonly _tag: "LengthValidated" }
  | { readonly _tag: "RejectedNode" }

export interface DStep<A> {
  readonly state: DState<A>
  readonly decisions: ReadonlyArray<DDecision>
}

export type DStepFunction<A> = (
  params: DParams<A>,
  state: DState<A>,
  input: DInput<A>,
) => DStep<A>

export interface DRun<A> {
  readonly state: DState<A>
  readonly decisions: ReadonlyArray<DDecision>
}

export const initState = <A>(params: DParams<A>): DState<A> => ({
  stack: [{ expected: params.expectedRoot, base: 0, count: params.total }],
  status: "active",
})

export const disjoint = <A>(params: DParams<A>, frame: Frame<A>): boolean =>
  frame.base + frame.count <= params.lo || params.hi <= frame.base

export const rejectOut = <A>(state: DState<A>): DStep<A> => ({
  state: { stack: state.stack, status: "rejected" },
  decisions: [{ _tag: "RejectedNode" }],
})

export const popped = <A>(rest: ReadonlyArray<Frame<A>>): DState<A> => ({
  stack: rest,
  status: rest.length === 0 ? "done" : "active",
})

/** One total decoder transition; branch order follows the Lean definition. */
export const dstep = <A>(
  params: DParams<A>,
  state: DState<A>,
  input: DInput<A>,
): DStep<A> => {
  if (state.status === "rejected" || state.status === "done") {
    return { state, decisions: [] }
  }

  if (state.stack.length === 0) return { state, decisions: [] }
  const frame = state.stack[0]!
  const rest = state.stack.slice(1)

  if (disjoint(params, frame)) {
    return input._tag === "SkipNode"
      ? { state: popped(rest), decisions: [] }
      : rejectOut(state)
  }

  if (frame.count <= 1) {
    if (input._tag !== "ChunkNode") return rejectOut(state)
    const actual = params.P.H({
      _tag: "Leaf",
      index: frame.base,
      bytes: input.bytes,
    })
    if (!Equal.equals(actual, frame.expected)) return rejectOut(state)
    return {
      state: popped(rest),
      decisions: frame.base + 1 === params.total
        ? [
          { _tag: "Emitted", index: frame.base, bytes: input.bytes },
          { _tag: "LengthValidated" },
        ]
        : [{ _tag: "Emitted", index: frame.base, bytes: input.bytes }],
    }
  }

  if (input._tag !== "ParentNode") return rejectOut(state)
  const actual = params.P.H({
    _tag: "Parent",
    left: input.left,
    right: input.right,
  })
  if (!Equal.equals(actual, frame.expected)) return rejectOut(state)

  const split = pow2Below(frame.count)
  return {
    state: {
      stack: [
        { expected: input.left, base: frame.base, count: split },
        {
          expected: input.right,
          base: frame.base + split,
          count: frame.count - split,
        },
        ...rest,
      ],
      status: "active",
    },
    decisions: [],
  }
}

/** Run a parsed input list and collect decisions in input order. */
export const drun = <A>(
  params: DParams<A>,
  state: DState<A>,
  inputs: ReadonlyArray<DInput<A>>,
): DRun<A> => {
  let current = state
  const decisions: Array<DDecision> = []
  for (const input of inputs) {
    const output = dstep(params, current, input)
    current = output.state
    decisions.push(...output.decisions)
  }
  return { state: current, decisions }
}

/** Model-side pre-order stream generator, including range skip tokens. */
export type GenStreamInput<A> = GenerateStreamInput<A>

export const genStream = <A>(input: GenStreamInput<A>): ReadonlyArray<DInput<A>> => {
  return Result.getOrThrow(generateStream(input))
}

export interface RangedEmissionsInput {
  readonly range: Range
  readonly base: number
  readonly chunks: ReadonlyArray<Bytes>
}

export const rangedEmissions = ({
  range,
  base,
  chunks,
}: RangedEmissionsInput): ReadonlyArray<readonly [index: number, bytes: Bytes]> => {
  if (base + chunks.length <= range.lo || range.hi <= base) return []
  if (chunks.length <= 1) {
    return [[base, chunks.length === 0 ? [] : chunks[0]!]]
  }
  const split = pow2Below(chunks.length)
  return [
    ...rangedEmissions({ range, base, chunks: chunks.slice(0, split) }),
    ...rangedEmissions({
      range,
      base: base + split,
      chunks: chunks.slice(split),
    }),
  ]
}
