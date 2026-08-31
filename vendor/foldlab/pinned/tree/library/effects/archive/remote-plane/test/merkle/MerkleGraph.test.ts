import { expect, it } from "@effect/vitest"
import { Effect, Equal, Graph, Hash, Option, Ref, Result, Schema } from "effect"
import * as MerkleGraph from "../../src/internal/merkleGraph.ts"
import { genStream, rangedEmissions } from "../../src/internal/merkleDecoder.ts"
import { genPath, type Pre } from "../../src/internal/merkleTree.ts"
import { loadFamily } from "../conformance/harness.ts"
import {
  merkleH,
  mrk001Binding,
  mrk005Binding,
  mrk006Binding,
  mrk007Binding,
  type MerkleAddress,
} from "./MerkleFixtures.ts"

const RatifiedThreeLeafRoot = [
  36, 198, 104, 10, 172, 78, 240, 146,
  52, 214, 120, 26, 188, 94, 0, 162,
  68, 230, 136, 42, 204, 110, 16, 178,
  84, 246, 152, 58, 220, 126, 32, 194,
] as const

const Byte = Schema.Int.check(Schema.isBetween({ minimum: 0, maximum: 0xff }))
const Chunk = Schema.Array(Byte).check(Schema.isLengthBetween(0, 16))
const Chunks = Schema.Array(Chunk).check(Schema.isLengthBetween(0, 16))

it.effect("a native Graph-backed tree evaluates the ratified ragged root", () =>
  Effect.gen(function* () {
    const manifest = yield* loadFamily(mrk001Binding)
    const row = manifest.rows.find(({ case: name }) => name === "ragged-tail-002")
    if (row === undefined) return yield* Effect.die("MRK-001 has no ragged-tail-002 row")

    const tree = MerkleGraph.fromChunks(0, row.expect.chunks)
    const evaluated = MerkleGraph.evaluate(tree, merkleH)

    expect(Result.isSuccess(evaluated)).toBe(true)
    if (Result.isSuccess(evaluated)) {
      expect(evaluated.success).toEqual(row.expect.root)
    }
  }))

it.effect("effectful evaluation hashes each node once after its children", () =>
  Effect.gen(function* () {
    const tree = MerkleGraph.fromChunks(0, [[1], [2], [3]])
    const seen = yield* Ref.make<ReadonlySet<string>>(new Set())
    const calls = yield* Ref.make(0)

    const root = yield* MerkleGraph.evaluateEffect(tree, (preimage: Pre<MerkleAddress>) =>
      Effect.gen(function* () {
        if (preimage._tag === "Parent") {
          const completed = yield* Ref.get(seen)
          if (!completed.has(preimage.left.join(","))
            || !completed.has(preimage.right.join(","))) {
            return yield* Effect.die("parent digest ran before a child digest")
          }
        }
        const digest = merkleH.H(preimage)
        yield* Ref.update(seen, (completed) => new Set(completed).add(digest.join(",")))
        yield* Ref.update(calls, (count) => count + 1)
        return digest
      }))

    expect(root).toEqual(RatifiedThreeLeafRoot)
    expect(yield* Ref.get(calls)).toBe(5)
  }))

it.effect.prop(
  "Graph NodeIndex allocation never participates in a Merkle root",
  [Schema.Int.check(Schema.isBetween({ minimum: 0, maximum: 32 }))],
  ([padding]) => Effect.sync(() => {
    const offset = padding * 11
    const leaf2 = offset + 2
    const root = offset + 5
    const leaf0 = offset + 11
    const left = offset + 18
    const leaf1 = offset + 26
    const graph = Graph.fromSnapshot<MerkleGraph.Node, MerkleGraph.Branch, "directed">({
      type: "directed",
      nodes: [
        { index: leaf2, data: MerkleGraph.Node.Leaf({ index: 2, bytes: [3] }) },
        { index: root, data: MerkleGraph.Node.Parent() },
        { index: leaf0, data: MerkleGraph.Node.Leaf({ index: 0, bytes: [1] }) },
        { index: left, data: MerkleGraph.Node.Parent() },
        { index: leaf1, data: MerkleGraph.Node.Leaf({ index: 1, bytes: [2] }) },
      ],
      edges: [
        { index: offset + 3, source: left, target: leaf0, data: MerkleGraph.Branch.Left() },
        { index: offset + 7, source: left, target: leaf1, data: MerkleGraph.Branch.Right() },
        { index: offset + 12, source: root, target: left, data: MerkleGraph.Branch.Left() },
        { index: offset + 19, source: root, target: leaf2, data: MerkleGraph.Branch.Right() },
      ],
    })

    const result = MerkleGraph.evaluate({
      graph,
      root,
    }, merkleH)
    expect(Result.isSuccess(result)).toBe(true)
    if (Result.isSuccess(result)) expect(result.success).toEqual(RatifiedThreeLeafRoot)
  }),
  { fastCheck: { numRuns: 64 } },
)

it.effect.prop(
  "arbitrary chunk roots are invariant under non-contiguous graph reindexing",
  [Chunks, Schema.Int.check(Schema.isBetween({ minimum: 1, maximum: 64 }))],
  ([chunks, padding]) => Effect.sync(() => {
    const tree = MerkleGraph.fromChunks(7, chunks)
    const expected = MerkleGraph.evaluate(tree, merkleH)
    expect(Result.isSuccess(expected)).toBe(true)
    if (Result.isFailure(expected)) return

    const shift = 257 + padding * 37
    const snapshot = Graph.toSnapshot(tree.graph)
    const shifted = Graph.fromSnapshot<MerkleGraph.Node, MerkleGraph.Branch, "directed">({
      type: "directed",
      nodes: snapshot.nodes.map((node) => ({
        index: node.index + shift,
        data: node.data,
      })),
      edges: snapshot.edges.map((edge) => ({
        index: edge.index + shift * 3,
        source: edge.source + shift,
        target: edge.target + shift,
        data: edge.data,
      })),
    })
    const actual = MerkleGraph.evaluate({ graph: shifted, root: tree.root + shift }, merkleH)
    expect(Result.isSuccess(actual)).toBe(true)
    if (Result.isSuccess(actual)) expect(actual.success).toEqual(expected.success)
  }),
  { fastCheck: { numRuns: 128 } },
)

it("commitment nodes use Effect structural equality and hashing", () => {
  const left = MerkleGraph.Node.Commitment({ value: RatifiedThreeLeafRoot })
  const right = MerkleGraph.Node.Commitment({ value: [...RatifiedThreeLeafRoot] })
  expect(Equal.equals(left, right)).toBe(true)
  expect(Hash.hash(left)).toBe(Hash.hash(right))
})

it("rejects a leaf that carries graph children with a typed error", () => {
  const mutable = Graph.beginMutation(
    Graph.directed<MerkleGraph.Node, MerkleGraph.Branch>(),
  )
  const leaf = Graph.addNode(mutable, MerkleGraph.Node.Leaf({ index: 0, bytes: [1] }))
  const child = Graph.addNode(mutable, MerkleGraph.Node.Leaf({ index: 1, bytes: [2] }))
  Graph.addEdge(mutable, leaf, child, MerkleGraph.Branch.Left())

  const result = MerkleGraph.evaluate({
    graph: Graph.endMutation(mutable),
    root: leaf,
  }, merkleH)

  expect(Result.isFailure(result)).toBe(true)
  if (Result.isFailure(result)) {
    expect(result.failure).toEqual(new MerkleGraph.MerkleGraphError({
      node: leaf,
      reason: "leaf must not have children",
    }))
  }
})

it("rejects a cycle before attempting Merkle evaluation", () => {
  const mutable = Graph.beginMutation(
    Graph.directed<MerkleGraph.Node, MerkleGraph.Branch>(),
  )
  const parent = Graph.addNode(mutable, MerkleGraph.Node.Parent())
  const leaf = Graph.addNode(mutable, MerkleGraph.Node.Leaf({ index: 0, bytes: [1] }))
  Graph.addEdge(mutable, parent, parent, MerkleGraph.Branch.Left())
  Graph.addEdge(mutable, parent, leaf, MerkleGraph.Branch.Right())

  const result = MerkleGraph.evaluate({
    graph: Graph.endMutation(mutable),
    root: parent,
  }, merkleH)

  expect(Result.isFailure(result)).toBe(true)
  if (Result.isFailure(result)) {
    expect(result.failure).toEqual(new MerkleGraph.MerkleGraphError({
      node: parent,
      reason: "tree must be acyclic",
    }))
  }
})

it("rejects a shared descendant that would make the topology a DAG", () => {
  const mutable = Graph.beginMutation(
    Graph.directed<MerkleGraph.Node, MerkleGraph.Branch>(),
  )
  const root = Graph.addNode(mutable, MerkleGraph.Node.Parent())
  const leftParent = Graph.addNode(mutable, MerkleGraph.Node.Parent())
  const rightParent = Graph.addNode(mutable, MerkleGraph.Node.Parent())
  const shared = Graph.addNode(mutable, MerkleGraph.Node.Leaf({ index: 1, bytes: [2] }))
  const farLeft = Graph.addNode(mutable, MerkleGraph.Node.Leaf({ index: 0, bytes: [1] }))
  const farRight = Graph.addNode(mutable, MerkleGraph.Node.Leaf({ index: 2, bytes: [3] }))
  Graph.addEdge(mutable, root, leftParent, MerkleGraph.Branch.Left())
  Graph.addEdge(mutable, root, rightParent, MerkleGraph.Branch.Right())
  Graph.addEdge(mutable, leftParent, farLeft, MerkleGraph.Branch.Left())
  Graph.addEdge(mutable, leftParent, shared, MerkleGraph.Branch.Right())
  Graph.addEdge(mutable, rightParent, shared, MerkleGraph.Branch.Left())
  Graph.addEdge(mutable, rightParent, farRight, MerkleGraph.Branch.Right())

  const result = MerkleGraph.evaluate({
    graph: Graph.endMutation(mutable),
    root,
  }, merkleH)

  expect(Result.isFailure(result)).toBe(true)
  if (Result.isFailure(result)) {
    expect(result.failure).toEqual(new MerkleGraph.MerkleGraphError({
      node: shared,
      reason: "non-root tree nodes must have exactly one parent",
    }))
  }
})

it("rejects topology outside the selected Merkle root", () => {
  const mutable = Graph.beginMutation(
    Graph.directed<MerkleGraph.Node, MerkleGraph.Branch>(),
  )
  const root = Graph.addNode(mutable, MerkleGraph.Node.Leaf({ index: 0, bytes: [1] }))
  const unreachable = Graph.addNode(
    mutable,
    MerkleGraph.Node.Leaf({ index: 99, bytes: [99] }),
  )

  const result = MerkleGraph.evaluate({
    graph: Graph.endMutation(mutable),
    root,
  }, merkleH)

  expect(Result.isFailure(result)).toBe(true)
  if (Result.isFailure(result)) {
    expect(result.failure).toEqual(new MerkleGraph.MerkleGraphError({
      node: unreachable,
      reason: "tree must not contain unreachable nodes",
    }))
  }
})

it.effect("validates all topology before running an effectful digest", () =>
  Effect.gen(function* () {
    const mutable = Graph.beginMutation(
      Graph.directed<MerkleGraph.Node, MerkleGraph.Branch>(),
    )
    const parent = Graph.addNode(mutable, MerkleGraph.Node.Parent())
    const left = Graph.addNode(mutable, MerkleGraph.Node.Leaf({ index: 0, bytes: [1] }))
    const right = Graph.addNode(mutable, MerkleGraph.Node.Leaf({ index: 1, bytes: [2] }))
    Graph.addEdge(mutable, parent, left, MerkleGraph.Branch.Left())
    Graph.addEdge(mutable, parent, right, MerkleGraph.Branch.Left())
    const calls = yield* Ref.make(0)

    const failure = yield* MerkleGraph.evaluateEffect({
      graph: Graph.endMutation(mutable),
      root: parent,
    }, (preimage: Pre<MerkleAddress>) => Ref.update(calls, (count) => count + 1).pipe(
      Effect.as(merkleH.H(preimage)),
    )).pipe(Effect.flip)

    expect(failure).toEqual(new MerkleGraph.MerkleGraphError({
      node: parent,
      reason: "parent must have one distinct left and right child",
    }))
    expect(yield* Ref.get(calls)).toBe(0)
  }))

it.effect("an opening exposes the ratified root-side-first sibling path", () =>
  Effect.gen(function* () {
    const manifest = yield* loadFamily(mrk006Binding)
    const row = manifest.rows.find(({ case: name }) => name === "honest-opening-accepted-000")
    if (row === undefined) return yield* Effect.die("MRK-006 has no honest opening row")

    const tree = MerkleGraph.fromChunks(0, [[1], [2], [3]])
    let digestCalls = 0
    const opened = MerkleGraph.opening(tree, {
      H: (preimage: Pre<MerkleAddress>) => {
        digestCalls += 1
        return merkleH.H(preimage)
      },
    }, row.input.index)

    expect(Result.isSuccess(opened)).toBe(true)
    if (Result.isSuccess(opened)) {
      expect(opened.success).toEqual({
        index: row.input.index,
        count: row.input.count,
        leaf: row.input.bytes,
        siblings: row.input.siblings,
        root: row.input.root,
      })
    }
    expect(genPath({
      P: merkleH,
      base: 0,
      index: row.input.index,
      chunks: [[1], [2], [3]],
    })).toEqual(row.input.siblings)
    expect(digestCalls).toBe(5)
  }))

it.effect("reconstructs an inclusion root through committed graph nodes", () =>
  Effect.gen(function* () {
    const manifest = yield* loadFamily(mrk006Binding)
    const honest = manifest.rows.find(({ case: name }) => name === "honest-opening-accepted-000")
    const short = manifest.rows.find(({ case: name }) => name === "short-path-rejected-002")
    if (honest === undefined || short === undefined) {
      return yield* Effect.die("MRK-006 is missing inclusion reconstruction rows")
    }

    const rebuilt = MerkleGraph.rebuildInclusion({
      P: merkleH,
      base: 0,
      index: honest.input.index,
      count: honest.input.count,
      bytes: honest.input.bytes,
      siblings: honest.input.siblings,
    })
    expect(Option.isSome(rebuilt)).toBe(true)
    if (Option.isSome(rebuilt)) expect(rebuilt.value).toEqual(honest.input.root)

    expect(Option.isNone(MerkleGraph.rebuildInclusion({
      P: merkleH,
      base: 0,
      index: short.input.index,
      count: short.input.count,
      bytes: short.input.bytes,
      siblings: short.input.siblings,
    }))).toBe(true)
  }))

it.effect("reconstructs both consistency roots through one native graph", () =>
  Effect.gen(function* () {
    const manifest = yield* loadFamily(mrk007Binding)
    const honest = manifest.rows.find(({ case: name }) => name === "honest-3-of-5-accepted-001")
    const trailing = manifest.rows.find(({ case: name }) => name === "trailing-element-rejected-004")
    if (honest === undefined || trailing === undefined) {
      return yield* Effect.die("MRK-007 is missing consistency reconstruction rows")
    }

    const rebuilt = MerkleGraph.rebuildConsistency({
      P: merkleH,
      oldAnchor: honest.input.oldRoot,
      oldSize: honest.input.oldSize,
      newSize: honest.input.newSize,
      anchored: true,
      proof: honest.input.proof,
    })
    expect(Option.isSome(rebuilt)).toBe(true)
    if (Option.isSome(rebuilt)) {
      expect(rebuilt.value).toEqual([honest.input.oldRoot, honest.input.newRoot])
    }

    expect(Option.isNone(MerkleGraph.rebuildConsistency({
      P: merkleH,
      oldAnchor: trailing.input.oldRoot,
      oldSize: trailing.input.oldSize,
      newSize: trailing.input.newSize,
      anchored: true,
      proof: trailing.input.proof,
    }))).toBe(true)
  }))

it.effect("generates the ratified range stream from graph topology", () =>
  Effect.gen(function* () {
    const manifest = yield* loadFamily(mrk005Binding)
    const row = manifest.rows.find(({ case: name }) => name === "slice-middle-chunk-000")
    if (row === undefined) return yield* Effect.die("MRK-005 has no middle-slice row")

    let digestCalls = 0
    const generated = MerkleGraph.generateStream({
      P: {
        H: (preimage: Pre<MerkleAddress>) => {
          digestCalls += 1
          return merkleH.H(preimage)
        },
      },
      range: { lo: row.input.lo, hi: row.input.hi },
      base: 0,
      chunks: [[1], [2], [3]],
    })
    expect(Result.isSuccess(generated)).toBe(true)
    if (Result.isSuccess(generated)) expect(generated.success).toEqual(row.input.inputs)
    expect(digestCalls).toBe(4)
    expect(genStream({
      P: merkleH,
      range: { lo: row.input.lo, hi: row.input.hi },
      base: 0,
      chunks: [[1], [2], [3]],
    })).toEqual(row.input.inputs)
    expect(rangedEmissions({
      range: { lo: row.input.lo, hi: row.input.hi },
      base: 0,
      chunks: [[1], [2], [3]],
    })).toEqual([[1, [2]]])
  }))
