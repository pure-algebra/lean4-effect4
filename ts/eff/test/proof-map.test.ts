// Synthetic graph controls: shape/joins only, never a receipt of Lean proof evidence.
import { describe, expect, test } from "bun:test"
import { Schema } from "effect"
import { ProofMap } from "../proof-map.ts"
import { decodeSemanticsReport } from "../semantics.ts"
import fixture from "./semantics.fixture.json"

const report = decodeSemanticsReport(fixture)
const proved = report.claims[0]!.status
const wanted = report.claims[1]!.status
const refuted = report.claims[2]!.status
if (proved._tag !== "proved" || wanted._tag !== "wanted" || refuted._tag !== "refuted")
  throw new Error("Unexpected pinned fixture statuses")

const definition = (id: string) => ({
  id, title: id, kind: "definition", status: "defined", module: "Fixture", path: "Fixture.lean", line: 0,
  levels: [], evidence: null, statement: "ProgramSource → Prop", body: "fun root => ∀ w, Fits w → Typed root w",
  premises: [], axioms: [], claims: [], omittedReferences: 2,
})
const seq = {
  id: proved.witness.name, title: "Synthetic proved compatibility", kind: "theorem", status: "proved",
  module: proved.witness.module, path: "Fixture.lean", line: 1, levels: proved.witness.levels,
  evidence: proved.witness.name, statement: proved.witness.statement, body: null,
  premises: [], axioms: proved.witness.axioms, claims: [report.claims[0]!.id], omittedReferences: 3,
}
const goal = {
  id: wanted.goal.name, title: "Synthetic wanted denotation", kind: "goal", status: "wanted",
  module: wanted.goal.module, path: "Fixture.lean", line: 0, levels: wanted.goal.levels,
  evidence: wanted.placeholder, statement: wanted.goal.statement, body: null,
  premises: [], axioms: wanted.goal.axioms, claims: [report.claims[1]!.id], omittedReferences: 0,
}
const conditional = {
  ...seq, id: "Fixture.conditional", title: "A proved conditional is still conditional",
  evidence: "Fixture.conditional", statement: "ProvideLayerArm root → DenotesTyped root",
  claims: [], premises: [{ name: "hlayer", statement: "ProvideLayerArm root" }],
}
const prerequisite = {
  ...goal, id: "Fixture.prerequisite", evidence: "Fixture.prerequisite.wanted", claims: [],
}
const feature = (id: string) => ({
  id, title: id, concepts: [report.concepts[0]!.id], syntax: [], judgments: [], rules: [], requires: [],
  boundary: "Synthetic selected fragment; no host or compiler claim.",
})
const graph = Schema.decodeUnknownSync(ProofMap, { onExcessProperty: "error" })({
  scope: "Synthetic selected direct-reference graph, not a complete census or proof receipt.",
  literature: [{ work: "Ballarin", locator: "§§3.2–3.5, pp37–41", use: "Retain assumptions" }],
  features: [
    { ...feature("syntax"), syntax: ["Fixture.Eff"] },
    { ...feature("typing"), judgments: ["Fixture.Typed"], rules: [seq.id, goal.id, conditional.id], requires: ["syntax"] },
  ],
  nodes: [definition("Fixture.Eff"), definition("Fixture.Typed"), seq, goal, conditional, prerequisite],
  edges: [
    { from: "Fixture.Eff", to: "Fixture.Typed", kind: "definition-reference" },
    { from: "Fixture.Typed", to: seq.id, kind: "statement-reference" },
    { from: seq.id, to: conditional.id, kind: "proof-reference" },
    { from: prerequisite.id, to: goal.id, kind: "ledger-prerequisite" },
  ],
  work: [{ id: "prove-layer", title: "Proposed layer proof", features: ["typing"], after: [goal.id],
    source: "contract.md", reason: "Close the layer premise; this work item is not a theorem." }],
})
const value = (map: unknown = graph) => ({ ...fixture, proofMap: map })
const nodes = (change: (node: typeof graph.nodes[number]) => unknown) => ({ ...graph, nodes: graph.nodes.map(change) })
const rejects = (name: string, make: () => unknown, reason?: string) => test(name, () => {
  const decode = () => decodeSemanticsReport(make())
  if (reason) expect(decode).toThrow(reason)
  else expect(decode).toThrow()
})

describe("selected proof and feature graph", () => {
  test("accepts the meaningful graph with all four distinct edge kinds", () => {
    const decoded = decodeSemanticsReport(value())
    expect(decoded.proofMap.edges.map((edge) => edge.kind)).toEqual([
      "definition-reference", "statement-reference", "proof-reference", "ledger-prerequisite",
    ])
  })
  test("preserves the proved conditional's premise and definition's nested conditions", () => {
    const decoded = decodeSemanticsReport(value())
    const node = decoded.proofMap.nodes.find((node) => node.id === conditional.id)!
    expect(node.status).toBe("proved")
    expect(node.premises).toEqual([{ name: "hlayer", statement: "ProvideLayerArm root" }])
    expect(decoded.proofMap.nodes[1]!.body).toContain("∀ w")
  })
  test("wanted stays wanted when its ledger prerequisite is proved", () => {
    const decoded = decodeSemanticsReport(value(nodes((node) => node.id === prerequisite.id
      ? { ...node, status: "proved", evidence: `${node.id}.checked` } : node)))
    expect(decoded.proofMap.nodes.find((node) => node.id === goal.id)!.status).toBe("wanted")
    expect(decoded.claims[1]!.status._tag).toBe("wanted")
    expect(decoded.concepts[0]!.counts.proved).toBe(1)
  })
  test("accepts an unassociated proved goal with its checked witness", () => {
    expect(() => decodeSemanticsReport(value(nodes((node) => node.id === prerequisite.id
      ? { ...node, status: "proved", evidence: `${node.id}.checked` } : node)))).not.toThrow()
  })
  rejects("refuses a wanted placeholder as evidence for an unassociated proved goal", () =>
    value(nodes((node) => node.id === prerequisite.id ? { ...node, status: "proved" } : node)),
    "proved goal evidence must name its checked witness")
  test("a refuted claim still points to a proved refutation theorem", () => {
    const witness = refuted.counterexample.witness!
    const node = { ...seq, id: witness.name, evidence: witness.name, module: witness.module,
      levels: witness.levels, statement: witness.statement, axioms: witness.axioms, claims: [report.claims[2]!.id] }
    expect(() => decodeSemanticsReport(value({ ...graph, nodes: [...graph.nodes, node] }))).not.toThrow()
  })
  test("compares a proved goal statement with its marker and axioms with its checked witness", () => {
    const declaration = { ...proved.witness, name: "Fixture.provedGoal" }
    const witness = { ...proved.witness, name: "Fixture.provedGoal.checked", axioms: ["propext"] }
    const input = {
      ...fixture, claims: fixture.claims.map((claim, index) => index === 0
        ? { ...claim, status: { _tag: "proved", by: "ledger", goal: declaration, witness } } : claim),
      proofMap: { ...graph, nodes: [
        ...graph.nodes.filter((node) => node.id !== seq.id).map((node) => ({ ...node, claims: [] })),
        { ...seq, id: declaration.name, kind: "goal", evidence: witness.name, axioms: witness.axioms, claims: [report.claims[0]!.id] },
      ], edges: graph.edges.filter((edge) => edge.from !== seq.id && edge.to !== seq.id),
        features: graph.features.map((feature) => ({ ...feature, rules: feature.rules.filter((id) => id !== seq.id) })) },
    }
    expect(() => decodeSemanticsReport(input)).not.toThrow()
    expect(() => decodeSemanticsReport({ ...input, proofMap: {
      ...input.proofMap, nodes: input.proofMap.nodes.map((node) => node.id === declaration.name
        ? { ...node, axioms: declaration.axioms } : node),
    } })).toThrow("disagrees with claim")
  })
  test("does not confuse a wanted marker's axioms with its placeholder's axioms", () => {
    expect(() => decodeSemanticsReport({ ...value(), claims: fixture.claims.map((claim, index) => index === 1
      ? { ...claim, status: { ...wanted, goal: { ...wanted.goal, axioms: ["propext"] } } } : claim),
    })).not.toThrow()
  })

  rejects("requires proofMap", () => fixture.schemaVersion === 2 ? (() => {
    const { proofMap, ...rest } = fixture
    return rest
  })() : {})
  rejects("refuses report version one", () => ({ ...value(), schemaVersion: 1 }))
  rejects("refuses blank scope", () => value({ ...graph, scope: " \n" }))
  rejects("refuses missing body", () => value(nodes((node) => {
    const { body, ...rest } = node
    return rest
  })))
  rejects("refuses theorem proof text in body", () => value(nodes((node) => node.id === conditional.id
    ? { ...node, body: "proof text" } : node)), "non-definition body")
  test("accepts a constructor/inductive definition without a value", () => {
    expect(() => decodeSemanticsReport(value(nodes((node) => node.id === "Fixture.Eff"
      ? { ...node, body: null } : node)))).not.toThrow()
  })
  for (const [name, map] of [
    ["map", { ...graph, extra: true }],
    ["literature", { ...graph, literature: [{ ...graph.literature[0], extra: true }] }],
    ["feature", { ...graph, features: [{ ...graph.features[0], extra: true }] }],
    ["node", nodes((node) => ({ ...node, extra: true }))],
    ["premise", nodes((node) => ({ ...node, premises: [{ name: "h", statement: "P", extra: true }] }))],
    ["edge", { ...graph, edges: [{ ...graph.edges[0], extra: true }] }],
    ["work", { ...graph, work: [{ ...graph.work[0], extra: true }] }],
  ] as const) rejects(`refuses excess keys in ${name}`, () => value(map))

  rejects("refuses duplicate features", () => value({ ...graph, features: [...graph.features, graph.features[0]] }), "duplicate")
  rejects("refuses duplicate nodes", () => value({ ...graph, nodes: [...graph.nodes, graph.nodes[0]] }), "duplicate")
  rejects("refuses duplicate work", () => value({ ...graph, work: [...graph.work, graph.work[0]] }), "duplicate")
  rejects("refuses duplicate edges", () => value({ ...graph, edges: [...graph.edges, graph.edges[0]] }), "duplicate")
  rejects("refuses duplicate claim links", () => value(nodes((node) => node.id === seq.id
    ? { ...node, claims: [report.claims[0]!.id, report.claims[0]!.id] } : node)), "duplicate")
  rejects("refuses unknown concept", () => value({ ...graph, features: [{ ...feature("x"), concepts: ["unknown"] }] }), "unknown reference")
  for (const field of ["syntax", "judgments", "rules", "requires"] as const)
    rejects(`refuses dangling feature ${field}`, () => value({ ...graph, features: graph.features.map((feature, index) => index === 0
      ? { ...feature, [field]: ["Unknown"] } : feature) }), "unknown reference")
  rejects("refuses unknown claim", () => value(nodes((node) => ({ ...node, claims: ["unknown"] }))), "unknown reference")
  rejects("refuses wrong claim association", () => value(nodes((node) => node.id === conditional.id
    ? { ...node, claims: [report.claims[0]!.id] } : node)), "not an evidence pointer")
  for (const endpoint of ["from", "to"] as const)
    rejects(`refuses dangling edge ${endpoint}`, () => value({ ...graph, edges: [{ ...graph.edges[0], [endpoint]: "Unknown" }] }), "unknown node")
  rejects("refuses unknown edge kind", () => value({ ...graph, edges: [{ ...graph.edges[0], kind: "imports" }] }))
  rejects("refuses unknown work feature", () => value({ ...graph, work: [{ ...graph.work[0], features: ["unknown"] }] }), "unknown reference")
  rejects("refuses unknown work prerequisite", () => value({ ...graph, work: [{ ...graph.work[0], after: ["unknown"] }] }), "unknown reference")
  rejects("refuses work/node id collision", () => value({ ...graph, work: [{ ...graph.work[0], id: seq.id }] }), "collides")
  rejects("refuses feature dependency cycle", () => value({ ...graph, features: graph.features.map((feature, index) => index === 0
    ? { ...feature, requires: ["typing"] } : feature) }), "dependency cycle")
  rejects("refuses work dependency cycle", () => value({ ...graph, work: [
    { ...graph.work[0], id: "first", after: ["second"] }, { ...graph.work[0], id: "second", after: ["first"] },
  ] }), "dependency cycle")
  rejects("refuses ledger dependency cycle", () => value({ ...graph, edges: [
    ...graph.edges, { from: goal.id, to: prerequisite.id, kind: "ledger-prerequisite" },
  ] }), "dependency cycle")
  rejects("refuses ledger prerequisites between non-goals", () => value({ ...graph, edges: [
    { from: seq.id, to: goal.id, kind: "ledger-prerequisite" },
  ] }), "must connect goals")
  rejects("refuses proof-reference into an unproved goal", () => value({ ...graph, edges: [
    { from: seq.id, to: goal.id, kind: "proof-reference" },
  ] }), "consumer must be proved")
  rejects("refuses definition-reference into a theorem", () => value({ ...graph, edges: [
    { from: "Fixture.Eff", to: seq.id, kind: "definition-reference" },
  ] }), "must be a definition")
  rejects("refuses definition as proved evidence", () => value(nodes((node) => node.kind === "definition"
    ? { ...node, status: "proved" } : node)), "defined status")
  rejects("refuses theorem as wanted", () => value(nodes((node) => node.id === conditional.id
    ? { ...node, status: "wanted", evidence: `${node.id}.wanted` } : node)), "kind/status")
  rejects("refuses theorem evidence naming another declaration", () => value(nodes((node) => node.id === conditional.id
    ? { ...node, evidence: seq.id } : node)), "name itself")
  rejects("refuses wrong wanted placeholder", () => value(nodes((node) => node.id === goal.id
    ? { ...node, evidence: "Other.wanted" } : node)), "placeholder")
  rejects("refuses missing proof evidence", () => value(nodes((node) => node.id === conditional.id
    ? { ...node, evidence: null } : node)), "requires evidence")
  rejects("refuses proof axioms outside ceiling", () => value(nodes((node) => node.id === conditional.id
    ? { ...node, axioms: ["Classical.choice"] } : node)), "axiom ceiling")
  rejects("refuses graph success contradicting a wanted claim", () => value(nodes((node) => node.id === goal.id
    ? { ...node, status: "proved", evidence: `${node.id}.checked` } : node)), "disagrees with claim")
  for (const [field, changed] of [["statement", "different"], ["module", "Other"], ["levels", ["u"]], ["axioms", ["propext"]]] as const)
    rejects(`refuses overlapping claim ${field} drift even without authored claim links`, () => value(nodes((node) => node.id === seq.id
      ? { ...node, [field]: changed, claims: [] } : node)), "disagrees with claim")
  rejects("refuses negative source line", () => value(nodes((node) => ({ ...node, line: -1 }))))
  rejects("refuses fractional omitted reference count", () => value(nodes((node) => ({ ...node, omittedReferences: 0.5 }))))
  rejects("refuses blank premise", () => value(nodes((node) => ({ ...node, premises: [{ name: "h", statement: " " }] }))))
  rejects("refuses an invented feature status", () => value({ ...graph, features: [{ ...graph.features[0], status: "proved" }] }))
})
