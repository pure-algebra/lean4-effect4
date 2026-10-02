// Selected declaration references and authored feature/work dependencies, not a new proof authority.
import { Schema } from "effect"
import type { Claim, Declaration } from "./semantics.ts"

const Text = Schema.String.check(Schema.isPattern(/\S/))
const LeanName = Schema.String.check(Schema.isPattern(/^\S+$/))
const Count = Schema.Int.check(Schema.isGreaterThanOrEqualTo(0))

export const ProofMapNode = Schema.Struct({
  id: LeanName, title: Text,
  kind: Schema.Literals(["theorem", "definition", "goal"]),
  status: Schema.Literals(["proved", "wanted", "defined"]),
  module: LeanName, path: Text, line: Count,
  levels: Schema.Array(LeanName), evidence: Schema.NullOr(LeanName), statement: Text, body: Schema.NullOr(Text),
  premises: Schema.Array(Schema.Struct({ name: Text, statement: Text })),
  axioms: Schema.Array(LeanName), claims: Schema.Array(Text), omittedReferences: Count,
})

export const ProofMap = Schema.Struct({
  scope: Text,
  literature: Schema.Array(Schema.Struct({ work: Text, locator: Text, use: Text })),
  features: Schema.Array(Schema.Struct({
    id: Text, title: Text, concepts: Schema.Array(Text), syntax: Schema.Array(LeanName),
    judgments: Schema.Array(LeanName), rules: Schema.Array(LeanName),
    requires: Schema.Array(Text), boundary: Text,
  })),
  nodes: Schema.Array(ProofMapNode),
  edges: Schema.Array(Schema.Struct({
    from: LeanName, to: LeanName,
    kind: Schema.Literals(["proof-reference", "definition-reference", "statement-reference", "ledger-prerequisite"]),
  })),
  work: Schema.Array(Schema.Struct({
    id: Text, title: Text, features: Schema.Array(Text), after: Schema.Array(Text), source: Text, reason: Text,
  })),
})

export type ProofMap = typeof ProofMap.Type

type ClaimRecord = typeof Claim.Type
type DeclarationRecord = typeof Declaration.Type

/** Structural joins only. No graph edge establishes a proof or propagates success. */
export const proofMapIntegrity = (
  map: ProofMap, concepts: ReadonlyArray<string>, claims: ReadonlyArray<ClaimRecord>,
  ceiling: ReadonlyArray<string>,
): Array<string> => {
  const issues: Array<string> = []
  const unique = (path: string, ids: ReadonlyArray<string>) => {
    const seen = new Set<string>()
    for (const id of ids) {
      if (seen.has(id)) issues.push(`${path}: duplicate ${id}`)
      seen.add(id)
    }
  }
  const known = (path: string, ids: ReadonlyArray<string>, universe: ReadonlySet<string>) => {
    unique(path, ids)
    for (const id of ids) if (!universe.has(id)) issues.push(`${path}: unknown reference ${id}`)
  }
  // Edges point from prerequisites to consumers. Kahn's traversal checks only the named relation.
  const acyclic = (path: string, ids: ReadonlyArray<string>, edges: ReadonlyArray<readonly [string, string]>) => {
    const incoming = new Map(ids.map((id) => [id, 0]))
    const outgoing = new Map<string, Array<string>>()
    for (const [from, to] of edges) {
      if (!incoming.has(from) || !incoming.has(to)) continue
      incoming.set(to, incoming.get(to)! + 1)
      const next = outgoing.get(from) ?? []
      next.push(to)
      outgoing.set(from, next)
    }
    const ready = ids.filter((id) => incoming.get(id) === 0)
    let visited = 0
    for (let index = 0; index < ready.length; index++) {
      const id = ready[index]!
      visited++
      for (const to of outgoing.get(id) ?? []) {
        const count = incoming.get(to)! - 1
        incoming.set(to, count)
        if (count === 0) ready.push(to)
      }
    }
    if (visited !== incoming.size) issues.push(`${path}: dependency cycle`)
  }
  const featureIds = map.features.map((feature) => feature.id)
  const nodeIds = map.nodes.map((node) => node.id)
  const workIds = map.work.map((item) => item.id)
  unique("proofMap.features", featureIds)
  unique("proofMap.nodes", nodeIds)
  unique("proofMap.work", workIds)
  const featureSet = new Set(featureIds)
  const nodeSet = new Set(nodeIds)
  const conceptSet = new Set(concepts)
  const claimSet = new Set(claims.map((claim) => claim.id))
  const workSet = new Set([...nodeIds, ...workIds])
  for (const id of workIds) if (nodeSet.has(id)) issues.push(`proofMap.work: id collides with node ${id}`)
  for (const feature of map.features) {
    const path = `proofMap.features (${feature.id})`
    known(`${path}.concepts`, feature.concepts, conceptSet)
    for (const field of ["syntax", "judgments", "rules"] as const) known(`${path}.${field}`, feature[field], nodeSet)
    known(`${path}.requires`, feature.requires, featureSet)
  }
  acyclic("proofMap.features", featureIds, map.features.flatMap((feature) =>
    feature.requires.map((id): readonly [string, string] => [id, feature.id])))

  const same = (a: ReadonlyArray<string>, b: ReadonlyArray<string>) =>
    a.length === b.length && a.every((value, index) => value === b[index])
  const matches = (node: typeof ProofMapNode.Type, declaration: DeclarationRecord, axioms: ReadonlyArray<string> | null) =>
    node.module === declaration.module && node.statement === declaration.statement &&
    same(node.levels, declaration.levels) && (axioms === null || same([...node.axioms].sort(), [...axioms].sort()))
  // A refuted claim points to a proved refutation theorem, not to a "refuted" theorem node.
  const associations = (claim: ClaimRecord): Array<{
    declaration: DeclarationRecord, kind: "theorem" | "goal", status: "proved" | "wanted", evidence: string, axioms: ReadonlyArray<string> | null,
  }> => {
    const status = claim.status
    switch (status._tag) {
      case "proved": return [
        { declaration: status.witness, kind: "theorem", status: "proved", evidence: status.witness.name, axioms: status.witness.axioms },
        ...(status.goal === null ? [] : [{
          declaration: status.goal, kind: "goal" as const, status: "proved" as const, evidence: status.witness.name,
          axioms: status.witness.axioms,
        }]),
      ]
      // The claim reports the marker's axioms, not the placeholder's. Only its node ceiling is comparable.
      case "wanted": return [{ declaration: status.goal, kind: "goal", status: "wanted", evidence: status.placeholder, axioms: null }]
      case "refuted": return status.counterexample.witness === null ? [] : [{
        declaration: status.counterexample.witness, kind: "theorem", status: "proved",
        evidence: status.counterexample.witness.name, axioms: status.counterexample.witness.axioms,
      }]
      default: return []
    }
  }
  for (const node of map.nodes) {
    const path = `proofMap.nodes (${node.id})`
    known(`${path}.claims`, node.claims, claimSet)
    unique(`${path}.levels`, node.levels)
    unique(`${path}.axioms`, node.axioms)
    if (node.kind === "definition") {
      if (node.status !== "defined" || node.evidence !== null) issues.push(`${path}: definition requires defined status and null evidence`)
    } else {
      if (node.body !== null) issues.push(`${path}: non-definition body must be null`)
      if (node.status === "defined" || (node.kind === "theorem" && node.status !== "proved"))
        issues.push(`${path}: kind/status mismatch`)
      if (node.evidence === null) issues.push(`${path}: proof or goal requires evidence`)
      if (node.kind === "theorem" && node.evidence !== node.id) issues.push(`${path}: theorem evidence must name itself`)
      if (node.status === "wanted" && node.evidence !== `${node.id}.wanted`)
        issues.push(`${path}: wanted evidence must name its placeholder`)
      if (node.kind === "goal" && node.status === "proved" && node.evidence !== `${node.id}.checked`)
        issues.push(`${path}: proved goal evidence must name its checked witness`)
      if (node.axioms.some((axiom) => !ceiling.includes(axiom))) issues.push(`${path}: evidence exceeds semantic axiom ceiling`)
    }
    for (const claim of claims) {
      const association = associations(claim).find((item) => item.declaration.name === node.id)
      if (association) {
        if (node.kind !== association.kind || node.status !== association.status || node.evidence !== association.evidence ||
            !matches(node, association.declaration, association.axioms)) issues.push(`${path}: evidence disagrees with claim ${claim.id}`)
      } else if (node.claims.includes(claim.id)) issues.push(`${path}: not an evidence pointer of claim ${claim.id}`)
    }
  }
  unique("proofMap.edges", map.edges.map((edge) => JSON.stringify([edge.from, edge.to, edge.kind])))
  const nodes = new Map(map.nodes.map((node) => [node.id, node]))
  for (const edge of map.edges) {
    const path = `proofMap.edges (${edge.from} -> ${edge.to}, ${edge.kind})`
    for (const id of [edge.from, edge.to]) if (!nodeSet.has(id)) issues.push(`${path}: unknown node ${id}`)
    const consumer = nodes.get(edge.to)
    if (consumer && edge.kind === "proof-reference" && (consumer.kind === "definition" || consumer.status !== "proved"))
      issues.push(`${path}: proof-reference consumer must be proved`)
    if (consumer && edge.kind === "definition-reference" && consumer.kind !== "definition")
      issues.push(`${path}: definition-reference consumer must be a definition`)
    if (edge.kind === "ledger-prerequisite" &&
        ((nodes.has(edge.from) && nodes.get(edge.from)!.kind !== "goal") || (consumer && consumer.kind !== "goal")))
      issues.push(`${path}: ledger prerequisites must connect goals`)
  }
  acyclic("proofMap.ledger", nodeIds, map.edges.filter((edge) => edge.kind === "ledger-prerequisite")
    .map((edge): readonly [string, string] => [edge.from, edge.to]))
  for (const item of map.work) {
    known(`proofMap.work (${item.id}).features`, item.features, featureSet)
    known(`proofMap.work (${item.id}).after`, item.after, workSet)
  }
  acyclic("proofMap.work", [...nodeIds, ...workIds], map.work.flatMap((item) =>
    item.after.map((id): readonly [string, string] => [id, item.id])))
  return issues
}
