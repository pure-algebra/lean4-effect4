// A pinned report shape, not a receipt of Lean evidence; each mutation attacks one boundary.
import { describe, expect, test } from "bun:test"
import { Schema } from "effect"
import { SemanticsReport, decodeSemanticsReport } from "../semantics.ts"
import fixture from "./semantics.fixture.json"

type FixtureClaim = typeof fixture.claims[number]
const withClaim = (index: number, change: (claim: FixtureClaim) => unknown): unknown => ({
  ...fixture,
  claims: fixture.claims.map((claim, current) => current === index ? change(claim) : claim),
})
const withStatus = (index: number, status: unknown): unknown => withClaim(index, (claim) => ({ ...claim, status }))
const withPlacement = (fields: object): unknown => ({ ...fixture, placement: { ...fixture.placement, ...fields } })
const rejects = (name: string, value: () => unknown, reason?: string) => test(name, () => {
  const decode = () => decodeSemanticsReport(value())
  if (reason) expect(decode).toThrow(reason)
  else expect(decode).toThrow()
})
const witness = fixture.claims[0]!.status.witness!
const goal = fixture.claims[1]!.status.goal!
const refutation = fixture.claims[2]!.status.counterexample!
const contest = fixture.claims[1]!.contestedBy[0]!
const concept = fixture.concepts[0]!
const placed = fixture.placement.declarations[0]!

describe("semantics report boundary", () => {
  test("accepts the pinned instance with command and producer inputs", () => {
    const report = decodeSemanticsReport(fixture)
    expect(report.command).toBe("make gen-semantics")
    expect(report.claims.map((claim) => claim.status._tag)).toEqual(["proved", "wanted", "refuted", "absent"])
  })
  test("the default decoder accepts an excess key; the boundary decoder must refuse it", () => {
    const value = { ...fixture, timestamp: "2026-10-01T19:00:00Z" }
    expect(() => Schema.decodeUnknownSync(SemanticsReport)(value)).not.toThrow()
    expect(() => decodeSemanticsReport(value)).toThrow()
  })
  rejects("refuses excess keys inside evidence", () => withStatus(0, {
    ...fixture.claims[0]!.status, witness: { ...witness, unchecked: true },
  }))
  rejects("refuses a dangling concept", () => withClaim(0, (claim) => ({ ...claim, concept: "store-typing" })), "unknown concept")
  rejects("refuses duplicate claims", () => withClaim(1, (claim) => ({ ...claim, id: "seq-typed" })), "duplicate")
  rejects("refuses duplicate concepts", () => ({ ...fixture, concepts: [concept, concept] }), "duplicate")
  rejects("refuses proved without a witness", () => withStatus(0, { _tag: "proved", by: "theorem", goal: null }))
  rejects("refuses a malformed nested name", () => withStatus(0, {
    ...fixture.claims[0]!.status, witness: { ...witness, name: "seq typed" },
  }))
  rejects("refuses an unknown status tag", () => withStatus(0, { ...fixture.claims[0]!.status, _tag: "checked" }))
  test("accepts the register's existing multi-part domains", () => {
    expect(() => decodeSemanticsReport(withStatus(2, {
      _tag: "refuted", counterexample: { ...refutation, id: "E4-TARGET-NAME-CE-001" },
    }))).not.toThrow()
  })
  rejects("refuses a malformed register id", () => withStatus(2, {
    _tag: "refuted", counterexample: { ...refutation, id: "E4-TYPED-CE-1" },
  }))
  rejects("refuses an unknown register status", () => withStatus(2, {
    _tag: "refuted", counterexample: { ...refutation, registerStatus: "OPEN" },
  }))
  rejects("refuses a refutation without its register record", () => {
    const { record, ...counterexample } = refutation
    return withStatus(2, { _tag: "refuted", counterexample })
  })
  rejects("refuses a refutation with a blank register record", () => withStatus(2, {
    _tag: "refuted", counterexample: { ...refutation, record: "   " },
  }))
  rejects("refuses a contest without its register record", () => {
    const { record, ...reference } = contest
    return withClaim(1, (claim) => ({ ...claim, contestedBy: [reference] }))
  })
  rejects("refuses a contest with a blank register record", () => withClaim(1, (claim) => ({
    ...claim, contestedBy: [{ ...contest, record: "\n\t " }],
  })))
  rejects("refuses duplicate contest references", () => withClaim(1, (claim) => ({
    ...claim, contestedBy: [contest, contest],
  })), "duplicate")
  rejects("refuses counts that disagree with claims", () => ({
    ...fixture, concepts: [{ ...concept, counts: { ...concept.counts, proved: 2 } }],
  }), "counts.proved")
  rejects("refuses negative counts", () => ({
    ...fixture, concepts: [{ ...concept, counts: { ...concept.counts, assumed: -1 } }],
  }))
  rejects("refuses one goal counted by two claims", () => withStatus(3, fixture.claims[1]!.status), "counted by two claims")
  rejects("refuses placement outside tagged/inherited", () => withPlacement({
    declarations: [{ ...placed, placement: "provisional" }],
  }))
  rejects("refuses absent without a reason", () => withStatus(3, { _tag: "absent", reason: "   " }))
  rejects("refuses a malformed counterexample witness", () => withStatus(2, {
    _tag: "refuted", counterexample: { ...refutation, witness: { name: "x" } },
  }))
})

describe("report links and metadata", () => {
  rejects("refuses a missing regeneration command", () => {
    const { command, ...value } = fixture
    return value
  })
  rejects("refuses a different regeneration command", () => ({ ...fixture, command: "make gen" }))
  rejects("refuses missing producer inputs", () => {
    const { inputs, ...value } = fixture
    return value
  })
  rejects("refuses empty inputs", () => ({ ...fixture, inputs: [] }), "inputs")
  rejects("refuses duplicate inputs", () => ({ ...fixture, inputs: [fixture.inputs[0], fixture.inputs[0]] }), "duplicate")
  rejects("refuses empty roots", () => ({ ...fixture, provenance: { ...fixture.provenance, roots: [] } }), "roots")
  rejects("refuses duplicate roots", () => ({
    ...fixture, provenance: { ...fixture.provenance, roots: ["Effect4.Laws", "Effect4.Laws"] },
  }), "duplicate")
  rejects("refuses a mismatched policy gate", () => ({
    ...fixture, provenance: { ...fixture.provenance, policy: { ...fixture.provenance.policy, gate: "Other.lean" } },
  }), "policy.gate")
  rejects("refuses a mismatched axiom ceiling", () => ({
    ...fixture, provenance: { ...fixture.provenance, policy: { ...fixture.provenance.policy, ceiling: ["Classical.choice"] } },
  }), "policy.ceiling")
  rejects("refuses repeated default modules within a concept", () => ({
    ...fixture, concepts: [{ ...concept, defaultModules: [concept.defaultModules[0], concept.defaultModules[0]] }],
  }), "defaultModules")
  rejects("refuses default modules assigned to two concepts", () => ({
    ...fixture, concepts: [concept, {
      id: "store-typing", title: "Another concept", defaultModules: [concept.defaultModules[0]],
      counts: { claims: 0, proved: 0, wanted: 0, refuted: 0, absent: 0, assumed: 0 },
    }],
  }), "defaultModules")
  rejects("refuses an inherited placement from the wrong concept", () => ({
    ...fixture,
    concepts: [concept, {
      id: "store-typing", title: "Another concept", defaultModules: [],
      counts: { claims: 0, proved: 0, wanted: 0, refuted: 0, absent: 0, assumed: 0 },
    }],
    placement: { ...fixture.placement, declarations: [{ ...placed, concept: "store-typing", placement: "inherited" }] },
  }), "inherited placement")
  rejects("refuses a placement outside the census module universe", () => withPlacement({
    declarations: [{ ...placed, module: "Effect4.Laws.Other" }],
  }), "census universe")
  rejects("refuses duplicate placements", () => withPlacement({ declarations: [placed, placed] }), "duplicate")
  rejects("refuses a dangling placement concept", () => withPlacement({
    declarations: [{ ...placed, concept: "unknown-concept" }],
  }), "unknown concept")
  rejects("refuses a dangling cut concept", () => ({
    ...fixture, cuts: [{ ...fixture.cuts[0], concept: "unknown-concept" }],
  }), "unknown concept")
  rejects("refuses inconsistent unplaced totals", () => withPlacement({ unplacedCount: 1 }), "unplacedCount")
  rejects("refuses duplicate unplaced module rows", () => withPlacement({
    unplacedCount: 2, unplacedByModule: [{ module: placed.module, count: 1 }, { module: placed.module, count: 1 }],
  }), "duplicate")
  test("accepts a consistent unplaced count within the named modules", () => {
    expect(() => decodeSemanticsReport(withPlacement({
      unplacedCount: 1, unplacedByModule: [{ module: placed.module, count: 1 }],
    }))).not.toThrow()
  })
})

describe("evidence variants are distinct from authored assignments", () => {
  rejects("refuses ledger evidence without its goal", () => withStatus(0, {
    _tag: "proved", by: "ledger", witness, goal: null,
  }), "requires a goal")
  rejects("refuses theorem evidence carrying a ledger goal", () => withStatus(0, {
    _tag: "proved", by: "theorem", witness, goal,
  }), "no ledger goal")
  rejects("refuses a witness outside the reported ceiling", () => withStatus(0, {
    _tag: "proved", by: "theorem", witness: { ...witness, withinSemanticAxiomCeiling: false }, goal: null,
  }), "axiom ceiling")
  rejects("refuses contradictory witness axiom metadata", () => withStatus(0, {
    _tag: "proved", by: "theorem", witness: { ...witness, axioms: ["Classical.choice"] }, goal: null,
  }), "axiom ceiling")
  rejects("refuses a wanted marker for a different goal", () => withStatus(1, {
    _tag: "wanted", goal, placeholder: "Effect4.Program.Other.wanted",
  }), "placeholder")
  rejects("refuses a refutation without a witness", () => withStatus(2, {
    _tag: "refuted", counterexample: { ...refutation, witness: null },
  }), "requires evidence")
  rejects("refuses a retired row as a refutation", () => withStatus(2, {
    _tag: "refuted", counterexample: { ...refutation, registerStatus: "RETIRED" },
  }), "retired")
  test("placement cannot turn an absent claim into proved evidence", () => {
    const report = decodeSemanticsReport({
      ...fixture, placement: { ...fixture.placement, declarations: [
        ...fixture.placement.declarations,
        { name: "Effect4.Program.Typed.assignedOnly", module: placed.module,
          concept: concept.id, placement: "inherited" },
      ] },
    })
    expect(report.claims[3]!.status._tag).toBe("absent")
    expect(report.concepts[0]!.counts.proved).toBe(1)
  })
})
