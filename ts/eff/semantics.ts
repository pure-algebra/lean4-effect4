// The v1 semantics report (seat-B/spec-v3 §§2.3, 8), separate from the program IR.
// The producer validates Lean evidence; this consumer checks the report's shape and links.
import { Schema } from "effect"

const Count = Schema.Int.check(Schema.isGreaterThanOrEqualTo(0))
const Text = Schema.String.check(Schema.isPattern(/\S/))
/** A Lean name as `Name.toString` prints it: non-empty, no whitespace. */
const LeanName = Schema.String.check(Schema.isPattern(/^\S+$/))
/** Concept and claim ids: kebab-case. */
const Id = Schema.String.check(Schema.isPattern(/^[a-z0-9]+(-[a-z0-9]+)*$/))
/** A row id of Test/Counterexamples/REGISTER.md. */
const RegisterId = Schema.String.check(Schema.isPattern(/^E4-[A-Z0-9]+(?:-[A-Z0-9]+)*-CE-[0-9]{3}$/))
/** The leading word of the register's status cell (REGISTER.md:13-28). */
const RegisterStatus = Schema.Literals(["SEEDED", "PINNED", "RESERVED", "MOVED", "REPAIRED", "RETIRED"])

/** A constant of the loaded environment. `statement` is display only, printed at emit time. */
export const Declaration = Schema.Struct({
  name: LeanName,
  module: LeanName,
  levels: Schema.Array(Schema.String),
  statement: Text,
  axioms: Schema.Array(Schema.String),
  withinSemanticAxiomCeiling: Schema.Boolean,
})

export const CounterexampleRef = Schema.Struct({
  id: RegisterId,
  registerStatus: RegisterStatus,
  /** Verbatim register row for historical context; no current-refutation conclusion is inferred. */
  record: Text,
  witness: Schema.NullOr(Declaration),
})

export const Status = Schema.TaggedUnion({
  proved: { by: Schema.Literals(["theorem", "ledger"]), witness: Declaration, goal: Schema.NullOr(Declaration) },
  wanted: { goal: Declaration, placeholder: LeanName },
  refuted: { counterexample: CounterexampleRef },
  absent: { reason: Text },
  assumed: { source: Text, reason: Text },
})

export const Role = Schema.Literals([
  "inversion", "canonicalForms", "weakening", "substitution", "progress", "preservation",
  "monotonicity", "transitivity", "antisymmetry", "decidability", "adequacy", "simulation",
  "compatibility", "fundamentalProperty",
])

export const LiteratureRef = Schema.Struct({
  work: Text,
  locator: Text,
  relation: Schema.Literals(["definitionUsed", "proofTechnique", "adaptedResult", "analogy", "excludedFeature"]),
})

export const Claim = Schema.Struct({
  id: Id,
  concept: Id,
  role: Role,
  title: Text,
  status: Status,
  contestedBy: Schema.Array(CounterexampleRef),
  literature: Schema.Array(LiteratureRef),
})

export const Counts = Schema.Struct({
  claims: Count, proved: Count, wanted: Count, refuted: Count, absent: Count, assumed: Count,
})

export const Concept = Schema.Struct({
  id: Id,
  title: Text,
  defaultModules: Schema.Array(LeanName),
  counts: Counts,
})

export const Cut = Schema.Struct({
  concept: Id,
  decisionRow: Count,
  who: Text,
  excluded: Text,
  reason: Text,
})

export const Placement = Schema.Struct({
  universe: Text,
  declarations: Schema.Array(Schema.Struct({
    name: LeanName,
    module: LeanName,
    concept: Id,
    placement: Schema.Literals(["tagged", "inherited"]),
  })),
  unplacedCount: Count,
  unplacedByModule: Schema.Array(Schema.Struct({ module: LeanName, count: Count })),
})

const ReportShape = Schema.Struct({
  format: Schema.Literal("effect4-semantics-report"),
  schemaVersion: Schema.Literal(1),
  producer: Text,
  command: Schema.Literal("make gen-semantics"),
  inputs: Schema.Array(Text),
  provenance: Schema.Struct({
    toolchain: Text,
    roots: Schema.Array(LeanName),
    policy: Schema.Struct({ gate: Text, ceiling: Schema.Array(LeanName) }),
  }),
  concepts: Schema.Array(Concept),
  claims: Schema.Array(Claim),
  cuts: Schema.Array(Cut),
  placement: Placement,
})

type Report = typeof ReportShape.Type

const duplicates = (values: ReadonlyArray<string>): Array<string> =>
  [...new Set(values.filter((value, index) => values.indexOf(value) !== index))]

/** Structural consistency only; authored assignments do not validate Lean proofs. */
export const integrity = (report: Report): Array<string> => {
  const issues: Array<string> = []
  const unique = (path: string, values: ReadonlyArray<string>) => {
    for (const value of duplicates(values)) issues.push(`${path}: duplicate ${value}`)
  }
  const conceptIds = report.concepts.map((concept) => concept.id)
  unique("concepts", conceptIds)
  unique("claims", report.claims.map((claim) => claim.id))
  unique("inputs", report.inputs)
  unique("provenance.roots", report.provenance.roots)
  if (report.inputs.length === 0) issues.push("inputs: expected producer inputs")
  if (report.provenance.roots.length === 0) issues.push("provenance.roots: expected loaded roots")
  unique("provenance.policy.ceiling", report.provenance.policy.ceiling)
  if (report.provenance.policy.gate !== "Test/Audit/AxiomGate.lean")
    issues.push("provenance.policy.gate: expected Test/Audit/AxiomGate.lean")
  const ceiling = ["propext", "Quot.sound"]
  if (report.provenance.policy.ceiling.length !== ceiling.length ||
      ceiling.some((name) => !report.provenance.policy.ceiling.includes(name)))
    issues.push("provenance.policy.ceiling: expected propext and Quot.sound")

  const defaults = report.concepts.flatMap((concept) => concept.defaultModules)
  unique("concepts.defaultModules", defaults)
  const goals: Array<string> = []
  const checkDeclaration = (path: string, declaration: typeof Declaration.Type) => {
    if (!declaration.withinSemanticAxiomCeiling ||
        declaration.axioms.some((name) => !ceiling.includes(name)))
      issues.push(`${path}: evidence exceeds the declared semantic axiom ceiling`)
  }
  report.claims.forEach((claim, index) => {
    const path = `claims[${index}] (${claim.id})`
    if (!conceptIds.includes(claim.concept)) issues.push(`${path}: unknown concept ${claim.concept}`)
    const status = claim.status
    switch (status._tag) {
      case "proved":
        checkDeclaration(`${path}.status.witness`, status.witness)
        if (status.by === "ledger" && status.goal === null)
          issues.push(`${path}.status.goal: ledger evidence requires a goal`)
        if (status.by === "theorem" && status.goal !== null)
          issues.push(`${path}.status.goal: theorem evidence has no ledger goal`)
        if (status.goal !== null) {
          goals.push(status.goal.name)
          checkDeclaration(`${path}.status.goal`, status.goal)
        }
        break
      case "wanted":
        goals.push(status.goal.name)
        checkDeclaration(`${path}.status.goal`, status.goal)
        if (status.placeholder !== `${status.goal.name}.wanted`)
          issues.push(`${path}.status.placeholder: expected ${status.goal.name}.wanted`)
        break
      case "refuted":
        if (status.counterexample.registerStatus === "RETIRED")
          issues.push(`${path}.status.counterexample: a retired row cannot refute a claim`)
        if (status.counterexample.witness === null)
          issues.push(`${path}.status.counterexample.witness: refutation requires evidence`)
        else checkDeclaration(`${path}.status.counterexample.witness`, status.counterexample.witness)
        break
    }
    unique(`${path}.contestedBy`, claim.contestedBy.map((reference) => reference.id))
    claim.contestedBy.forEach((reference, refIndex) => {
      if (reference.witness !== null)
        checkDeclaration(`${path}.contestedBy[${refIndex}].witness`, reference.witness)
    })
  })
  unique("claims: goal counted by two claims", goals)
  report.cuts.forEach((cut, index) => {
    if (!conceptIds.includes(cut.concept)) issues.push(`cuts[${index}]: unknown concept ${cut.concept}`)
  })
  unique("placement.declarations", report.placement.declarations.map((declaration) => declaration.name))
  report.placement.declarations.forEach((declaration, index) => {
    const path = `placement.declarations[${index}] (${declaration.name})`
    const concept = report.concepts.find((candidate) => candidate.id === declaration.concept)
    if (!concept) issues.push(`${path}: unknown concept ${declaration.concept}`)
    if (!defaults.includes(declaration.module))
      issues.push(`${path}.module: outside the concept-module census universe`)
    if (concept && declaration.placement === "inherited" && !concept.defaultModules.includes(declaration.module))
      issues.push(`${path}: inherited placement does not match the concept's default modules`)
  })
  unique("placement.unplacedByModule", report.placement.unplacedByModule.map((entry) => entry.module))
  report.placement.unplacedByModule.forEach((entry, index) => {
    if (!defaults.includes(entry.module))
      issues.push(`placement.unplacedByModule[${index}].module: outside the concept-module census universe`)
  })
  const unplaced = report.placement.unplacedByModule.reduce((sum, entry) => sum + entry.count, 0)
  if (unplaced !== report.placement.unplacedCount)
    issues.push(`placement.unplacedCount: is ${report.placement.unplacedCount}, module counts say ${unplaced}`)
  for (const concept of report.concepts) {
    const claims = report.claims.filter((claim) => claim.concept === concept.id)
    const tally = (tag: typeof Status.Type["_tag"]) => claims.filter((claim) => claim.status._tag === tag).length
    const expected = {
      claims: claims.length, proved: tally("proved"), wanted: tally("wanted"),
      refuted: tally("refuted"), absent: tally("absent"), assumed: tally("assumed"),
    }
    for (const key of Object.keys(expected) as Array<keyof typeof expected>) {
      if (concept.counts[key] !== expected[key])
        issues.push(`concepts (${concept.id}): counts.${key} is ${concept.counts[key]}, claims say ${expected[key]}`)
    }
  }
  return issues
}

export const SemanticsReport = ReportShape.check(Schema.makeFilter((report) => {
  const issues = integrity(report)
  return issues.length === 0 ? true : issues
}))

export type SemanticsReport = typeof SemanticsReport.Type

/** Excess keys refused: a wall-clock field or any unschematized key fails, never stripped. */
export const decodeSemanticsReport = Schema.decodeUnknownSync(SemanticsReport, { onExcessProperty: "error" })
