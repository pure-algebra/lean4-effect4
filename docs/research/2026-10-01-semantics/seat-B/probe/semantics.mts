// Seat B probe copy of the proposed `ts/eff/semantics.ts` (spec-v3 §6). The only difference from
// the file Gemini lands is the import: here the pinned install by absolute path, as Codex's probe
// did; in ts/eff it is `import { Schema } from "effect"` (the precedent of ts/eff/eff.gen.ts:42).
// API forms follow ts/eff/eff.gen.ts: Schema.TaggedUnion, Schema.Literals, Schema.NullOr,
// Schema.Int, .check(Schema.makeFilter(...)). `Schema.NonNegativeInt` does not exist in rc.112's
// dist/Schema.d.ts (0 occurrences), so counts are Int checked >= 0.
import * as Schema from "/Users/pooks/Dev/lean4-effect4/ts/eff/node_modules/effect/dist/Schema.js"

const Count = Schema.Int.check(Schema.isGreaterThanOrEqualTo(0))
const Text = Schema.String.check(Schema.isPattern(/\S/))
/** A Lean name as `Name.toString` prints it: non-empty, no whitespace. */
const LeanName = Schema.String.check(Schema.isPattern(/^\S+$/))
/** Concept and claim ids: kebab-case. */
const Id = Schema.String.check(Schema.isPattern(/^[a-z0-9]+(-[a-z0-9]+)*$/))
/** A row id of Test/Counterexamples/REGISTER.md. */
const RegisterId = Schema.String.check(Schema.isPattern(/^E4-[A-Z0-9]+-CE-[0-9]{3}$/))
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

type Report = {
  readonly concepts: ReadonlyArray<{ readonly id: string; readonly counts: { readonly [k: string]: number } }>
  readonly claims: ReadonlyArray<{ readonly id: string; readonly concept: string; readonly status: { readonly _tag: string } & Record<string, unknown> }>
  readonly cuts: ReadonlyArray<{ readonly concept: string }>
  readonly placement: { readonly declarations: ReadonlyArray<{ readonly name: string; readonly concept: string }> }
}

const duplicates = (xs: ReadonlyArray<string>): Array<string> =>
  xs.filter((x, i) => xs.indexOf(x) !== i)

/** Referential integrity, after the shape: one place a dangling link or a duplicate is refused. */
export const integrity = (r: Report): Array<string> => {
  const issues: Array<string> = []
  const conceptIds = r.concepts.map((c) => c.id)
  for (const d of duplicates(conceptIds)) issues.push(`concepts: duplicate id ${d}`)
  for (const d of duplicates(r.claims.map((c) => c.id))) issues.push(`claims: duplicate id ${d}`)
  for (const d of duplicates(r.placement.declarations.map((x) => x.name))) issues.push(`placement: ${d} placed twice`)
  r.claims.forEach((c, i) => { if (!conceptIds.includes(c.concept)) issues.push(`claims[${i}] (${c.id}): unknown concept ${c.concept}`) })
  r.cuts.forEach((c, i) => { if (!conceptIds.includes(c.concept)) issues.push(`cuts[${i}]: unknown concept ${c.concept}`) })
  r.placement.declarations.forEach((d, i) => { if (!conceptIds.includes(d.concept)) issues.push(`placement.declarations[${i}] (${d.name}): unknown concept ${d.concept}`) })
  // one ledger goal discharges at most one claim (Codex review §8 condition 3)
  const goals = r.claims.flatMap((c) => {
    const g = c.status["goal"] as { name?: string } | null | undefined
    return g && typeof g.name === "string" ? [g.name] : []
  })
  for (const d of duplicates(goals)) issues.push(`claims: goal ${d} counted by two claims`)
  for (const c of r.concepts) {
    const mine = r.claims.filter((x) => x.concept === c.id)
    const tally = (tag: string) => mine.filter((x) => x.status._tag === tag).length
    const expected: Record<string, number> = {
      claims: mine.length, proved: tally("proved"), wanted: tally("wanted"),
      refuted: tally("refuted"), absent: tally("absent"), assumed: tally("assumed"),
    }
    for (const k of Object.keys(expected)) {
      if (c.counts[k] !== expected[k]) issues.push(`concepts (${c.id}): counts.${k} is ${c.counts[k]}, the claims say ${expected[k]}`)
    }
  }
  return issues
}

export const SemanticsReport = Schema.Struct({
  format: Schema.Literal("effect4-semantics-report"),
  schemaVersion: Schema.Literal(1),
  producer: Text,
  provenance: Schema.Struct({
    toolchain: Text,
    roots: Schema.Array(LeanName),
    policy: Schema.Struct({ gate: Text, ceiling: Schema.Array(LeanName) }),
  }),
  concepts: Schema.Array(Concept),
  claims: Schema.Array(Claim),
  cuts: Schema.Array(Cut),
  placement: Placement,
}).check(Schema.makeFilter((r) => {
  const issues = integrity(r)
  return issues.length === 0 ? true : issues
}))

export type SemanticsReport = typeof SemanticsReport.Type

/** Excess keys refused: a wall-clock field or any unschematized key fails, never stripped. */
export const decodeSemanticsReport = Schema.decodeUnknownSync(SemanticsReport, { onExcessProperty: "error" })
