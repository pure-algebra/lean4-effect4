#!/usr/bin/env bun
/**
 * The rows and atoms against the target's own declarations (plan 1.11(b)).
 *
 *     bun tools/target/rows.ts --repo . [--promote]
 *
 * A row of `NativeOp.row` transcribes an rc.112 export: `Ref.set` is `Ref.set`, `Deferred.await`
 * is `Deferred.await`. An atom of the alphabet is an export of the generated prelude block. Both
 * are claims about a signature the target declares, and nothing had ever asked the target about
 * them — `make check-citations` reads the path of a `cite` and never its line, let alone its
 * content.
 *
 * So: one query per row (`Parameters<typeof Ref.set>` and the three `Effect` columns of its
 * `ReturnType`) and one per atom (`Parameters<typeof Atoms.isSome>` and its `ReturnType`, which
 * is a value, not an `Effect`), with the expectation `Ty.renderRaw` prints for the row's request,
 * answer and error, under the row's own shape (`generated/row-types.tsv`).
 *
 * Every line of `generated/row-citations.tsv` is a report, never a gate on agreement: an rc.112
 * export is generic where a row is monomorphic, so most rows are *reported* with what the target
 * declares rather than judged. The two rows this repository already knows disagree are signed
 * exceptions with their content, not skips (DI-97, DI-98). The committed file is compared on
 * every run; `--promote` rewrites it.
 */
import { readFileSync, writeFileSync } from "node:fs"
import { resolve } from "node:path"
import { rowSignatures, type RowSignature } from "./profile.ts"
import { query, type Observation, type Query } from "./oracle.ts"

/** The two rows whose answer column disagrees with rc.112 on purpose (plan Q9). The content is
 * stated here, not a skip: the lane reports the exception and what the target actually says. */
const signed: Record<string, string> = {
  "Native/deferredPoll":
    "DI-98, signed exception: rc.112's `Deferred.poll` answers `Effect<Option<Effect<A, E>>>` (Deferred.ts:1414-1416); this row answers `bool` because the language has no carrier for an Effect as a value, and the machine answers `isSome` of the rc.112 value.",
  "Native/refSet":
    "DI-97, signed exception: rc.112's `Ref.set` answers `Effect<void>` (Ref.ts:306-307); this row answers the cell, because the machine answers the cell (`refStep (SyncOp.refSet cell value) heap = (Val.cell cell, ...)`, Stores.lean:883-884, pinned at :979 and :993-994). The restatement is scheduled with the binder-term rows of L4.",
}

// `Effect` itself is imported by every query source; naming it again here is a duplicate
// identifier, which refuses the query.
const imports = ['import type { Cause, Context, Deferred, Exit, Fiber, Option, Ref, Result, Scope } from "effect"']

export function queries(repo: string, signatures: Map<string, RowSignature>): Query[] {
  const out: Query[] = []
  for (const [id, signature] of signatures) {
    const [table, name] = id.split("/") as [string, string]
    if (table !== "Native" && table !== "Atom") continue
    const atom = table === "Atom"
    const subject = atom ? `typeof Atoms.${name}` : `typeof ${nativeSpelling(name)}`
    // A `value` row is not called: `Effect.currentTimeMillis` is an `Effect`, not a function.
    const value = signature.shape === "value"
    const q: Query = {
      id, source: atom ? "harness/truth/prelude-atoms.gen.ts" : "vendor/effect-4.0.0-rc.112/src",
      imports: atom ? [...imports, `import type * as Atoms from ${JSON.stringify(resolve(repo, "harness/truth/prelude-atoms.gen.ts"))}`] : imports,
      subject, kind: atom ? "callable" : value ? "effect" : "function", expected: {},
      provenance: { table, row: name, scheme: signature.shape, rendered: signature },
    }
    if (signature.request && !value) q.expected.request = signature.request
    if (signature.answer) q.expected.A = signature.answer
    if (!atom && signature.error) q.expected.E = signature.error
    if (!atom) q.expected.R = "never"
    // A row that declares the top means it (decisions row 46, `tagIs`): comparing `unknown`
    // against `unknown` is the claim, not contamination.
    const top = (["A", "E", "R", "request"] as const).filter(axis => /\bunknown\b/.test(q.expected[axis] ?? ""))
    if (top.length) q.allowUnknown = top
    out.push(q)
  }
  return out
}

/** The export a row prints, as its spelling names it. The rows of `NativeOp.row` spell the
 * qualified rc.112 export (`Ref.set`), which is what the query asks about. */
const spellings: Record<string, string> = {
  refMake: "Ref.make", refGet: "Ref.get", refSet: "Ref.set", refGetAndSet: "Ref.getAndSet",
  refSetAndGet: "Ref.setAndGet", refUpdate: "Ref.update", refGetAndUpdate: "Ref.getAndUpdate",
  refUpdateAndGet: "Ref.updateAndGet", refUpdateSome: "Ref.updateSome",
  refGetAndUpdateSome: "Ref.getAndUpdateSome", refUpdateSomeAndGet: "Ref.updateSomeAndGet",
  refModify: "Ref.modify", refModifySome: "Ref.modifySome", deferredMake: "Deferred.make",
  deferredIsDone: "Deferred.isDone", deferredPoll: "Deferred.poll",
  deferredSucceed: "Deferred.succeed", deferredFail: "Deferred.fail", deferredAwait: "Deferred.await",
  scopeMake: "Scope.make", sleep: "Effect.sleep", clockNow: "Effect.currentTimeMillis",
}
function nativeSpelling(name: string): string {
  const spelling = spellings[name]
  if (!spelling) throw new Error(`rows: no target spelling for Native/${name}`)
  return spelling
}

const COLUMNS = ["id", "subject", "scheme", "status", "expectedRequest", "actualRequest",
  "expectedAnswer", "actualAnswer", "agreement", "note"] as const

export function row(observation: Observation, signature: RowSignature): string {
  const columns = observation.columns
  const agreement = ["request", "A", "E", "R"]
    .map(axis => `${axis}=${columns[axis as "A"]?.agreement ?? "-"}`).join(" ")
  const reasons = observation.issues.map(i => i.code + (i.axis ? `/${i.axis}` : "")).filter((c, i, a) => a.indexOf(c) === i)
  const note = [signed[observation.id] ?? "", reasons.join(" "),
    observation.signatures[0]?.text ? `declared ${observation.signatures[0].text}` : ""]
    .filter(Boolean).join("; ").replaceAll("\t", " ").replaceAll("\n", " ")
  return [observation.id, observation.binding.subject, signature.shape, observation.status,
    signature.request || "-", columns.request?.actual ?? "-",
    signature.answer || "-", columns.A?.actual ?? "-", agreement, note].join("\t")
}

if (import.meta.main) {
  const args = process.argv.slice(2)
  let repo = resolve(import.meta.dir, "../.."), promote = false
  for (let i = 0; i < args.length; i++) {
    const arg = args[i]
    if (arg === "--promote") { promote = true; continue }
    const value = args[++i]
    if (!value) throw new Error(`missing value for ${arg}`)
    if (arg === "--repo") repo = resolve(value)
    else throw new Error(`unknown option ${arg}`)
  }
  const signatures = rowSignatures(repo)
  const selection = queries(repo, signatures)
  const report = query(repo, selection, "effect@4.0.0-rc.112/rows")
  const byId = new Map(report.observations.map(o => [o.id, o]))
  const lines = selection.map(q => {
    const observation = byId.get(q.id)
    if (!observation) throw new Error(`the compiler answered nothing for ${q.id}`)
    return row(observation, signatures.get(q.id)!)
  })
  const text = ["# GENERATED by make check-target (tools/target/rows.ts); do not edit",
    `# every row of NativeOp.row and every atom of the alphabet against the export it transcribes, under tsgo ${report.versions.typescript}`,
    "# a report, not a gate on agreement: an rc.112 export is generic where a row is monomorphic, so `status` is what the query could establish",
    "# " + COLUMNS.join("\t"), ...lines, ""].join("\n")
  const counts = new Map<string, number>()
  for (const q of selection) counts.set(byId.get(q.id)!.status, (counts.get(byId.get(q.id)!.status) ?? 0) + 1)
  console.log(`rows: ${selection.length} queried (${selection.filter(q => q.id.startsWith("Native/")).length} rows, ${selection.filter(q => q.id.startsWith("Atom/")).length} atoms); ` +
    [...counts.entries()].sort().map(([k, n]) => `${k} ${n}`).join(", "))
  const expected = resolve(repo, "generated/row-citations.tsv")
  if (promote) {
    writeFileSync(expected, text)
    console.log(`rows: wrote ${expected}`)
  } else {
    let committed: string | undefined
    try { committed = readFileSync(expected, "utf8") } catch { committed = undefined }
    if (committed !== text) {
      const fresh = resolve(repo, ".lake/target/row-citations.tsv")
      writeFileSync(fresh, text)
      console.error(`FAIL rows: generated/row-citations.tsv differs from this run (see ${fresh}); promote it deliberately if the change is intended`)
      process.exit(1)
    }
  }
  console.log("PASS rows: the table is what this run observed")
}
