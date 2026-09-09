// Retargeted from foldlab experiments/parser-census/src/capture.ts at 4005d34f.
// Stream files and unit rows; retain only integer histograms and one bounded worker batch.
import { mkdir, open, copyFile, writeFile } from "node:fs/promises"
import { resolve, join, dirname } from "node:path"
import { recognize, type Options } from "../index.ts"
import { canonJson, encodeReport, verdictKey } from "../contract.ts"
import { loadCorpus, Generations, excluded } from "./corpus.ts"
import { censusPins } from "./pins.ts"
import { add, bucket, equal, headSpelling, ordered, pairs, strata } from "./tally.ts"
import type { Metrics } from "./census-contract.ts"
export interface CensusOptions extends Options { root: string; manifest: string; labels: string; out: string }
export async function census(options: CensusOptions) {
  const projects = loadCorpus(options.manifest, options.labels, options.root), pins = censusPins(options.manifest, options.labels)
  await mkdir(options.out, { recursive: true })
  const files = await open(join(options.out, "files.jsonl"), "w"), rows = await open(join(options.out, "units.jsonl"), "w"), defects = await open(join(options.out, "defects.jsonl"), "w")
  const totals = strata(), histogram: Record<string, ReturnType<typeof strata>> = {}
  const metrics = { files: 0, bytes: 0, reads: 0, parseUs: 0, totalUs: 0 }, provenance = new Map<string, unknown>()
  let fileCount = 0, disagreeFiles = 0, declarationDisagreements = 0, parsedFiles = 0, candidateFiles = 0
  const started = performance.now()
  try {
    for (const project of projects) {
      const root = resolve(options.root, project.localPath), generations = new Generations(root)
      const projectTotals = histogram[project.id] = strata()
      for await (const report of recognize([root], { ...options, root, census: true, excludeDirs: excluded, onMetrics: (m: Metrics) => { for (const key of Object.keys(metrics) as (keyof Metrics)[]) metrics[key] += m[key]; options.onMetrics?.(m) } })) {
        fileCount++
        if (report.ckParsed === true || report.oxcParsed === true) parsedFiles++
        const units = pairs(report)
        if (units.length) candidateFiles++
        const generation = units.length ? generations.forFile(report.file) : null
        if (generation) provenance.set(project.id + ":" + generation.package, { project: project.id, ...generation })
        const declarationAgreement = report.ckDeclarations && report.oxcDeclarations ? canonJson(report.ckDeclarations) === canonJson(report.oxcDeclarations) : null
        if (declarationAgreement === false) declarationDisagreements++
        const row = { project: project.id, labels: project.labels, sourcePin: project.pin, generation: generation?.generation ?? null, dependency: generation, ...report }
        await files.write(canonJson({ ...row, ...encodeReport(report) as object }) + "\n")
        if (report.agreement === "disagree" || declarationAgreement === false) {
          disagreeFiles++
          const fixture = join("defects", project.id, report.file)
          await mkdir(dirname(join(options.out, fixture)), { recursive: true })
          await copyFile(join(root, report.file), join(options.out, fixture))
          await defects.write(canonJson({ project: project.id, file: report.file, fixture, contentDigest: report.contentDigest, pins: report.pins, recognition: report.agreement, declarationAgreement }) + "\n")
        }
        for (const { left, right } of units) {
          if (!generation) throw new Error("unit has no generation")
          const unit = (left ?? right)!.unit
          const kind = report.ckDeclarations?.find(d => d.name === unit.name)?.kind ?? report.oxcDeclarations?.find(d => d.name === unit.name)?.kind ?? "entry"
          const unitRow = { project: project.id, labels: project.labels, generation: generation.generation, file: report.file, unit, kind, engine1: left ? verdictKey(left) : null, engine2: right ? verdictKey(right) : null, agree: equal(left, right), code: [left, right].map(v => v?.kind === "refusal" ? v.code : null), headSpelling: [headSpelling(left), headSpelling(right)], pins: report.pins }
          await rows.write(canonJson(unitRow) + "\n")
          add(totals[generation.generation], left, right); add(projectTotals[generation.generation], left, right)
        }
      }
      process.stderr.write(`census ${project.id}: ${Object.values(projectTotals).reduce((n, b) => n + b.candidates, 0)} units\n`)
    }
  } finally { await files.close(); await rows.close(); await defects.close() }
  const wallUs = Math.round((performance.now() - started) * 1000)
  const summary = { pins, projects: projects.length, fileCount, candidateFiles, parsedFiles, disagreeFiles, declarationDisagreements, totals, histogram, dependencies: [...provenance.values()] }
  await writeFile(join(options.out, "summary.json"), canonJson(summary) + "\n")
  await writeFile(join(options.out, "performance.json"), JSON.stringify({ pins, runtime: process.versions.bun ? `bun-${process.versions.bun}` : `node-${process.versions.node}`, engine: options.engine ?? "both", workers: options.workers ?? null, batchSize: options.batchSize ?? 500, force: options.force ?? false, ...metrics, wallUs, peakRssBytes: process.resourceUsage().maxRSS * (process.versions.bun && process.platform === "darwin" ? 1 : 1024), filesPerSecond: fileCount / (wallUs / 1e6), megabytesPerSecond: metrics.bytes / wallUs, parseShare: metrics.totalUs ? metrics.parseUs / metrics.totalUs : 0 }) + "\n")
  const v4 = totals.v4
  await writeFile(join(options.out, "report.md"), `# Ingest census\n\nPinned projects: ${projects.length}. Files: ${fileCount}; candidate files: ${candidateFiles}.\n\nv4: **${v4.lifted} / ${v4.candidates}** corroborated lifts. V3 and pre-v3 are input data only and excluded from this score.\n\nEvery one of ${disagreeFiles} file disagreements has a copied source fixture and a defects.jsonl entry; ${declarationDisagreements} include declaration-enumeration differences.\n\n| Generation | Candidates | Corroborated lifts | Unit disagreements |\n| --- | ---: | ---: | ---: |\n${Object.entries(totals).map(([g, b]) => `| ${g} | ${b.candidates} | ${b.lifted} | ${b.disagree} |`).join("\n")}\n\n## V4 refusal codes\n\n${ordered(v4.codes).map(([k, n]) => `- ${k}: ${n}`).join("\n")}\n\n## V4 unknown heads\n\n${ordered(v4.heads).slice(0, 30).map(([k, n]) => `- ${JSON.stringify(k)}: ${n}`).join("\n")}\n\nCode and head histograms count a unit once per distinct engine answer; disagreements can therefore contribute two different answers. Full counts by project and generation are in summary.json. File rows, unit rows, dependency provenance and source pins are retained alongside this report.\n`)
  return summary
}
