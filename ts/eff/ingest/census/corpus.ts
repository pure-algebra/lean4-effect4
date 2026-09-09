// Retargeted from foldlab experiments/parser-census/src/corpus.ts at 4005d34f.
// Corpus inputs are read-only. Resolve generation from the owning package, never the host.
import { readFileSync, existsSync, readdirSync } from "node:fs"
import { dirname, join, relative, resolve } from "node:path"
import { spawnSync } from "node:child_process"
import ts from "typescript"
import { Schema } from "effect"
import { Manifest, Labels, type Generation, type Project } from "./census-contract.ts"
export const excluded = ["node_modules", ".git", ".lake", "dist", "build", "out", ".next", ".turbo", ".cache", "coverage", ".output", ".svelte-kit", ".vercel"]
const ObjectSchema = Schema.Record(Schema.String, Schema.Unknown)
const object = (x: unknown): Record<string, unknown> => Schema.is(ObjectSchema)(x) ? x : {}
const text = (x: unknown): string | undefined => typeof x === "string" ? x : undefined
const json = (path: string) => {
  const parsed = ts.parseConfigFileTextToJson(path, readFileSync(path, "utf8"))
  if (parsed.error) throw new Error(`invalid metadata: ${path}`)
  return object(parsed.config)
}
export function loadCorpus(manifest: string, labels: string, root: string): readonly Project[] {
  const projects = Schema.decodeUnknownSync(Manifest)(json(manifest)).projects
  const vocabulary = Schema.decodeUnknownSync(Labels)(json(labels)).labelVocabulary
  const seen = new Set<string>()
  for (const p of projects) {
    if (seen.has(p.id) || p.labels.some(l => !(l in vocabulary))) throw new Error(`invalid project labels/id: ${p.id}`)
    seen.add(p.id)
    const observed = spawnSync("git", ["rev-parse", "HEAD"], { cwd: resolve(root, p.localPath), encoding: "utf8" })
    if (observed.status !== 0 || observed.stdout.trim() !== p.pin) throw new Error(`corpus pin mismatch: ${p.id}: ${observed.stdout.trim()} != ${p.pin}`)
  }
  return projects
}
export const versionGeneration = (version: string): Generation | undefined => {
  // The first lower bound determines the admitted generation. Upper bounds are not a dependency.
  const m = /^(?:npm:effect@)?[~^>=\s]*(\d+)\./.exec(version)
  if (!m) return undefined
  const major = Number(m[1])
  return major === 4 ? "v4" : major === 3 ? "v3" : major < 3 ? "pre-v3" : undefined
}
export interface Provenance { generation: Generation; package: string; dependency: string; resolved: string; evidence: string }
export class Generations {
  private readonly packages = new Map<string, Record<string, unknown>>()
  private readonly resolved = new Map<string, Provenance>()
  constructor(readonly root: string) {
    const walk = (dir: string) => {
      if (existsSync(join(dir, "package.json"))) this.packages.set(dir, json(join(dir, "package.json")))
      for (const e of readdirSync(dir, { withFileTypes: true })) if (e.isDirectory() && !excluded.includes(e.name)) walk(join(dir, e.name))
    }
    walk(root)
  }
  private catalog(dir: string, name: string): { value: string; evidence: string } | undefined {
    for (let at = dir; at.startsWith(this.root); at = dirname(at)) {
      const p = this.packages.get(at) ?? {}, w = object(p.workspaces)
      const value = text(object(name ? object(w.catalogs ?? p.catalogs)[name] : w.catalog ?? p.catalog).effect)
      if (value) return { value, evidence: relative(this.root, join(at, "package.json")) }
      const yaml = join(at, "pnpm-workspace.yaml")
      if (existsSync(yaml)) {
        // Read only the scalar catalog entry; nesting is checked, not a global effect grep.
        const stack: { indent: number; key: string }[] = []
        for (const line of readFileSync(yaml, "utf8").split(/\r?\n/)) {
          const m = /^( *)([\w@./-]+):(?:\s+(.*))?\s*$/.exec(line)
          if (!m) continue
          const indent = m[1]!.length, key = m[2]!
          while (stack.length && stack[stack.length - 1]!.indent >= indent) stack.pop()
          const path = [...stack.map(s => s.key), key].join("/")
          if (path === (name ? `catalogs/${name}/effect` : "catalog/effect") && m[3]) return { value: m[3].replace(/\s+#.*$/, "").replace(/^["']|["']$/g, ""), evidence: relative(this.root, yaml) }
          stack.push({ indent, key })
        }
      }
      if (at === this.root) break
    }
    return undefined
  }
  private packageGeneration(dir: string, p: Record<string, unknown>): Provenance | undefined {
    const cache = this.resolved.get(dir); if (cache) return cache
    let dep: string | undefined
    for (const field of ["dependencies", "devDependencies", "peerDependencies", "optionalDependencies"]) dep ??= text(object(p[field]).effect)
    let value = dep, evidence = relative(this.root, join(dir, "package.json"))
    if (p.name === "effect" && text(p.version)) value = text(p.version)
    if (value?.startsWith("catalog:")) { const c = this.catalog(dir, value.slice(8)); value = c?.value; if (c) evidence = c.evidence }
    if (value?.startsWith("workspace:")) {
      const own = [...this.packages].filter(([at, v]) => v.name === "effect" && (at.startsWith(dirname(dir)) || dir.startsWith(dirname(at))))
      const versions = [...new Set(own.map(([, v]) => text(v.version)).filter(v => v !== undefined))]
      if (versions.length === 1) { value = versions[0]; evidence = own.map(([at]) => relative(this.root, join(at, "package.json"))).join(",") }
    }
    if (value === "latest" && existsSync(join(this.root, "bun.lockb"))) {
      const lock = spawnSync("bun", [join(this.root, "bun.lockb")], { encoding: "utf8", maxBuffer: 32 * 1024 * 1024 })
      if (lock.status !== 0) throw new Error(`cannot read pinned binary lock: ${this.root}`)
      value = /^effect@[^\n]*:\n\s+version "([^"]+)"/m.exec(lock.stdout)?.[1]; evidence = "bun.lockb"
    }
    let generation = value ? versionGeneration(value) : undefined
    if (!dep && !(p.name === "effect" && text(p.version))) {
      const names = ["dependencies", "devDependencies", "peerDependencies"].flatMap(f => Object.keys(object(p[f])))
      if (names.some(n => n.startsWith("@effect-ts/"))) { generation = "pre-v3"; value = "@effect-ts/*" }
    }
    if (!generation || !value) return undefined
    const result = { generation, package: relative(this.root, join(dir, "package.json")), dependency: dep ?? value, resolved: value, evidence }
    this.resolved.set(dir, result); return result
  }
  forFile(file: string): Provenance {
    for (let at = dirname(resolve(this.root, file)); at.startsWith(this.root); at = dirname(at)) {
      const p = this.packages.get(at), g = p && this.packageGeneration(at, p)
      if (g) return g
      if (at === this.root) break
    }
    const choices = [...this.packages].map(([at, p]) => this.packageGeneration(at, p)).filter(p => p !== undefined)
    const generations = new Set(choices.map(p => p.generation))
    if (generations.size === 1) return { ...choices[0]!, evidence: `project has one resolved generation; ${choices[0]!.evidence}` }
    if (!choices.length) return { generation: "pre-v3", package: "package.json", dependency: "none", resolved: "none", evidence: "control: no Effect dependency" }
    throw new Error(`no unambiguous owning Effect dependency: ${join(this.root, file)}`)
  }
}
