/** Pinned TypeScript diagnostics for explicitly selected program/adapter type claims.
 * Assignment statements are the comparison; typeToString is display data only.
 *
 * The compiler is tsgo, the one compiler of decisions row 57 (`@typescript/native-preview`,
 * pinned in `ts/eff/package.json`). Its synchronous client reads a node-internal pipe handle,
 * so it cannot be driven from bun — the same reason `harness/tsdiag/run-tsdiag.mjs` is node.
 * This module is therefore the face: the types, the query sources, and a `query` that runs
 * `checker.ts` under node and returns the report it wrote. Everything that touches the
 * compiler is in `checker.ts`; everything here is text and can be read from either runtime. */
import { spawnSync } from "node:child_process"
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs"
import { tmpdir } from "node:os"
import { fileURLToPath } from "node:url"
import { join } from "node:path"

export type Axis = "A" | "E" | "R" | "request" | "receiver"
export interface Issue { code: string; message: string; axis?: Axis }
export interface Query {
  id: string
  source: string
  /** Import declarations and explicit bindings; no value assertions are generated. */
  imports: string[]
  subject: string
  /** Only programs use an error bound; effect-valued and callable primitives stay exact.
   * `callable` is a function that answers a value rather than an `Effect`: its `A` is the
   * return type itself and it has no error or requirement column (the atoms of the prelude). */
  kind: "program" | "effect" | "function" | "callable"
  receiver?: string
  expected: Partial<Record<Axis, string>>
  /** Handle target bindings, `<qualified name>` → `<target>`: declared in the query source as
   * namespaces, so the compiler resolves the rendered text instead of a hand AST rewrite. */
  bindings?: Record<string, string>
  allowUnknown?: Axis[]
  inputIssues?: Issue[]
  provenance?: unknown
}
export interface Diagnostic {
  code: number; file: string; line: number; column: number; message: string
}
export interface Column {
  expected: string | null; actual: string | null
  actualToExpected: boolean | null; expectedToActual: boolean | null
  agreement: "exact" | "strict-containment" | "mismatch" | null
}
export interface Observation {
  id: string; source: string; status: "agree" | "mismatch" | "refused"
  binding: { kind: Query["kind"]; subject: string; receiver: string | null; imports: string[]; unknownPolicy: Axis[] }
  columns: Partial<Record<Axis, Column>>
  issues: Issue[]; diagnostics: Diagnostic[]
  signatures: Array<{ text: string; parameters: Array<{ name: string; type: string; optional: boolean; rest: boolean }> }>
  provenance: unknown
}
export interface Report {
  format: "effect4-target-report-v1"
  profile: string
  versions: { compiler: string; typescript: string; effect: string; lean: string }
  compilerOptions: unknown
  expected: string[]; attempted: string[]; resolved: string[]; mismatching: string[]; refused: string[]
  globalDiagnostics: Diagnostic[]; observations: Observation[]
  sourceHashes: Record<string, string>
  limitations: string[]
  conforms: boolean
}

/** One assignability question about a bare pair of rendered types (plan 1.10). Neither side is
 * an `Effect` and neither is an axis, so the pair has no axis policy: `unknown` is the top of
 * the algebra (decisions row 46) and is compared here, never refused as contamination. */
export interface Pair {
  id: string
  /** The two rendered types, as `Ty.renderRaw` printed them. */
  left: string
  right: string
}
/** Both readings of one direction: the checker's own relation, and the assignment statement a
 * user's program hits. They are reported side by side and never conflated. */
export interface Direction { assignable: boolean | null; statement: boolean | null }
export interface PairObservation {
  id: string; left: string; right: string
  leftText: string | null; rightText: string | null
  leftToRight: Direction; rightToLeft: Direction
  issues: Issue[]; diagnostics: Diagnostic[]
}
export interface PairReport {
  format: "effect4-assignability-report-v1"
  versions: Report["versions"]
  compilerOptions: unknown
  observations: PairObservation[]
  limitations: string[]
}

const axes: Axis[] = ["A", "E", "R", "request", "receiver"]
export const bindingName = (axis: Axis, direction: string) => `__${axis}_${direction}`
export const pairBindingName = (direction: "leftToRight" | "rightToLeft") => `__pair_${direction}`
/** Every module of the effect namespace a rendered type can name (`Ty.renderRaw`), plus the
 * handle spellings it prints verbatim. */
export const pairImports = ['import type { Cause, Context, Deferred, Exit, Fiber, Option, Ref, Result, Scope } from "effect"']

/** The handle bindings as declarations the compiler resolves. A binding `A.B` → `T` is a
 * namespace `A` with a type member `B`; a binding `A` → `T` is a type alias. The rendered text
 * is then pasted verbatim, so the report's expected column is what Lean printed. */
export function bindingSource(bindings: Record<string, string> | undefined): string[] {
  const lines: string[] = []
  const roots = new Map<string, Array<{ path: string[]; target: string }>>()
  const bound = new Map<string, string>()
  for (const [name, target] of Object.entries(bindings ?? {})) {
    // Two names on one target are one host type: the collapse DI-24/DI-76 refuse, caught at the
    // binding rather than per column.
    const prior = bound.get(target)
    if (prior !== undefined) throw new Error(`noninjective handle binding: ${prior} and ${name} both map to ${target}`)
    bound.set(target, name)
    const parts = name.split(".")
    if (!parts.length || !parts.every(p => /^[A-Za-z_$][\w$]*$/.test(p))) throw new Error(`invalid handle binding name ${name}`)
    if (!/^[A-Za-z_$][\w$]*(\.[A-Za-z_$][\w$]*)*$/.test(target)) throw new Error(`invalid qualified target binding ${target}`)
    const [root, ...rest] = parts as [string, ...string[]]
    if (!roots.has(root)) roots.set(root, [])
    roots.get(root)!.push({ path: rest, target })
  }
  for (const [root, members] of [...roots].sort(([a], [b]) => a.localeCompare(b))) {
    const direct = members.find(m => !m.path.length)
    if (direct) {
      if (members.length !== 1) throw new Error(`handle binding ${root} is both a name and a namespace`)
      lines.push(`type ${root} = ${direct.target}`)
      continue
    }
    const open = (path: string[], target: string): string =>
      path.length === 1 ? `export type ${path[0]} = ${target}`
        : `export namespace ${path[0]} { ${open(path.slice(1), target)} }`
    lines.push(`declare namespace ${root} { ${members.map(m => open(m.path, m.target)).join(" ")} }`)
  }
  return lines
}

/** The module the compiler is asked about: the subject's three Effect columns, the request and
 * receiver of a callable, and one assignment statement per axis and direction. */
export function querySource(q: Query): string {
  const lines = ['import type * as Effect from "effect/Effect"', ...q.imports, ...bindingSource(q.bindings),
    `type __Subject = ${q.subject}`]
  if (q.kind === "callable") {
    // No Effect extraction: the answer column is the return type itself.
    lines.push("type __Actual_A = ReturnType<__Subject>")
  } else {
    lines.push(
      `type __Effect = ${q.kind === "function" ? "ReturnType<__Subject>" : "__Subject"}`,
      "type __EffectShape = [__Effect] extends [never] ? false : __Effect extends Effect.Effect<infer _A, infer _E, infer _R> ? true : false",
      "declare const __effectShape: __EffectShape",
      "export const __requiresEffect: true = __effectShape",
      "type __Actual_A = Effect.Success<__Effect>",
      "type __Actual_E = Effect.Error<__Effect>",
      "type __Actual_R = Effect.Services<__Effect>")
  }
  if (q.kind === "function" || q.kind === "callable") lines.push("type __Actual_request = Parameters<__Subject>")
  if (q.receiver !== undefined) lines.push(`type __Actual_receiver = ${q.receiver}`)
  const callable = q.kind === "function" || q.kind === "callable"
  for (const axis of axes) {
    if ((axis === "request" && !callable) || (axis === "receiver" && q.receiver === undefined)) continue
    // A callable answers a value: it has no error and no requirement column to compare.
    if (q.kind === "callable" && (axis === "E" || axis === "R")) continue
    lines.push(`declare const __${axis}_actual: __Actual_${axis}`)
    const expected = q.expected[axis]
    if (expected === undefined) continue
    lines.push(`type __Expected_${axis} = ${expected}`,
      `declare const __${axis}_expected: __Expected_${axis}`,
      `export const ${bindingName(axis, "actualToExpected")}: __Expected_${axis} = __${axis}_actual`,
      `export const ${bindingName(axis, "expectedToActual")}: __Actual_${axis} = __${axis}_expected`)
  }
  return lines.join("\n") + "\n"
}

/** The module a bare type pair is asked about. The two named aliases are where the checker's
 * own relation is read; the two assignments are what a user's program hits. */
export function pairSource(p: Pair): string {
  return [...pairImports,
    `type __Left = ${p.left}`,
    `type __Right = ${p.right}`,
    "declare const __left: __Left",
    "declare const __right: __Right",
    `export const ${pairBindingName("leftToRight")}: __Right = __left`,
    `export const ${pairBindingName("rightToLeft")}: __Left = __right`,
  ].join("\n") + "\n"
}

/** The node that runs the compiler. `node` is a pinned tool of this repository (`make doctor`). */
const nodeExecutable = () => process.env.EFFECT4_NODE ?? "node"
const checkerPath = () => fileURLToPath(new URL("./checker.ts", import.meta.url))

function run(request: unknown): unknown {
  const directory = mkdtempSync(join(tmpdir(), "effect4-target-"))
  try {
    const input = join(directory, "request.json"), output = join(directory, "response.json")
    writeFileSync(input, JSON.stringify(request))
    const result = spawnSync(nodeExecutable(), [checkerPath(), input, output], { encoding: "utf8" })
    if (result.error) throw new Error(`target oracle: ${nodeExecutable()} could not run the checker: ${String(result.error)}`)
    if (result.status !== 0) throw new Error(`target oracle: the checker refused (exit ${result.status}):\n${result.stderr}`)
    return JSON.parse(readFileSync(output, "utf8"))
  } finally { rmSync(directory, { recursive: true, force: true }) }
}

export function query(repoRoot: string, queries: readonly Query[], profile = "effect@4.0.0-rc.112/adapter"): Report {
  if (new Set(queries.map(q => q.id)).size !== queries.length) throw new Error("duplicate target query ID")
  if (!queries.length) throw new Error("empty required target selection")
  return run({ kind: "query", repo: repoRoot, profile, queries }) as Report
}

/** The assignability differential's questions (plan 1.10), in one compiler run. */
export function assignability(repoRoot: string, questions: readonly Pair[]): PairReport {
  if (new Set(questions.map(p => p.id)).size !== questions.length) throw new Error("duplicate assignability pair ID")
  if (!questions.length) throw new Error("empty required assignability selection")
  return run({ kind: "pairs", repo: repoRoot, pairs: questions }) as PairReport
}

/** The object type of every subject that is an indexed access, as the compiler parsed it:
 * `X["m"]` answers `X`, anything else answers `undefined`. One parse for the whole batch. */
export function subjectReceivers(repoRoot: string, subjects: readonly string[]): (string | undefined)[] {
  if (!subjects.length) return []
  const answer = run({ kind: "subjects", repo: repoRoot, subjects }) as { receivers: (string | null)[] }
  return answer.receivers.map(r => r ?? undefined)
}
