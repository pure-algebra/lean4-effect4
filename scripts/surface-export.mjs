#!/usr/bin/env node
/**
 * The Interface Surface Snapshot of Effect rc.112 (lane L1 of
 * docs/research/2026-09-04-production-standards-spike.md, §2).
 *
 * Usage: node scripts/surface-export.mjs [--ts <dir>] [--out generated] [--src <dir>]
 *
 *   --ts   directory of the `typescript` package to load (classic JS compiler API);
 *          default ts/eff/node_modules/typescript (pinned by ts/eff/package.json).
 *          The repo's own harness/truth/node_modules/typescript is 7.x and may lack the JS API.
 *   --out  output directory, relative to the repository root; default `generated`.
 *   --src  the vendored source tree; default `vendor/effect-4.0.0-rc.112/src`.
 *
 * Emits, deterministically (sorted, LF, UTF-8 without BOM, no timestamps, no absolute paths):
 *   <out>/rc112-surface.tsv          one row per value-level export call signature / member / key
 *   <out>/rc112-surface.json         { meta, summary, rows }
 *   <out>/rc112-surface.summary.txt  the human-readable census
 *
 * Elapsed time is printed to stdout only; it is never written to a file, so two runs
 * produce byte-identical outputs.
 */

import { createHash } from "node:crypto"
import { createRequire } from "node:module"
import { mkdirSync, readdirSync, readFileSync, statSync, writeFileSync } from "node:fs"
import { dirname, join, resolve as presolve, sep } from "node:path"
import { fileURLToPath } from "node:url"

const T0 = Date.now()

// ---------------------------------------------------------------- arguments

const argv = process.argv.slice(2)
if (argv.includes("--help") || argv.includes("-h")) {
  console.log("node scripts/surface-export.mjs [--ts <dir>] [--out generated] [--src <dir>]")
  process.exit(0)
}
const opt = (flag, dflt) => {
  const i = argv.indexOf(flag)
  return i >= 0 && argv[i + 1] !== undefined ? argv[i + 1] : dflt
}

const REPO = presolve(dirname(fileURLToPath(import.meta.url)), "..")
const TS_DIR = opt("--ts", process.env.EFFECT4_TYPESCRIPT_DIR ?? join(REPO, "ts/eff/node_modules/typescript"))
const OUT_DIR = presolve(REPO, opt("--out", "generated"))
const SRC = presolve(REPO, opt("--src", join("vendor", "effect-4.0.0-rc.112", "src")))

const require = createRequire(import.meta.url)
const ts = require(TS_DIR)
const expectedTs = JSON.parse(readFileSync(join(REPO, "ts/eff/package.json"), "utf8")).devDependencies.typescript
if (ts.version !== expectedTs) throw new Error(`TypeScript ${ts.version}; expected ${expectedTs}`)
const sha256 = (bytes) => createHash("sha256").update(bytes).digest("hex")
const inputPins = readFileSync(join(REPO, "vendor/effect-4.0.0-rc.112/SHA256SUMS"), "utf8")
  .trim().split(/\r?\n/).map((line) => {
    const [digest, file] = line.trim().split(/\s+/)
    const actual = sha256(readFileSync(join(SRC, "..", file)))
    if (actual !== digest) throw new Error(`Off-pin input: ${file}`)
    return { file: `vendor/effect-4.0.0-rc.112/${file}`, sha256: digest }
  })
const receipt = {
  format: "rc112-surface-v1", generator: "scripts/surface-export.mjs",
  generatorSha256: sha256(readFileSync(fileURLToPath(import.meta.url))),
  regenerate: "node scripts/surface-export.mjs", typescript: ts.version, inputs: inputPins
}
const receiptLines = [
  `# GENERATED format=${receipt.format}; generator=${receipt.generator}; sha256=${receipt.generatorSha256}`,
  `# regenerate: ${receipt.regenerate}; typescript=${receipt.typescript}`,
  ...inputPins.map((p) => `# input=${p.file} sha256=${p.sha256}`)
].join("\n") + "\n"


const PACKAGE = "effect"
const VERSION = "4.0.0-rc.112"

// ---------------------------------------------------------------- utilities

const posix = (p) => p.split(sep).join("/")
const ws = (t) => String(t ?? "").replace(/\s+/g, " ").trim()
const cap = (t, n) => (t.length > n ? t.slice(0, n) : t)
/** Deterministic, locale-independent code-unit order. */
const cmp = (a, b) => (a < b ? -1 : a > b ? 1 : 0)
const uniq = (xs) => Array.from(new Set(xs)).sort(cmp)

/** Split on a top-level separator, ignoring anything inside brackets. */
function splitTop(text, sep2) {
  const out = []
  let depth = 0
  let cur = ""
  for (const ch of text) {
    if ("<([{".includes(ch)) depth++
    if (">)]}".includes(ch)) depth--
    if (ch === sep2 && depth === 0) {
      out.push(cur.trim())
      cur = ""
    } else cur += ch
  }
  if (cur.trim()) out.push(cur.trim())
  return out
}

/** Syntactic channel extraction (the prototype's `channels`). */
function channels(ret) {
  let m
  ret = ws(ret)
  if ((m = ret.match(/^(?:[A-Za-z_$][\w$]*\.)?Effect<([\s\S]*)>$/))) {
    const a = splitTop(m[1], ",")
    return { kind: "Effect", A: a[0] ?? "", E: a[1] ?? "never", R: a[2] ?? "never" }
  }
  if ((m = ret.match(/^(?:[A-Za-z_$][\w$]*\.)?Layer<([\s\S]*)>$/))) {
    const a = splitTop(m[1], ",")
    return { kind: "Layer", A: a[0] ?? "", E: a[1] ?? "never", R: a[2] ?? "never" }
  }
  if ((m = ret.match(/^(?:[A-Za-z_$][\w$]*\.)?Stream<([\s\S]*)>$/))) {
    const a = splitTop(m[1], ",")
    return { kind: "Stream", A: a[0] ?? "", E: a[1] ?? "never", R: a[2] ?? "never" }
  }
  if ((m = ret.match(/^(?:[A-Za-z_$][\w$]*\.)?Config<([\s\S]*)>$/))) {
    return { kind: "Config", A: splitTop(m[1], ",")[0] ?? "", E: "ConfigError", R: "never" }
  }
  return { kind: "other", A: ret, E: "", R: "" }
}

const SCALARS = new Set(["never", "void", "number", "string", "boolean", "undefined", "null", "bigint", "symbol"])

/** Typing grade of one channel text (the prototype's `isTy`). */
function isTy(t, params) {
  t = ws(t)
  if (SCALARS.has(t)) return "ty"
  if (params.has(t)) return "param"
  const union = splitTop(t, "|")
  if (union.length > 1) {
    const gs = union.map((u) => isTy(u, params))
    return gs.includes("handle") ? "handle" : gs.includes("param") ? "param" : "ty"
  }
  let m
  if ((m = t.match(/^(?:[A-Za-z_$][\w$]*\.)?Option<([\s\S]*)>$/))) return isTy(m[1], params)
  if ((m = t.match(/^(?:ReadonlyArray|Array)<([\s\S]*)>$/))) return isTy(m[1], params)
  if ((m = t.match(/^readonly \[([\s\S]*)\]$/))) {
    const a = splitTop(m[1], ",")
    if (a.length !== 2) return "handle"
    const g = a.map((x) => isTy(x, params))
    return g.includes("handle") ? "handle" : g.includes("param") ? "param" : "ty"
  }
  if (
    (m = t.match(/^(?:[A-Za-z_$][\w$]*\.)?Result<([\s\S]*)>$/)) ||
    (m = t.match(/^(?:[A-Za-z_$][\w$]*\.)?Exit<([\s\S]*)>$/)) ||
    (m = t.match(/^(?:[A-Za-z_$][\w$]*\.)?Fiber<([\s\S]*)>$/))
  ) {
    const a = splitTop(m[1], ",")
    const g = a.map((x) => isTy(x, params))
    return g.includes("handle") ? "handle" : g.includes("param") ? "param" : "ty"
  }
  if ((m = t.match(/^(?:[A-Za-z_$][\w$]*\.)?Cause<([\s\S]*)>$/))) return isTy(m[1], params)
  return "handle"
}

/** Shape of the R (or E) channel text (the prototype's `rShape`). */
function rShape(x, params) {
  x = ws(x)
  if (x === "never") return "never"
  if (/^Exclude</.test(x)) return "Exclude"
  if (splitTop(x, "|").length > 1) return "union"
  if (params.has(x)) return "param"
  if (/^[A-Z][A-Za-z0-9_$.]*(<[\s\S]*>)?$/.test(x)) return "single"
  return "other"
}

/** The census R-class taxonomy: what the combinator does to the channel. */
function rClassOf(before, after) {
  const b = ws(before)
  const a = ws(after)
  if (b === "" || a === "") return ""
  if (a === b) return "neutral"
  if (a === "never") return "closes"
  if (/^Exclude</.test(a) && a.includes(b)) return "discharges"
  const members = splitTop(a, "|")
  if (members.length > 1 && members.some((m) => ws(m) === b)) return "adds"
  if (a.includes(b)) return "transforms"
  return "replaces"
}

const SELF_NAMES = new Set(["self", "effect", "layer", "stream", "config", "sink", "channel"])

const TYPE_NOISE = new Set([
  ...SCALARS,
  "any",
  "unknown",
  "object",
  "readonly",
  "Exclude",
  "Extract",
  "Omit",
  "Pick",
  "NoInfer",
  "Partial",
  "Required",
  "Record",
  "Array",
  "ReadonlyArray",
  "Iterable",
  "keyof",
  "typeof",
  "infer",
  "extends",
  "true",
  "false"
])

/** Best-effort: the service identity strings an R text mentions. */
function keysOfR(rText, params, keyByTypeName) {
  const out = []
  const text = ws(rText)
  for (const m of text.matchAll(/[A-Za-z_$][\w$]*(?:\.[A-Za-z_$][\w$]*)*/g)) {
    const tok = m[0]
    if (TYPE_NOISE.has(tok)) continue
    if (params.has(tok)) continue
    if (!/^[A-Z]/.test(tok.split(".").pop() ?? "")) continue
    // a key in R is a bare identifier; an applied generic (`Layer.Services<…>`) is a helper
    if (text[m.index + tok.length] === "<") continue
    out.push(keyByTypeName.get(tok) ?? keyByTypeName.get(tok.split(".").pop()) ?? tok)
  }
  return uniq(out)
}

// ---------------------------------------------------------------- file walk

function walk(dir, acc) {
  for (const e of readdirSync(dir).sort(cmp)) {
    const p = join(dir, e)
    if (statSync(p).isDirectory()) {
      if (e !== "internal") walk(p, acc)
    } else if (e.endsWith(".ts") && e !== "index.ts") acc.push(p)
  }
  return acc
}

const files = walk(SRC, []).sort(cmp)
const relOf = (f) => posix(f.slice(SRC.length + 1))

function stabilityOf(rel) {
  const segs = rel.split("/")
  if (segs.length === 1) return "stable"
  if (segs[0] === "unstable") return `unstable/${segs[1]}`
  return segs[0]
}

// ---------------------------------------------------------------- program

const compilerOptions = {
  strict: true,
  target: ts.ScriptTarget.ESNext,
  module: ts.ModuleKind.ESNext,
  moduleResolution: ts.ModuleResolutionKind.Bundler,
  noEmit: true,
  skipLibCheck: true,
  allowImportingTsExtensions: true,
  noResolve: false,
  types: [],
  baseUrl: SRC,
  paths: { "effect/*": ["./*.ts"] }
}

const program = ts.createProgram(files, compilerOptions)
const checker = program.getTypeChecker()
const FMT = ts.TypeFormatFlags.NoTruncation | ts.TypeFormatFlags.InTypeAlias

const tstr = (t) => {
  try {
    return ws(checker.typeToString(t, undefined, FMT))
  } catch {
    return ""
  }
}

// module-resolution / syntax health, recorded but never fatal
let unresolvedImports = 0
let syntacticDiagnostics = 0
const unresolvedExamples = []
const resolveCache = new Map()
for (const f of files) {
  const sf = program.getSourceFile(f)
  if (!sf) continue
  syntacticDiagnostics += program.getSyntacticDiagnostics(sf).length
  for (const st of sf.statements) {
    let spec = null
    if (ts.isImportDeclaration(st)) spec = st.moduleSpecifier
    else if (ts.isExportDeclaration(st) && st.moduleSpecifier) spec = st.moduleSpecifier
    if (!spec || !ts.isStringLiteral(spec)) continue
    const ck = `${dirname(f)}\0${spec.text}`
    let r = resolveCache.get(ck)
    if (r === undefined) {
      r = ts.resolveModuleName(spec.text, f, compilerOptions, ts.sys)
      resolveCache.set(ck, r)
    }
    if (!r.resolvedModule) {
      unresolvedImports++
      if (unresolvedExamples.length < 12) unresolvedExamples.push(`${relOf(f)} -> ${spec.text}`)
    }
  }
}
const diagnosticsCount = unresolvedImports + syntacticDiagnostics

// ---------------------------------------------------------------- extraction

const rows = []
const keyRows = []
let exportedStatements = 0
let checkerRows = 0
let syntacticRows = 0
let exportStarSkipped = 0
const untypedByChecker = []

const jsdocOf = (text, node) => {
  const rs = ts.getLeadingCommentRanges(text, node.getFullStart()) ?? []
  let category = ""
  let since = ""
  for (const r of rs) {
    const c = text.slice(r.pos, r.end)
    const mc = c.match(/@category\s+([^\n*]+)/)
    if (mc && !category) category = ws(mc[1])
    const ms = c.match(/@since\s+([^\n*]+)/)
    if (ms && !since) since = ws(ms[1])
  }
  return { category, since }
}

/** The one module each core carrier is declared in, so name collisions do not match. */
const CORE_FILES = new Map([
  ["Effect", posix(join(SRC, "Effect.ts"))],
  ["Layer", posix(join(SRC, "Layer.ts"))],
  ["Stream", posix(join(SRC, "Stream.ts"))],
  ["Config", posix(join(SRC, "Config.ts"))]
])

function declaredInCoreFile(sym, name) {
  const want = CORE_FILES.get(name)
  if (!want) return false
  for (const d of sym.declarations ?? []) {
    if (posix(d.getSourceFile().fileName) === want) return true
  }
  return false
}

/** Structural channel extraction from a checker type. */
function structuralChannels(type) {
  try {
    let sym = type.aliasSymbol
    let args = sym ? type.aliasTypeArguments ?? null : null
    if (!sym) {
      sym = type.getSymbol ? type.getSymbol() : undefined
      const isRef = (type.flags & ts.TypeFlags.Object) !== 0 &&
        ((type.objectFlags ?? 0) & ts.ObjectFlags.Reference) !== 0
      if (isRef) args = checker.getTypeArguments(type)
    }
    const nm = sym && sym.getName ? sym.getName() : null
    if (!nm || !args || !args.length) return null
    if (!declaredInCoreFile(sym, nm)) return null
    if (nm === "Config") return { kind: "Config", A: tstr(args[0]) || "", E: "ConfigError", R: "never" }
    if (nm === "Effect" || nm === "Layer" || nm === "Stream") {
      return {
        kind: nm,
        A: args[0] ? tstr(args[0]) : "",
        E: args[1] ? tstr(args[1]) : "never",
        R: args[2] ? tstr(args[2]) : "never"
      }
    }
    return null
  } catch {
    return null
  }
}

function typeParamNames(list) {
  const out = []
  for (const p of list ?? []) {
    const n = p.symbol ? p.symbol.getName() : p.name ? p.name.getText() : ""
    if (n) out.push(n)
  }
  return out
}

/**
 * Build one row.  `spec` carries everything the columns need; the channel grading,
 * the R-class and the key extraction are shared by the syntactic and checker paths.
 */
function makeRow(spec) {
  const {
    rel,
    stability,
    name,
    sigIndex,
    unit, // "value" | "member" | "key"
    category,
    since,
    line,
    typeSource,
    params,
    dataLast,
    ch, // { kind, A, E, R } or null
    selfCh, // { kind, A, E, R } or null
    hadCallSignatures,
    key,
    keyByTypeName,
    configReads
  } = spec

  const effectful = ch != null && ch.kind !== "other"
  const A = effectful ? cap(ws(ch.A), 200) : ch ? cap(ws(ch.A), 200) : ""
  const E = effectful ? cap(ws(ch.E), 200) : ""
  const R = effectful ? cap(ws(ch.R), 200) : ""

  const gradeA = effectful ? isTy(ch.A, params) : ""
  const gradeE = effectful ? isTy(ch.E, params) : ""
  const gradeR = effectful ? (ws(ch.R) === "never" ? "ty" : rShape(ch.R, params)) : ""
  const gradeRnorm = gradeR === "" ? "" : gradeR === "ty" || gradeR === "never" ? "ty"
    : gradeR === "param" || gradeR === "union" || gradeR === "Exclude" || gradeR === "single" ? "param"
    : "handle"

  let kind
  if (unit === "key") kind = "key"
  else if (effectful) kind = ch.kind
  else if (unit === "member") kind = "member"
  else kind = hadCallSignatures ? "other" : "value"

  let rowGrade
  if (unit === "key") rowGrade = "key"
  else if (effectful) {
    rowGrade = [gradeA, gradeE].includes("handle") || gradeRnorm === "handle"
      ? "handle"
      : [gradeA, gradeE].includes("param") || gradeRnorm === "param"
      ? "param"
      : "ty"
  } else if (unit === "member") rowGrade = "member"
  else rowGrade = hadCallSignatures ? "other" : "value"

  const shape = effectful ? rShape(ch.R, params) : ""
  const rcls = effectful && selfCh && selfCh.kind !== "other" ? rClassOf(selfCh.R, ch.R) : ""
  const ecls = effectful && selfCh && selfCh.kind !== "other" ? rClassOf(selfCh.E, ch.E) : ""

  rows.push({
    file: rel,
    name,
    sigIndex,
    kind,
    stability,
    category,
    since,
    dataLast: dataLast ? "true" : "false",
    A,
    E,
    R,
    gradeA,
    gradeE,
    gradeR: gradeR === "" ? "" : gradeRnorm,
    rowGrade,
    rShape: shape,
    rClass: rcls,
    eClass: ecls,
    scopeInR: effectful && /\bScope\b/.test(ch.R) ? "true" : "false",
    keys: effectful ? keysOfR(ch.R, params, keyByTypeName).join(";") : "",
    configReads,
    keyId: key ? key.keyId : "",
    keyKind: key ? key.keyKind : "",
    hasDefault: key ? (key.hasDefault ? "true" : "false") : "",
    fiberCached: key ? key.fiberCached : "",
    defaultText: key ? key.defaultText : "",
    line,
    typeSource,
    unit
  })
  if (typeSource === "checker") checkerRows++
  else if (typeSource === "syntactic") syntacticRows++
}

// ---- syntactic signature analysis (a node with parameters and a return type)

const isSelfParam = (p) => !!p && ts.isIdentifier(p.name) && SELF_NAMES.has(p.name.text)

/**
 * The curried tail of a data-last signature: a function type taking `self`, or an
 * overloaded object type whose first self-taking call signature we follow.
 */
function curriedTail(node) {
  if (!node) return null
  if (ts.isFunctionTypeNode(node)) return isSelfParam(node.parameters[0]) ? node : null
  if (ts.isTypeLiteralNode(node)) {
    for (const m of node.members) {
      if (ts.isCallSignatureDeclaration(m) && isSelfParam(m.parameters[0])) return m
    }
  }
  return null
}

function analyzeSyntacticSig(sf, sig, extraParams) {
  const params = new Set(extraParams)
  const addTps = (tps) => {
    for (const tp of tps ?? []) params.add(tp.name.getText(sf))
  }
  addTps(sig.typeParameters)
  let dataLast = false
  let selfNode = (sig.parameters ?? []).find(isSelfParam) ?? null
  let retNode = sig.type ?? null
  let hops = 0
  let tail = curriedTail(retNode)
  while (tail && hops < 3) {
    dataLast = true
    addTps(tail.typeParameters)
    selfNode = tail.parameters[0]
    retNode = tail.type ?? null
    hops++
    tail = curriedTail(retNode)
  }
  const ret = retNode ? ws(retNode.getText(sf)) : ""
  const selfType = selfNode && selfNode.type ? ws(selfNode.type.getText(sf)) : ""
  for (const m of ret.matchAll(/\binfer\s+([A-Za-z_$][\w$]*)/g)) params.add(m[1])
  const ch = channels(ret)
  const selfCh = selfType ? channels(selfType) : null
  return { params, dataLast, ch, selfCh }
}

// ---- checker signature analysis

function analyzeCheckerSig(sig) {
  const params = new Set(typeParamNames(sig.getTypeParameters()))
  let retType
  try {
    retType = checker.getReturnTypeOfSignature(sig)
  } catch {
    return null
  }
  let dataLast = false
  let selfType = null
  const selfParam = sig.getParameters().find((p) => SELF_NAMES.has(p.getName()))
  if (selfParam) {
    try {
      selfType = checker.getTypeOfSymbolAtLocation(selfParam, selfParam.valueDeclaration ?? sig.getDeclaration())
    } catch {
      selfType = null
    }
  }
  let inner = null
  try {
    const innerSigs = retType.getCallSignatures()
    if (innerSigs.length === 1) {
      const p0 = innerSigs[0].getParameters()[0]
      if (p0 && SELF_NAMES.has(p0.getName())) inner = innerSigs[0]
    }
  } catch { /* ignore */ }
  if (inner) {
    dataLast = true
    for (const n of typeParamNames(inner.getTypeParameters())) params.add(n)
    const p0 = inner.getParameters()[0]
    try {
      selfType = checker.getTypeOfSymbolAtLocation(p0, p0.valueDeclaration ?? inner.getDeclaration())
    } catch { /* keep */ }
    try {
      retType = checker.getReturnTypeOfSignature(inner)
    } catch { /* keep */ }
  }
  const ch = structuralChannels(retType) ?? channels(tstr(retType))
  const selfCh = selfType ? structuralChannels(selfType) ?? channels(tstr(selfType)) : null
  return { params, dataLast, ch, selfCh }
}

// ---- service-key extraction

const strLit = (n) => (n && ts.isStringLiteral(n) ? n.text : null)

const CONTEXT_FILE = posix(join(SRC, "Context.ts"))

/** true when this name really denotes `Context.Service` / `Context.Reference`. */
function resolvesToContext(node) {
  try {
    let s = checker.getSymbolAtLocation(node)
    if (s && s.flags & ts.SymbolFlags.Alias) s = checker.getAliasedSymbol(s)
    for (const d of s?.declarations ?? []) {
      if (posix(d.getSourceFile().fileName) === CONTEXT_FILE) return true
    }
  } catch { /* fall through */ }
  return false
}

/** Follow `const K = "literal"` inside the same file. */
function literalOfIdentifier(sf, nameText) {
  for (const st of sf.statements) {
    if (!ts.isVariableStatement(st)) continue
    for (const d of st.declarationList.declarations) {
      if (ts.isIdentifier(d.name) && d.name.text === nameText && d.initializer && ts.isStringLiteral(d.initializer)) {
        return d.initializer.text
      }
    }
  }
  return null
}

/**
 * Recognise `Context.Service<Self, Shape>()("id", opts?)`,
 * `Context.Service<Self, Shape>()(id)` and `Context.Reference<T>("id", { defaultValue })`.
 * Returns { keyKind, keyId, hasDefault, fiberCached, defaultText, shapeTypeNode }.
 */
function serviceKeyOf(sf, expr) {
  if (!expr || !ts.isCallExpression(expr)) return null
  // collect the call chain from outermost to innermost
  const chain = []
  let cur = expr
  while (ts.isCallExpression(cur)) {
    chain.push(cur)
    cur = cur.expression
  }
  const headText = ws(cur.getText(sf))
  const m = headText.match(/(?:^|\.)(Service|Reference)$/)
  if (!m) return null
  // the call form `X.Service<Self, Shape>()("id")` is accepted from any module that
  // re-exports Context's constructor (RpcMiddleware.Service and friends).
  const keyKind = m[1] === "Reference" ? "reference" : "service"

  // type arguments live on the innermost call that carries them
  let typeArgs = null
  for (let i = chain.length - 1; i >= 0; i--) {
    if (chain[i].typeArguments && chain[i].typeArguments.length) {
      typeArgs = chain[i].typeArguments
      break
    }
  }
  // the identity string and the options object live on the outermost call with arguments
  let idArg = null
  let optsArg = null
  for (let i = 0; i < chain.length; i++) {
    const args = chain[i].arguments ?? []
    if (args.length) {
      idArg = args[0]
      optsArg = args[1] ?? null
      break
    }
  }
  let keyId = strLit(idArg)
  if (!keyId && idArg && ts.isIdentifier(idArg)) keyId = literalOfIdentifier(sf, idArg.text) ?? idArg.text
  if (!keyId && idArg) keyId = cap(ws(idArg.getText(sf)), 120)

  // options: either the second argument of a Service call or the second of a Reference call
  let hasDefault = false
  let fiberCached = ""
  let defaultText = ""
  const scan = (obj) => {
    if (!obj || !ts.isObjectLiteralExpression(obj)) return
    for (const p of obj.properties) {
      if (!p.name || !ts.isIdentifier(p.name)) continue
      if (p.name.text === "defaultValue" && ts.isPropertyAssignment(p)) {
        hasDefault = true
        defaultText = cap(ws(p.initializer.getText(sf)), 120)
      } else if (p.name.text === "fiberCached" && ts.isPropertyAssignment(p)) {
        const t = ws(p.initializer.getText(sf))
        if (t === "true" || t === "false") fiberCached = t
      }
    }
  }
  scan(optsArg)
  // Context.Reference<T>("id", {...}) has its options in the same call as the id
  const shapeTypeNode = typeArgs ? (keyKind === "reference" ? typeArgs[0] : typeArgs[1] ?? typeArgs[0]) : null
  return { keyKind, keyId: keyId ?? "", hasDefault, fiberCached, defaultText, shapeTypeNode }
}

/** Resolve an expression to the declaration of the value it names. */
function symbolDeclarationOf(node) {
  try {
    let s = checker.getSymbolAtLocation(node)
    if (s && s.flags & ts.SymbolFlags.Alias) s = checker.getAliasedSymbol(s)
    if (!s) return null
    return s.valueDeclaration ?? (s.declarations ?? [])[0] ?? null
  } catch {
    return null
  }
}

/** Read `Context.Service<…>` / `Context.Reference<…>` off a type annotation. */
function annotationKeyOf(dsf, typeNode) {
  if (!typeNode || !ts.isTypeReferenceNode(typeNode)) return null
  const nm = ws(typeNode.typeName.getText(dsf))
  const m = nm.match(/(?:^|\.)(Service|Reference)$/)
  if (!m) return null
  if (nm !== `Context.${m[1]}` && !resolvesToContext(typeNode.typeName)) return null
  const keyKind = m[1] === "Reference" ? "reference" : "service"
  const ta = typeNode.typeArguments ?? []
  const shapeTypeNode = keyKind === "reference" ? ta[0] ?? null : ta[1] ?? ta[0] ?? null
  return { keyKind, shapeTypeNode }
}

/**
 * The service key a declaration denotes, following one or more re-export hops
 * (`export const Clock: Context.Reference<Clock> = effect.ClockRef`).
 */
function keyOfDeclaration(decl, depth = 0) {
  if (!decl || depth > 3) return null
  const dsf = decl.getSourceFile()
  if (ts.isClassDeclaration(decl)) {
    for (const h of decl.heritageClauses ?? []) {
      for (const t of h.types) {
        const k = serviceKeyOf(dsf, t.expression)
        if (k) return k
      }
    }
    return null
  }
  if (!ts.isVariableDeclaration(decl)) return null
  if (decl.initializer) {
    const k = serviceKeyOf(dsf, decl.initializer)
    if (k) return k
  }
  const annot = annotationKeyOf(dsf, decl.type ?? null)
  if (decl.initializer && (ts.isIdentifier(decl.initializer) || ts.isPropertyAccessExpression(decl.initializer))) {
    const target = symbolDeclarationOf(decl.initializer)
    if (target && target !== decl) {
      const k = keyOfDeclaration(target, depth + 1)
      if (k) {
        return annot
          ? { ...k, keyKind: annot.keyKind, shapeTypeNode: annot.shapeTypeNode ?? k.shapeTypeNode }
          : k
      }
    }
  }
  if (annot) {
    return {
      keyKind: annot.keyKind,
      keyId: "",
      hasDefault: annot.keyKind === "reference",
      fiberCached: "",
      defaultText: "",
      shapeTypeNode: annot.shapeTypeNode
    }
  }
  return null
}

/** true when the interface looks like a service shape (members return Effect/Layer/Stream). */
function interfaceIsServiceShape(sf, decl) {
  for (const m of decl.members ?? []) {
    let fnNode = null
    if (ts.isMethodSignature(m)) fnNode = m
    else if (ts.isPropertySignature(m) && m.type && ts.isFunctionTypeNode(m.type)) fnNode = m.type
    if (!fnNode || !fnNode.type) continue
    const c = channels(ws(fnNode.type.getText(sf)))
    if (c.kind === "Effect" || c.kind === "Layer" || c.kind === "Stream") return true
  }
  return false
}

/** All call-signature-bearing members of an interface / class body. */
function callableMembers(sf, decl) {
  const out = []
  for (const m of decl.members ?? []) {
    if (!m.name || !(ts.isIdentifier(m.name) || ts.isStringLiteral(m.name))) continue
    const mname = m.name.text
    if (ts.isMethodSignature(m) || ts.isMethodDeclaration(m)) out.push({ mname, sigs: [m] })
    else if ((ts.isPropertySignature(m) || ts.isPropertyDeclaration(m)) && m.type) {
      if (ts.isFunctionTypeNode(m.type)) out.push({ mname, sigs: [m.type] })
      else if (ts.isTypeLiteralNode(m.type)) {
        const cs = m.type.members.filter((x) => ts.isCallSignatureDeclaration(x))
        if (cs.length) out.push({ mname, sigs: cs })
      }
    }
  }
  return out
}

// ---------------------------------------------------------------- main pass

const configReadsByFile = new Map()
const filesWithConfigReads = []

for (const file of files) {
  const sf = program.getSourceFile(file)
  if (!sf) continue
  const text = sf.getFullText()
  const rel = relOf(file)
  const stability = stabilityOf(rel)
  const lineOf = (n) => sf.getLineAndCharacterOfPosition(n.getStart(sf)).line + 1
  const isExported = (n) => (ts.getCombinedModifierFlags(n) & ts.ModifierFlags.Export) !== 0

  // --- config reads (per file): Config.<prim>("NAME")
  const cfg = new Set()
  const visitCfg = (n) => {
    if (
      ts.isCallExpression(n) &&
      ts.isPropertyAccessExpression(n.expression) &&
      ts.isIdentifier(n.expression.expression) &&
      /Config$/.test(n.expression.expression.text) &&
      n.arguments.length
    ) {
      // the path name is the last string-literal argument:
      // Config.string("host"), Config.schema(schema, "OTEL_RESOURCE_ATTRIBUTES")
      const lits = n.arguments.filter((a) => ts.isStringLiteral(a))
      if (lits.length) cfg.add(lits[lits.length - 1].text)
    }
    ts.forEachChild(n, visitCfg)
  }
  ts.forEachChild(sf, visitCfg)
  const configReads = uniq([...cfg]).join(";")
  configReadsByFile.set(rel, uniq([...cfg]))
  if (cfg.size) filesWithConfigReads.push(rel)

  // --- pass 1: the file's service/reference keys, so R texts can be mapped to identities
  const keyByTypeName = new Map()
  const declaredKeys = [] // { name, node, key }
  const interfaceByName = new Map()
  for (const st of sf.statements) {
    if (ts.isInterfaceDeclaration(st)) interfaceByName.set(st.name.text, st)
  }
  const noteKey = (name, node, key) => {
    declaredKeys.push({ name, node, key })
    if (key.keyId) keyByTypeName.set(name, key.keyId)
  }
  for (const st of sf.statements) {
    if (ts.isExportDeclaration(st) && st.exportClause && ts.isNamedExports(st.exportClause) && !st.isTypeOnly) {
      for (const spec of st.exportClause.elements) {
        if (spec.isTypeOnly) continue
        const target = symbolDeclarationOf(spec.name)
        const k = target ? keyOfDeclaration(target) : null
        if (k) noteKey(spec.name.text, spec, k)
      }
      continue
    }
    if (!isExported(st)) continue
    if (ts.isClassDeclaration(st) && st.name) {
      const k = keyOfDeclaration(st)
      if (k) noteKey(st.name.text, st, k)
    } else if (ts.isVariableStatement(st)) {
      for (const d of st.declarationList.declarations) {
        if (!ts.isIdentifier(d.name)) continue
        const k = keyOfDeclaration(d)
        if (k) noteKey(d.name.text, d, k)
      }
    }
  }

  const base = { rel, stability, keyByTypeName, configReads }

  // --- pass 2: rows
  const emitSyntactic = (name, sigIndex, sigNode, extraParams, meta, unit) => {
    const a = analyzeSyntacticSig(sf, sigNode, extraParams)
    makeRow({
      ...base,
      name,
      sigIndex,
      unit,
      category: meta.category,
      since: meta.since,
      line: meta.line,
      typeSource: "syntactic",
      params: a.params,
      dataLast: a.dataLast,
      ch: a.ch,
      selfCh: a.selfCh,
      hadCallSignatures: true,
      key: null
    })
  }

  const emitFromChecker = (name, node, meta, unit) => {
    let type = null
    try {
      const sym = checker.getSymbolAtLocation(node)
      type = sym ? checker.getTypeOfSymbolAtLocation(sym, node) : checker.getTypeAtLocation(node)
    } catch {
      type = null
    }
    let sigs = []
    try {
      sigs = type ? type.getCallSignatures() : []
    } catch {
      sigs = []
    }
    const asText = type ? tstr(type) : ""
    if (!sigs.length) {
      if (!type || asText === "" || asText === "any" || asText === "error") {
        untypedByChecker.push(`${rel}:${meta.line} ${name}`)
      }
      const ch = type ? structuralChannels(type) ?? channels(asText) : { kind: "other", A: "", E: "", R: "" }
      makeRow({
        ...base,
        name,
        sigIndex: 0,
        unit,
        category: meta.category,
        since: meta.since,
        line: meta.line,
        typeSource: "checker",
        params: new Set(),
        dataLast: false,
        ch,
        selfCh: null,
        hadCallSignatures: false,
        key: null
      })
      return
    }
    sigs.forEach((sig, i) => {
      const a = analyzeCheckerSig(sig)
      if (!a) return
      makeRow({
        ...base,
        name,
        sigIndex: i,
        unit,
        category: meta.category,
        since: meta.since,
        line: meta.line,
        typeSource: "checker",
        params: a.params,
        dataLast: a.dataLast,
        ch: a.ch,
        selfCh: a.selfCh,
        hadCallSignatures: true,
        key: null
      })
    })
  }

  const emitValue = (name, decl, nameNode, typeNode, meta) => {
    if (typeNode && ts.isTypeLiteralNode(typeNode)) {
      const cs = typeNode.members.filter((m) => ts.isCallSignatureDeclaration(m))
      if (cs.length) {
        cs.forEach((m, i) => emitSyntactic(name, i, m, [], meta, "value"))
        return
      }
      // a typed object with no call signature
      const ch = channels(ws(typeNode.getText(sf)))
      makeRow({
        ...base,
        name,
        sigIndex: 0,
        unit: "value",
        category: meta.category,
        since: meta.since,
        line: meta.line,
        typeSource: "syntactic",
        params: new Set(),
        dataLast: false,
        ch,
        selfCh: null,
        hadCallSignatures: false,
        key: null
      })
      return
    }
    if (typeNode && ts.isFunctionTypeNode(typeNode)) {
      emitSyntactic(name, 0, typeNode, [], meta, "value")
      return
    }
    if (typeNode) {
      const ch = channels(ws(typeNode.getText(sf)))
      makeRow({
        ...base,
        name,
        sigIndex: 0,
        unit: "value",
        category: meta.category,
        since: meta.since,
        line: meta.line,
        typeSource: "syntactic",
        params: new Set(),
        dataLast: false,
        ch,
        selfCh: null,
        hadCallSignatures: false,
        key: null
      })
      return
    }
    emitFromChecker(name, nameNode, meta, "value")
  }

  const emitMembers = (ownerName, decl, meta) => {
    for (const { mname, sigs } of callableMembers(sf, decl)) {
      const mMeta = jsdocOf(text, decl.members.find((m) => m.name && m.name.text === mname) ?? decl)
      const mLine = (() => {
        const m = decl.members.find((x) => x.name && x.name.text === mname)
        return m ? lineOf(m) : meta.line
      })()
      sigs.forEach((s, i) =>
        emitSyntactic(
          `${ownerName}.${mname}`,
          i,
          s,
          [],
          {
            category: mMeta.category || meta.category,
            since: mMeta.since || meta.since,
            line: mLine
          },
          "member"
        )
      )
    }
  }

  const serviceShapeInterfaces = new Set()

  for (const st of sf.statements) {
    // ---- named re-exports: export { A, B } [from "..."]
    if (ts.isExportDeclaration(st)) {
      if (!st.exportClause) {
        exportStarSkipped++
        continue
      }
      if (st.isTypeOnly || !ts.isNamedExports(st.exportClause)) continue
      exportedStatements++
      for (const spec of st.exportClause.elements) {
        if (spec.isTypeOnly) continue
        let sym = null
        try {
          sym = checker.getSymbolAtLocation(spec.name)
          if (sym && sym.flags & ts.SymbolFlags.Alias) sym = checker.getAliasedSymbol(sym)
        } catch {
          sym = null
        }
        if (!sym || !(sym.flags & ts.SymbolFlags.Value)) continue
        const meta = { ...jsdocOf(text, spec), line: lineOf(spec) }
        emitFromChecker(spec.name.text, spec.name, meta, "value")
      }
      continue
    }

    if (!isExported(st)) continue
    exportedStatements++
    const meta = { ...jsdocOf(text, st), line: lineOf(st) }

    if (ts.isFunctionDeclaration(st)) {
      if (!st.name) continue
      if (st.type) emitSyntactic(st.name.text, 0, st, [], meta, "value")
      else emitFromChecker(st.name.text, st.name, meta, "value")
      continue
    }

    if (ts.isVariableStatement(st)) {
      for (const d of st.declarationList.declarations) {
        if (!ts.isIdentifier(d.name)) continue
        const dMeta = { ...jsdocOf(text, st), line: lineOf(d) }
        emitValue(d.name.text, d, d.name, d.type ?? null, dMeta)
      }
      continue
    }

    if (ts.isClassDeclaration(st) && st.name) {
      // the class as a value
      emitFromChecker(st.name.text, st.name, meta, "value")
      const mine = declaredKeys.filter((k) => k.name === st.name.text)
      if (mine.length) {
        for (const k of mine) {
          makeRow({
            ...base,
            name: st.name.text,
            sigIndex: 0,
            unit: "key",
            category: meta.category,
            since: meta.since,
            line: meta.line,
            typeSource: "syntactic",
            params: new Set(),
            dataLast: false,
            ch: null,
            selfCh: null,
            hadCallSignatures: false,
            key: k.key
          })
          // service shape members
          const shape = k.key.shapeTypeNode && k.key.shapeTypeNode.getSourceFile() === sf
            ? k.key.shapeTypeNode
            : null
          if (shape && ts.isTypeReferenceNode(shape)) {
            const nm = ws(shape.typeName.getText(sf))
            const iface = interfaceByName.get(nm)
            if (iface && !serviceShapeInterfaces.has(nm)) {
              serviceShapeInterfaces.add(nm)
              emitMembers(nm, iface, { ...jsdocOf(text, iface), line: lineOf(iface) })
            }
          } else if (shape && ts.isTypeLiteralNode(shape)) {
            emitMembers(st.name.text, shape, meta)
          }
        }
        // the class's own body members
        emitMembers(st.name.text, st, meta)
      }
      continue
    }

    if (ts.isInterfaceDeclaration(st)) {
      if (serviceShapeInterfaces.has(st.name.text)) continue
      if (interfaceIsServiceShape(sf, st)) {
        serviceShapeInterfaces.add(st.name.text)
        emitMembers(st.name.text, st, meta)
      }
      continue
    }
  }

  // const-form service keys (the class form is handled above)
  for (const k of declaredKeys) {
    const already = rows.some((r) => r.file === rel && r.name === k.name && r.kind === "key")
    if (already) continue
    const meta = { ...jsdocOf(text, k.node.parent && ts.isVariableDeclarationList(k.node.parent) ? k.node.parent.parent : k.node), line: lineOf(k.node) }
    makeRow({
      ...base,
      name: k.name,
      sigIndex: 0,
      unit: "key",
      category: meta.category,
      since: meta.since,
      line: meta.line,
      typeSource: "syntactic",
      params: new Set(),
      dataLast: false,
      ch: null,
      selfCh: null,
      hadCallSignatures: false,
      key: k.key
    })
    const shape = k.key.shapeTypeNode && k.key.shapeTypeNode.getSourceFile() === sf
      ? k.key.shapeTypeNode
      : null
    if (shape && ts.isTypeReferenceNode(shape)) {
      const nm = ws(shape.typeName.getText(sf))
      const iface = interfaceByName.get(nm)
      if (iface && !serviceShapeInterfaces.has(nm)) {
        serviceShapeInterfaces.add(nm)
        emitMembers(nm, iface, { ...jsdocOf(text, iface), line: lineOf(iface) })
      }
    }
    keyRows.push({ file: rel, name: k.name, ...k.key })
  }
}

// ---------------------------------------------------------------- assemble

const COLUMNS = [
  "file",
  "name",
  "sigIndex",
  "kind",
  "stability",
  "category",
  "since",
  "dataLast",
  "A",
  "E",
  "R",
  "gradeA",
  "gradeE",
  "gradeR",
  "rowGrade",
  "rShape",
  "rClass",
  "eClass",
  "scopeInR",
  "keys",
  "configReads",
  "keyId",
  "keyKind",
  "hasDefault",
  "fiberCached",
  "defaultText",
  "line",
  "typeSource"
]

// dedupe on (file, name, sigIndex, kind) and sort
const seen = new Set()
const finalRows = []
rows.sort(
  (a, b) =>
    cmp(a.file, b.file) || cmp(a.name, b.name) || a.sigIndex - b.sigIndex || cmp(a.kind, b.kind) ||
    cmp(a.rowGrade, b.rowGrade) || a.line - b.line
)
for (const r of rows) {
  const k = `${r.file}\u0000${r.name}\u0000${r.sigIndex}\u0000${r.kind}`
  if (seen.has(k)) continue
  seen.add(k)
  finalRows.push(r)
}

const cell = (v) => String(v ?? "").replace(/[\t\r\n]+/g, " ")
const tsv = [COLUMNS.join("\t"), ...finalRows.map((r) => COLUMNS.map((c) => cell(r[c])).join("\t"))].join("\n") + "\n"

const count = (arr, f) => {
  const m = new Map()
  for (const r of arr) {
    const k = f(r)
    m.set(k, (m.get(k) ?? 0) + 1)
  }
  return Object.fromEntries([...m.entries()].sort((a, b) => b[1] - a[1] || cmp(a[0], b[0])))
}

const effectfulKinds = new Set(["Effect", "Layer", "Stream", "Config"])
const effectful = finalRows.filter((r) => effectfulKinds.has(r.kind))
const memberRows = finalRows.filter((r) => r.unit === "member")
const valueRows = finalRows.filter((r) => r.unit === "value")
const keyOnly = finalRows.filter((r) => r.unit === "key")
const stabilities = uniq(finalRows.map((r) => r.stability))

const perStability = {}
for (const s of stabilities) {
  perStability[s] = count(finalRows.filter((r) => r.stability === s), (r) => r.rowGrade)
}

const WEAK = new Set(["any", "unknown", "error", "{}", ""])
const weakChecker = finalRows
  .filter((r) => r.typeSource === "checker" && WEAK.has(r.A))
  .map((r) => `${r.file}:${r.line} ${r.name} = ${r.A || "<empty>"}`)
  .sort(cmp)

const configFiles = {}
for (const f of uniq(filesWithConfigReads)) configFiles[f] = configReadsByFile.get(f)

const summary = {
  files: files.length,
  exportedStatements,
  rows: finalRows.length,
  rowsByKind: count(finalRows, (r) => r.kind),
  rowsByUnit: { value: valueRows.length, member: memberRows.length, key: keyOnly.length },
  effectfulRows: effectful.length,
  dataLastRows: finalRows.filter((r) => r.dataLast === "true").length,
  rowGradeOverall: count(finalRows, (r) => r.rowGrade),
  rowGradeEffectful: count(effectful, (r) => r.rowGrade),
  rowGradePerStability: perStability,
  rShape: count(effectful.filter((r) => r.rShape !== ""), (r) => r.rShape),
  rClass: count(effectful.filter((r) => r.rClass !== ""), (r) => r.rClass),
  eClass: count(effectful.filter((r) => r.eClass !== ""), (r) => r.eClass),
  scopeInR: effectful.filter((r) => r.scopeInR === "true").length,
  keysByKind: count(keyOnly, (r) => r.keyKind),
  referencesWithDefault: keyOnly.filter((r) => r.keyKind === "reference" && r.hasDefault === "true").length,
  servicesWithDefault: keyOnly.filter((r) => r.keyKind === "service" && r.hasDefault === "true").length,
  keysFiberCached: keyOnly.filter((r) => r.fiberCached === "true").length,
  configReadFiles: configFiles,
  configReadNames: uniq([...Object.values(configFiles).flat()]).length,
  typeSource: count(finalRows, (r) => r.typeSource),
  checkerRows: finalRows.filter((r) => r.typeSource === "checker").length,
  syntacticRows: finalRows.filter((r) => r.typeSource === "syntactic").length,
  rowsBeforeDedupe: rows.length,
  untypedByCheckerCount: untypedByChecker.length,
  untypedByCheckerExamples: untypedByChecker.slice(0, 3),
  checkerWeakTypeCount: weakChecker.length,
  checkerWeakTypeExamples: weakChecker.slice(0, 3),
  exportStarSkipped,
  unresolvedImports,
  syntacticDiagnostics,
  diagnosticsCount
}

const meta = { package: PACKAGE, version: VERSION, ...receipt }

// stable JSON key order: `meta`, `summary`, `rows`; rows use COLUMNS order.
const jsonRows = finalRows.map((r) => {
  const o = {}
  for (const c of COLUMNS) o[c] = c === "sigIndex" || c === "line" ? Number(r[c]) : String(r[c] ?? "")
  return o
})
// one row per line: stable key order, small enough to commit and to diff
const json = [
  "{",
  `  "meta": ${JSON.stringify(meta)},`,
  `  "summary": ${JSON.stringify(summary, null, 2).split("\n").join("\n  ")},`,
  `  "rows": [`,
  ...jsonRows.map((r, i) => `    ${JSON.stringify(r)}${i === jsonRows.length - 1 ? "" : ","}`),
  "  ]",
  "}"
].join("\n") + "\n"

// ---------------------------------------------------------------- summary text

const pad = (o) => Object.entries(o).map(([k, v]) => `${k}=${v}`).join(" ")
const lines = []
lines.push(`Effect rc.112 interface surface snapshot`)
lines.push(`package ${PACKAGE} version ${VERSION} generator scripts/surface-export.mjs`)
lines.push(``)
lines.push(`files ${summary.files}; exported statements ${summary.exportedStatements}; rows ${summary.rows}`)
lines.push(`rows by kind: ${pad(summary.rowsByKind)}`)
lines.push(`rows by unit: ${pad(summary.rowsByUnit)}`)
lines.push(`effectful rows ${summary.effectfulRows}; data-last rows ${summary.dataLastRows}; Scope in R ${summary.scopeInR}`)
lines.push(``)
lines.push(`row grade (all rows): ${pad(summary.rowGradeOverall)}`)
lines.push(`row grade (effectful): ${pad(summary.rowGradeEffectful)}`)
for (const s of stabilities) lines.push(`row grade [${s}]: ${pad(summary.rowGradePerStability[s])}`)
lines.push(``)
lines.push(`R shape: ${pad(summary.rShape)}`)
lines.push(`R class: ${pad(summary.rClass)}`)
lines.push(`E class: ${pad(summary.eClass)}`)
lines.push(``)
lines.push(`keys by kind: ${pad(summary.keysByKind)}`)
lines.push(
  `references with defaultValue ${summary.referencesWithDefault}; services with defaultValue ${summary.servicesWithDefault}; fiberCached ${summary.keysFiberCached}`
)
lines.push(``)
lines.push(`files reading Config.<prim>("NAME") (${Object.keys(configFiles).length}), ${summary.configReadNames} distinct names:`)
for (const [f, names] of Object.entries(configFiles)) lines.push(`  ${f}: ${names.join(";")}`)
lines.push(``)
lines.push(
  `type source: ${pad(summary.typeSource)} (rows before dedupe ${summary.rowsBeforeDedupe}; emitted checker ${checkerRows}, syntactic ${syntacticRows})`
)
lines.push(`declarations the checker could not type: ${summary.untypedByCheckerCount}`)
for (const e of summary.untypedByCheckerExamples) lines.push(`  ${e}`)
lines.push(`checker rows whose type is any/unknown/error/{}: ${summary.checkerWeakTypeCount}`)
for (const e of summary.checkerWeakTypeExamples) lines.push(`  ${e}`)
lines.push(`export * statements skipped: ${summary.exportStarSkipped}`)
lines.push(`diagnostics: unresolved imports ${unresolvedImports}, syntactic ${syntacticDiagnostics}, total ${diagnosticsCount}`)
const summaryText = lines.join("\n") + "\n"

// ---------------------------------------------------------------- write

mkdirSync(OUT_DIR, { recursive: true })
const write = (name, body) => writeFileSync(join(OUT_DIR, name), body, { encoding: "utf8" })
write("rc112-surface.tsv", receiptLines + tsv)
write("rc112-surface.json", json)
write("rc112-surface.summary.txt", receiptLines + summaryText)

process.stdout.write(summaryText)
process.stdout.write(`\nunresolved import examples: ${unresolvedExamples.slice(0, 6).join(", ")}\n`)
process.stdout.write(`elapsed ${((Date.now() - T0) / 1000).toFixed(1)}s (not written to any file)\n`)
