// ESTree engine, independently adapted from foldlab's oxc-engine.mjs at 4005d34f.
// This engine normalizes on its own parser walk, then uses the existing fragment reader.
import { parseSync } from "oxc-parser"
import { Result } from "effect"
import { readEff, readLayer, restoreAll, exprOf, childrenOf, type IrNode, type Expr, type TsStmt } from "../read.ts"
import { decodeEff, type Eff, type LayerTerm, type ServiceKey } from "../eff.gen.ts"
import { atomNames, heads, rows } from "../profile.gen.ts"
import type { Ty } from "../eff.gen.ts"
import type { Package } from "../packages.gen.ts"
import { withTable } from "../read.ts"
import { bindText, isStringList, methodArgs, methodRow, packageByHead, packageByTarget, packageTable } from "./package-rows.ts"
import { foldSql, isRefusal, type Bind, type SqlArg, type SqlPart } from "./sql-fold.ts"

/** The foreign readers read under the canonical package table (`Packages.table`). */
const underTable = <A>(body: () => A): A => withTable(packageTable, body)
import { forms } from "../forms.gen.ts"
import { taxonomy } from "../taxonomy.gen.ts"
import { encodeProgram } from "../wire.gen.ts"
import type { Verdict, RefusalCode, Key, LayerBinding } from "./contract.ts"

interface Node { type: string; [key: string]: unknown }
const isNode = (v: unknown): v is Node => typeof v === "object" && v !== null && typeof Reflect.get(v, "type") === "string"
const node = (n: Node, k: string): Node => isNode(n[k]) ? n[k] : reject("E-NODE", k)
const list = (n: Node, k: string): Node[] => Array.isArray(n[k]) ? n[k].map(v => isNode(v) ? v : reject("E-NODE", k)) : []
const str = (n: Node, k: string): string => typeof n[k] === "string" ? n[k] : reject("E-NODE", k)
const offset = (n: Node, k: string): number => typeof n[k] === "number" ? n[k] : reject("E-NODE", k)
const unwrap = (n: Node): Node => n.type === "ParenthesizedExpression" || n.type === "TSParenthesizedExpression" ? unwrap(node(n, "expression")) : n
class Refuse extends Error { constructor(readonly code: RefusalCode, readonly value: string) { super(code) } }
function reject(code: RefusalCode, value: string): never { throw new Refuse(code, value) }
const id = (name: string): Expr => ({ _tag: "ident", name })
const call = (name: string, args: readonly Expr[]): Expr => ({ _tag: "call", fn: id(name), args })
const admitted = new Set<string>([...heads, ...rows.map(r => r.row.spelling), ...forms.rows.map(r => r.head)])
// The pure atoms are read, not copied (DI-40): `atomNames` above is
// `Effect4.Program.nativeAtom`'s own name list from `profile.gen.ts`, checked at generation
// against `nativeAtomTy`. This engine and `ck.ts` therefore admit the same eleven names.

class Normalize {
  readonly keys: Key[] = []
  readonly layers: LayerBinding[] = []
  private readonly definitions: { sourceName: string; expression: Expr }[] = []
  private referenceCut: number | undefined
  constructor(readonly source: string, readonly bindings: Map<string, string>, readonly declarations: Map<string, Node>, readonly current: number) {}
  finish(program: Eff): Eff {
    if (this.definitions.length === 0) return decodeEff(program)
    const targets = new Map<number, readonly number[]>()
    const definition = (index: number): LayerTerm => {
      const d = this.definitions[index]
      if (!d) return reject("E-REF-UNBOUND", "layer")
      const parsed = underTable(() => readEff(0, call("Effect.provide", [call("Effect.succeed", [{ _tag: "int", value: 0 }]), d.expression])))
      if (Result.isFailure(parsed) || parsed.success._tag !== "provideLayer") return reject("E-NODE", "layer")
      return parsed.success.layer
    }
    const walk = (input: IrNode, path: readonly number[], keys?: Key[]): IrNode => {
      let current = input
      if (!keys && current.sort === "layer" && current.layer._tag === "ref") {
        const ref = current.layer
        if (ref.target.length !== 1) return reject("E-REF-UNBOUND", "layer")
        const index = ref.target[0]!, previous = targets.get(index)
        if (previous) return { sort: "layer", layer: { _tag: "ref", target: previous } }
        targets.set(index, path)
        const d = this.definitions[index]
        if (!d) return reject("E-REF-UNBOUND", "layer")
        const binding = { sourceName: d.sourceName, target: path }
        this.layers.push(binding)
        const result = walk({ sort: "layer", layer: definition(index) }, path)
        if (result.sort === "layer" && result.layer._tag === "ref") {
          targets.set(index, result.layer.target)
          binding.target = result.layer.target
        }
        return result
      }
      const rewriteKey = (key: ServiceKey): ServiceKey => {
        if (!keys) return key
        const old = keys.find(k => k.ordinal === key.name.value)
        if (!old) return reject("E-REF-UNBOUND", "service key")
        let entry = this.keys.find(k => k.sourceId === old.sourceId)
        if (!entry) { entry = { ...old, ordinal: this.keys.length + 4 }; this.keys.push(entry) }
        return { name: { value: entry.ordinal }, service: key.service }
      }
      // Layer constructors expose their key before their body; provision keys follow it.
      if (current.sort === "layer" && (current.layer._tag === "succeed" || current.layer._tag === "effect"))
        current = { sort: "layer", layer: { ...current.layer, key: rewriteKey(current.layer.key) } }
      let order = childrenOf(current).map((_, i) => i)
      if (keys && current.sort === "eff" && current.eff._tag === "provideLayer") order = [1, 0]
      for (const i of order) {
        const child = childrenOf(current)[i]!
        current = child[1](walk(child[0], [...path, i], keys)) ?? reject("E-NODE", "layer path")
      }
      if (current.sort === "eff" && (current.eff._tag === "service" || current.eff._tag === "provideService"))
        current = { sort: "eff", eff: { ...current.eff, key: rewriteKey(current.eff.key) } }
      return current
    }
    const restored = walk({ sort: "eff", eff: program }, [])
    const oldKeys = [...this.keys]
    this.keys.length = 0
    const result = walk(restored, [], oldKeys)
    return result.sort === "eff" ? decodeEff(result.eff) : reject("E-NODE", "program")
  }
  rawHead(n: Node): string {
    n = unwrap(n)
    if (n.type === "Identifier") return str(n, "name")
    if (n.type === "MemberExpression" && !n.computed && !n.optional) return `${this.rawHead(node(n, "object"))}.${str(node(n, "property"), "name")}`
    return reject("E-SPINE-ESCAPE", n.type)
  }
  head(n: Node): string {
    const raw = this.rawHead(n), [root, ...rest] = raw.split(".")
    const b = this.bindings.get(root!)
    if (b === "opaque") return reject("E-IMPORT-OPAQUE", raw)
    if (b !== undefined) return [b, ...rest].filter(Boolean).join(".")
    if (atomNames.has(raw) || forms.lambdas.some(l => l.atom === raw)) return raw
    return reject("E-OP-RECEIVER", raw)
  }
  literal(n: Node): Expr {
    n = unwrap(n)
    if (n.type === "Identifier" && n.name === "undefined") return id("undefined")
    if (n.type === "NewExpression") return reject("E-NODE-SHAPE", "new")
    if (n.type === "AwaitExpression") return reject("E-NODE-SHAPE", "await")
    if (n.type === "TemplateLiteral") return reject("E-NODE-SHAPE", "template")
    if (n.type !== "Literal") return reject("E-ARG-DYNAMIC", "literal")
    if (typeof n.value === "boolean") return { _tag: "bool", value: n.value }
    const raw = this.source.slice(offset(n, "start"), offset(n, "end"))
    if (typeof n.value === "number") {
      if (!/^(0|[1-9][0-9]*)$/.test(raw) || !Number.isSafeInteger(n.value)) return reject("E-ARG-DYNAMIC", "number")
      return { _tag: "int", value: n.value }
    }
    if (typeof n.value === "string") {
      if (raw.slice(1, -1) !== JSON.stringify(n.value).slice(1, -1)) return reject("E-ARG-DYNAMIC", "string")
      return { _tag: "str", value: n.value }
    }
    return reject("E-ARG-DYNAMIC", "literal")
  }
  declaration(n: Node): Node {
    const name = str(n, "name")
    if (this.bindings.has(name)) return reject("E-IMPORT-OPAQUE", name)
    const d = this.declarations.get(name)
    if (!d) return reject("E-REF-UNBOUND", name)
    if (offset(d, "start") >= (this.referenceCut ?? this.current)) return reject("E-REF-FORWARD", name)
    return node(d, d.type === "ClassDeclaration" ? "superClass" : "init")
  }
  /** A package key (spec §5.9, host rows step 5): a member head that resolves through an
   * `effect` import to a package's service, `SqlClient.SqlClient`; never a local declaration. */
  packageOf(n: Node): Package | undefined {
    n = unwrap(n)
    if (n.type !== "MemberExpression" || n.computed || n.optional) return undefined
    let head: string
    try { head = this.head(n) } catch { return undefined }
    return packageByHead.get(head)
  }
  packageKey(pkg: Package): Expr {
    let entry = this.keys.find(k => k.sourceId === pkg.key)
    if (!entry) { entry = { ordinal: this.keys.length + 4, service: pkg.service, sourceId: pkg.key }; this.keys.push(entry) }
    return { _tag: "call", fn: { _tag: "generic", fn: id("Context.Service"), typeArgs: [pkg.target] }, args: [{ _tag: "str", value: `k${entry.ordinal}_${pkg.service}` }] }
  }
  /** A method on a binder, as the printer's fragment (`receiver.spelling(args)`, or
   * `receiver.spelling<T>(args)`), which `read.ts` reads as the table's row under
   * `underTable`; a member the table does not carry is `E-OP-UNKNOWN` (decision 13). */
  methodCall(receiver: number, spelling: string, n: Node, env: readonly string[]): Expr {
    const found = methodRow(spelling)
    if (!found) return reject("E-OP-UNKNOWN", spelling)
    const types = isNode(n.typeArguments) ? list(n.typeArguments, "params").map(t => this.source.slice(offset(t, "start"), offset(t, "end"))) : []
    if (types.join(",") !== found.row.typeArgs.join(",")) return reject("E-OP-UNKNOWN", spelling)
    const { count, types: tys } = methodArgs(found.row), a = list(n, "arguments")
    // rc.112's `unsafe(sql, params?)`: an omitted trailing parameter list is the empty list.
    const omitted = a.length === count - 1 && count > 0 && isStringList(tys[count - 1]!)
    if (a.length !== count && !omitted) return reject("E-BIND-SHAPE", "arity")
    const args = tys.map((ty, i) => i < a.length ? this.rowArgument(a[i]!, ty, env) : call("strings", []))
    const base = id(`a${receiver}`)
    return types.length
      ? { _tag: "call", fn: { _tag: "generic", fn: { _tag: "member", base, name: spelling }, typeArgs: types }, args }
      : { _tag: "method", base, name: spelling, args }
  }
  /** A bind-parameter list is an array literal of bind literals, carried as JSON text through
   * `strings` (DB-15); anything else there, and every other position, is a term. */
  rowArgument(x: Node, ty: Ty, env: readonly string[]): Expr {
    const y = unwrap(x)
    if (isStringList(ty) && y.type === "ArrayExpression") {
      const texts: string[] = []
      for (const e of list(y, "elements")) {
        const z = unwrap(e)
        if (z.type !== "Literal") return reject("E-ARG-DYNAMIC", "bind")
        const v: unknown = z.value
        const text = typeof v === "string" || typeof v === "number" || typeof v === "boolean" || v === null ? bindText(v) : undefined
        if (text === undefined) return reject("E-ARG-DYNAMIC", "bind")
        texts.push(text)
      }
      return call("strings", texts.map(value => ({ _tag: "str" as const, value })))
    }
    return this.term(x, env)
  }
  /** The `sql\`` derived form (spec §5.5) as the printer's fragment of the `unsafe` row on the
   * client binder, `a<i>.unsafe(text, strings(params…))`; the fold is `sql-fold.ts`, shared
   * with the other engine. A generic tag `sql<Row>\`…\`` is the same form. */
  sqlTemplate(receiver: number, tag: string, n: Node, env: readonly string[]): Expr {
    const folded = foldSql(this.sqlParts(n, tag, env))
    if (isRefusal(folded)) return reject(folded.code, folded.detail)
    if (!methodRow("unsafe")) return reject("E-OP-UNKNOWN", "unsafe")
    return { _tag: "method", base: id(`a${receiver}`), name: "unsafe", args: [{ _tag: "str", value: folded.text }, call("strings", folded.params.map(value => ({ _tag: "str" as const, value })))] }
  }
  sqlParts(n: Node, tag: string, env: readonly string[]): SqlPart & { kind: "template" } {
    const q = node(n, "quasi")
    const quasis = list(q, "quasis").map(el => {
      const cooked: unknown = (el as { value?: { cooked?: unknown } }).value?.cooked
      return typeof cooked === "string" ? cooked : reject("E-ARG-DYNAMIC", "template text")
    })
    return { kind: "template", quasis, parts: list(q, "expressions").map(e => this.sqlPart(e, tag, env)) }
  }
  sqlBind(y: Node): Bind | undefined {
    if (y.type !== "Literal") return undefined
    const v: unknown = y.value
    if (typeof v === "string") return v
    if (typeof v === "number") return /^(0|[1-9][0-9]*)$/.test(this.source.slice(offset(y, "start"), offset(y, "end"))) && Number.isSafeInteger(v) ? v : undefined
    if (typeof v === "boolean") return v
    if (v === null) return null
    return undefined
  }
  sqlPart(e: Node, tag: string, env: readonly string[]): SqlPart {
    const y = unwrap(e)
    const value = this.sqlBind(y)
    if (value !== undefined) return { kind: "bind", value }
    if (y.type === "TaggedTemplateExpression") {
      const inner = unwrap(node(y, "tag"))
      return inner.type === "Identifier" && str(inner, "name") === tag ? this.sqlParts(y, tag, env) : { kind: "dynamic", detail: "bind" }
    }
    if (y.type === "CallExpression") {
      const callee = unwrap(node(y, "callee")), a = list(y, "arguments")
      if (callee.type === "MemberExpression" && !callee.computed && str(node(callee, "property"), "name") === "returning" && a.length === 1) {
        return { kind: "returning", base: this.sqlPart(node(callee, "object"), tag, env), value: this.sqlPart(a[0]!, tag, env) }
      }
      if (callee.type === "Identifier" && str(callee, "name") === tag) return { kind: "helper", name: "ident", args: a.map(x => this.sqlArg(x, tag, env)) }
      if (callee.type === "MemberExpression" && !callee.computed) {
        const object = unwrap(node(callee, "object"))
        if (object.type === "Identifier" && str(object, "name") === tag) return { kind: "helper", name: str(node(callee, "property"), "name"), args: a.map(x => this.sqlArg(x, tag, env)) }
      }
    }
    return { kind: "dynamic", detail: "bind" }
  }
  sqlArg(x: Node, tag: string, env: readonly string[]): SqlArg {
    const y = unwrap(x)
    if (y.type === "ArrayExpression") return { kind: "list", items: list(y, "elements").map(el => this.sqlArg(el, tag, env)) }
    if (y.type === "ObjectExpression") {
      const fields: (readonly [string, SqlPart])[] = []
      for (const p of list(y, "properties")) {
        if (p.type !== "Property" || p.computed || p.shorthand || p.method || p.kind !== "init") return { kind: "dynamic", detail: "record key" }
        const k = unwrap(node(p, "key"))
        const key = k.type === "Identifier" ? str(k, "name") : k.type === "Literal" && (typeof k.value === "string" || typeof k.value === "number") ? String(k.value) : undefined
        if (key === undefined) return { kind: "dynamic", detail: "record key" }
        fields.push([key, this.sqlPart(node(p, "value"), tag, env)])
      }
      return { kind: "record", fields }
    }
    return this.sqlPart(x, tag, env)
  }
  key(n: Node): Expr {
    n = unwrap(n)
    const pkg = this.packageOf(n)
    if (pkg) return this.packageKey(pkg)
    if (n.type === "Identifier") n = this.declaration(n)
    if (n.type !== "CallExpression") return reject("E-OP-UNKNOWN", "key")
    const inner = unwrap(node(n, "callee")), factory = inner.type === "CallExpression" ? inner : n
    if (this.head(node(factory, "callee")) !== "Context.Service") return reject("E-OP-UNKNOWN", "key")
    const a = list(n, "arguments")
    if (a.length !== 1) return reject("E-BIND-SHAPE", "arity")
    const types = list(node(factory, "typeArguments"), "params")
    const t = types.at(-1)
    const shape = t ? this.source.slice(offset(t, "start"), offset(t, "end")) : ""
    const packaged = packageByTarget(shape)?.service
    const service = shape === "number" ? 4 : shape === "boolean" ? 5 : shape === "void" || shape === "unknown" ? 6 : shape === "Ref.Ref<number>" ? 7 : packaged !== undefined ? packaged : reject("E-TYPE-PARAM", "service shape")
    const sourceId = this.literal(a[0]!)
    if (sourceId._tag !== "str") return reject("E-ARG-DYNAMIC", "service identifier")
    let entry = this.keys.find(k => k.sourceId === sourceId.value)
    if (!entry) { entry = { ordinal: this.keys.length + 4, service, sourceId: sourceId.value }; this.keys.push(entry) }
    if (entry.service !== service) return reject("E-TYPE-PARAM", "service identity has conflicting shapes")
    return { _tag: "call", fn: { _tag: "generic", fn: id("Context.Service"), typeArgs: [service === 6 ? "void" : shape] }, args: [{ _tag: "str", value: `k${entry.ordinal}_${service}` }] }
  }
  term(n: Node, env: readonly string[]): Expr {
    n = unwrap(n)
    if (n.type === "Identifier" && n.name !== "undefined") {
      const name = str(n, "name"), i = env.lastIndexOf(name)
      return i < 0 ? reject("E-REF-UNBOUND", name) : id(`a${i}`)
    }
    if (n.type === "CallExpression") {
      const fn = unwrap(node(n, "callee"))
      if (fn.type === "Identifier" && env.includes(str(fn, "name"))) return reject("E-ANSWER-HIGHER-ORDER", str(fn, "name"))
      const name = this.head(fn)
      if (!atomNames.has(name)) return reject("E-ARG-DYNAMIC", "term")
      return call(name, list(n, "arguments").map(a => this.term(a, env)))
    }
    return this.literal(n)
  }
  continuation(n: Node, env: readonly string[], count: number, role: "program" | "term" = "program"): Expr {
    n = unwrap(n)
    if (n.type !== "ArrowFunctionExpression") return reject("E-ARG-CLOSURE", "continuation")
    const ps = list(n, "params")
    if (ps.length !== count || ps.some(p => p.type !== "Identifier")) return reject("E-BIND-SHAPE", "parameters")
    const inner = [...env, ...ps.map(p => str(p, "name"))], body = node(n, "body")
    const value = role === "term" ? this.term(body, inner) : this.program(body, inner)
    return count ? { _tag: "lambda", params: ps.map((_, i) => `a${env.length + i}`), body: value } : { _tag: "arrow", body: value }
  }
  fields(n: Node, order?: readonly string[]): readonly (readonly [string, Node])[] {
    n = unwrap(n)
    if (n.type !== "ObjectExpression") return reject("E-BIND-SHAPE", "object")
    const found = new Map<string, Node>()
    for (const p of list(n, "properties")) {
      if (p.type !== "Property" || p.computed || p.method || p.shorthand || p.kind !== "init") return reject("E-SPINE-ESCAPE", "property")
      const k = str(node(p, "key"), "name")
      if (found.has(k)) return reject("E-BIND-SHAPE", "duplicate property")
      found.set(k, node(p, "value"))
    }
    if (!order) return [...found]
    if (found.size !== order.length || order.some(k => !found.has(k))) return reject("E-BIND-SHAPE", "object fields")
    return order.map(k => [k, found.get(k)!] as const)
  }
  duration(n: Node): Expr {
    let amount: string, units = "milli"
    if (unwrap(n).type === "CallExpression") {
      n = unwrap(n)
      const h = this.head(node(n, "callee")), args = list(n, "arguments")
      if (!/^Duration\.(millis|seconds|minutes|hours|days|weeks)$/.test(h) || args.length !== 1) return reject("E-ARG-DYNAMIC", "duration")
      const value = this.literal(args[0]!)
      if (value._tag !== "int") return reject("E-ARG-DYNAMIC", "duration")
      amount = String(value.value); units = h.split(".")[1]!.replace(/s$/, "")
    } else {
      const value = this.literal(n)
      if (value._tag === "int") amount = String(value.value)
      else if (value._tag === "str") {
        const match = /^(-?\d+(?:\.\d+)?)\s+(nanos?|micros?|millis?|seconds?|minutes?|hours?|days?|weeks?)$/.exec(value.value)
        if (!match || match[1]!.startsWith("-")) return reject("E-ARG-DYNAMIC", "duration")
        amount = match[1]!; units = match[2]!.replace(/s$/, "")
      } else return reject("E-ARG-DYNAMIC", "duration")
    }
    const digits = amount.split("."), decimalPlaces = digits[1]?.length ?? 0
    let numerator = BigInt(digits.join("")), denominator = 10n ** BigInt(decimalPlaces)
    switch (units) {
      case "nano": denominator *= 1000000n; break
      case "micro": denominator *= 1000n; break
      case "second": numerator *= 1000n; break
      case "minute": numerator *= 60000n; break
      case "hour": numerator *= 3600000n; break
      case "day": numerator *= 86400000n; break
      case "week": numerator *= 604800000n; break
    }
    if (numerator % denominator !== 0n || numerator / denominator >= 9007199254740992n) return reject("E-ARG-DYNAMIC", "duration")
    return { _tag: "int", value: Number(numerator / denominator) }
  }
  segment(n: Node, first: Expr, env: readonly string[]): Expr {
    n = unwrap(n)
    if (n.type === "ArrowFunctionExpression") {
      const ps = list(n, "params"), body = unwrap(node(n, "body"))
      if (ps.length !== 1 || ps[0]!.type !== "Identifier" || body.type !== "CallExpression") return reject("E-BIND-SHAPE", "eta")
      const parameter = str(ps[0]!, "name"), callee = unwrap(node(body, "callee")), args = list(body, "arguments")
      if (callee.type === "MemberExpression" && !callee.computed && str(node(callee, "property"), "name") === "pipe" && this.rawHead(node(callee, "object")) === parameter) {
        let result = first
        for (const a of args) result = this.segment(a, result, env)
        return result
      }
      if (!args[0] || this.rawHead(args[0]) !== parameter) return reject("E-BIND-SHAPE", "eta")
      const mentions = (v: unknown): boolean => {
        if (Array.isArray(v)) return v.some(mentions)
        if (!isNode(v)) return false
        if ((v.type === "ArrowFunctionExpression" || v.type === "FunctionExpression") && list(v, "params").some(p => p.type === "Identifier" && p.name === parameter)) return false
        if (v.type === "Identifier" && v.name === parameter) return true
        return Object.values(v).some(mentions)
      }
      if (args.slice(1).some(mentions)) return reject("E-BIND-SHAPE", "eta reuse")
      return this.invoke(this.head(callee), args.slice(1), env, first)
    }
    if (n.type === "CallExpression") return this.invoke(this.head(node(n, "callee")), list(n, "arguments"), env, first)
    const h = this.head(n)
    if (!(forms.unaryRefs as readonly string[]).includes(h)) return reject("E-BIND-SHAPE", "unary reference")
    return this.invoke(h, [], env, first)
  }
  invoke(h: string, args: readonly Node[], env: readonly string[], self?: Expr, typeArgs: readonly string[] = []): Expr {
    const length = args.length + (self ? 1 : 0)
    const arg = (i: number): Node => args[i - (self ? 1 : 0)] ?? reject("E-BIND-SHAPE", "arity")
    const arity = (n: number) => { if (length !== n) reject("E-BIND-SHAPE", "arity") }
    const p = (i: number) => self && i === 0 ? self : this.program(arg(i), env)
    const t = (i: number) => this.term(arg(i), env)
    const k = (i: number, count = 1) => this.continuation(arg(i), env, count)
    const bind = (body: Expr) => ({ _tag: "lambda" as const, params: [`a${env.length}`], body })
    if (h === "Effect.map") {
      arity(2); const first = p(0)
      try {
        const fn = this.continuation(arg(1), env, 1, "term")
        if (fn._tag !== "lambda") return reject("E-ARG-CLOSURE", "map")
        return call("Effect.flatMap", [first, { ...fn, body: call("Effect.succeed", [fn.body]) }])
      } catch { return reject("E-ARG-CLOSURE", "map") }
    }
    if (h === "Effect.flatMap" || h === "Effect.catchCause" || h === "Effect.catch" || h === "Effect.onExit") { arity(2); return call(h, [p(0), k(1)]) }
    if (h === "Effect.catchIf") {
      if (length === 4) {
        const fallback = unwrap(arg(3))
        if (fallback.type !== "Identifier" || str(fallback, "name") !== "undefined") return reject("E-BIND-SHAPE", "catchIf fallback")
      } else arity(3)
      const predicate = this.continuation(arg(1), env, 1, "term")
      if (predicate._tag !== "lambda") return reject("E-ARG-CLOSURE", "predicate")
      const test = predicate.body
      if (test._tag === "bool" && test.value) return call("Effect.catch", [p(0), k(2)])
      return call(h, [p(0), predicate, k(2), id("undefined")])
    }
    if (h === "Effect.andThen" || h === "Effect.tap") {
      arity(2); const first = p(0), n = unwrap(arg(1))
      let body: Expr
      if (n.type === "ArrowFunctionExpression" && list(n, "params").length) { const fn = k(1); if (fn._tag !== "lambda") return reject("E-NODE", "continuation"); body = fn.body }
      else body = this.program(n.type === "ArrowFunctionExpression" ? node(n, "body") : n, [...env, "\u0000"])
      if (h === "Effect.tap") body = call("Effect.flatMap", [body, { _tag: "lambda", params: [`a${env.length + 1}`], body: call("Effect.succeed", [id(`a${env.length}`)]) }])
      return call("Effect.flatMap", [first, bind(body)])
    }
    if (h === "Effect.as" || h === "Effect.asVoid") { arity(h === "Effect.as" ? 2 : 1); return call("Effect.flatMap", [p(0), bind(call("Effect.succeed", [h === "Effect.as" ? this.literal(arg(1)) : id("undefined")]))]) }
    if (h === "Effect.ensuring") { arity(2); return call("Effect.onExit", [p(0), bind(this.program(arg(1), [...env, "\u0000"]))]) }
    if (h === "Effect.matchCause" || h === "Effect.matchCauseEffect") {
      arity(2); const first = p(0)
      const m = new Map(this.fields(arg(1), ["onFailure", "onSuccess"]))
      const result = (name: string) => {
        const fn = this.continuation(m.get(name)!, env, 1, h === "Effect.matchCause" ? "term" : "program")
        if (fn._tag !== "lambda") return reject("E-NODE", "match continuation")
        return h === "Effect.matchCause" ? { ...fn, body: call("Effect.succeed", [fn.body]) } : fn
      }
      const onSuccess = result("onSuccess"), onFailure = result("onFailure")
      return call("Effect.matchCauseEffect", [first, { _tag: "object", fields: [["onFailure", onFailure], ["onSuccess", onSuccess]] }])
    }
    if (["Effect.exit", "Effect.uninterruptible", "Effect.interruptible", "Effect.scoped"].includes(h)) { arity(1); return call(h, [p(0)]) }
    if (["Effect.forkChild", "Effect.forkDetach", "Effect.forkScoped", "Effect.forkIn"].includes(h)) {
      const base = h === "Effect.forkIn" ? 2 : 1
      if (length !== base && length !== base + 1) return reject("E-BIND-SHAPE", "arity")
      const values = [p(0)]
      if (base === 2) values.push(t(1))
      const options: Expr = length === base ? { _tag: "object", fields: [["startImmediately", { _tag: "bool", value: false }], ["uninterruptible", { _tag: "str", value: "inherit" }]] } : { _tag: "object", fields: this.fields(arg(base), ["startImmediately", "uninterruptible"]).map(([key, v]) => [key, this.literal(v)] as const) }
      return call(h, [...values, options])
    }
    if (h === "Effect.acquireRelease") {
      arity(2); const first = p(0), n = unwrap(arg(1)), ps = list(n, "params")
      if (n.type !== "ArrowFunctionExpression" || ps.length < 1 || ps.length > 2 || ps.some(p => p.type !== "Identifier")) return reject("E-ARG-CLOSURE", "release")
      const inner = [...env, str(ps[0]!, "name"), ps[1] ? str(ps[1], "name") : "\u0000"]
      return call(h, [first, { _tag: "lambda", params: [`a${env.length}`, `a${env.length + 1}`], body: this.program(node(n, "body"), inner) }])
    }
    if (h === "Effect.provide") {
      if (length !== 2 && length !== 3) return reject("E-BIND-SHAPE", "arity")
      const first = p(0), layer = this.layer(arg(1))
      return call(h, [first, layer, ...(length === 3 ? [{ _tag: "object" as const, fields: this.fields(arg(2), ["local"]).map(([k, v]) => [k, this.literal(v)] as const) }] : [])])
    }
    if (h === "Effect.provideService") {
      arity(3); const first = p(0), key = this.key(arg(1)), value = this.provided(key, arg(2))
      return call(h, [first, key, value])
    }
    if (h === "Effect.suspend") {
      arity(1); const fn = unwrap(arg(0))
      if (fn.type !== "ArrowFunctionExpression" || list(fn, "params").length) return reject("E-ARG-CLOSURE", "suspend")
      const body = unwrap(node(fn, "body"))
      if (body.type === "BlockStatement") return this.loop(body, env)
      const value: Expr = body.type === "ConditionalExpression" ? { _tag: "cond", test: this.term(node(body, "test"), env), thenBranch: this.program(node(body, "consequent"), env), elseBranch: this.program(node(body, "alternate"), env) } : this.program(body, env)
      return call(h, [{ _tag: "arrow", body: value }])
    }
    if (h === "Effect.failCause") { arity(1); return call(h, [this.cause(arg(0), env)]) }
    if (h === "Effect.raceAll") { arity(1); const a = unwrap(arg(0)); if (a.type !== "ArrayExpression") return reject("E-BIND-SHAPE", "entrants"); return call(h, [{ _tag: "arr", items: list(a, "elements").map(x => this.program(x, env)) }]) }
    if (h === "Effect.withFiber") {
      arity(1); const f = unwrap(arg(0)), ss = list(node(f, "body"), "body")
      if (f.type !== "ArrowFunctionExpression" || list(f, "params").length || ss.length !== 2 || ss[0]!.type !== "ExpressionStatement" || ss[1]!.type !== "ReturnStatement") return reject("E-ARG-CLOSURE", "withFiber")
      const c = node(ss[0]!, "expression"), a = list(c, "arguments")
      if (c.type !== "CallExpression" || this.head(node(c, "callee")) !== "Fiber.runIn" || a.length !== 2 || this.head(node(ss[1]!, "argument")) !== "Effect.void") return reject("E-ARG-CLOSURE", "withFiber")
      return call(h, [{ _tag: "arrowBlock", params: [], body: [{ _tag: "exprStmt", value: call("Fiber.runIn", a.map(x => this.term(x, env))) }, { _tag: "ret", value: id("Effect.void") }] }])
    }
    if (["Fiber.join", "Fiber.await", "Fiber.interrupt", "Fiber.interruptAll", "Fiber.awaitAll", "Effect.yieldNowWith"].includes(h)) { arity(1); return call(h, [t(0)]) }
    if (h === "Scope.close" || h === "Fiber.interruptAllAs") { arity(2); return call(h, [t(0), t(1)]) }
    if (h === "Effect.context") { arity(0); return call(h, []) }
    if (h === "Effect.sleep") { arity(1); return call(h, [this.duration(arg(0))]) }
    for (const row of rows.filter(r => r.row.spelling === h)) {
      const requests = row.row.shape === "tupleCall" ? 2 : row.row.request._tag === "unit" ? 0 : 1
      if (length !== requests + row.row.trailing.length) continue
      const trailing: Expr[] = []
      for (let i = requests; i < length; i++) {
        const n = unwrap(arg(i))
        trailing.push(n.type === "ArrowFunctionExpression" ? id(this.lambdaAtom(n)) : n.type === "Literal" ? this.literal(n) : id(this.rawHead(n)))
      }
      if (!row.row.trailing.every((s, i) => { const x = trailing[i]!; return s === (x._tag === "ident" ? x.name : x._tag === "str" ? JSON.stringify(x.value) : "") })) continue
      if (typeArgs.join(",") !== row.row.typeArgs.join(",")) continue
      const fn: Expr = typeArgs.length ? { _tag: "generic", fn: id(h), typeArgs } : id(h)
      return { _tag: "call", fn, args: [...Array.from({ length: requests }, (_, i) => t(i)), ...trailing] }
    }
    return reject(admitted.has(h) ? "E-NODE" : "E-OP-UNKNOWN", h)
  }
  provided(key: Expr, n: Node): Expr {
    const value = this.literal(n)
    if (key._tag !== "call" || key.args[0]?._tag !== "str") return reject("E-NODE", "key")
    const service = Number(key.args[0].value.split("_")[1])
    const actual = value._tag === "int" ? 4 : value._tag === "bool" ? 5 : value._tag === "ident" && value.name === "undefined" ? 6 : -1
    if (service !== actual) return reject("E-ARG-DYNAMIC", "service literal shape")
    return value
  }
  layer(n: Node): Expr {
    n = unwrap(n)
    if (n.type === "Identifier") {
      const sourceName = str(n, "name"), value = this.declaration(n), d = this.declarations.get(sourceName)!
      if (d.declarationKind !== "const") return reject("E-REF-UNBOUND", sourceName)
      const index = this.definitions.findIndex(d => d.sourceName === sourceName)
      if (index >= 0) return id(`L_${index}`)
      const previous = this.referenceCut
      this.referenceCut = offset(d, "start")
      let expression: Expr
      try {
        expression = this.layer(value)
        if (Result.isFailure(underTable(() => readLayer(expression)))) reject("E-NODE", "layer")
      }
      catch (e) { if (e instanceof Refuse) return reject("E-REF-UNBOUND", `${sourceName}: ${e.code}`); throw e }
      finally { this.referenceCut = previous }
      const next = this.definitions.length
      this.definitions.push({ sourceName, expression })
      return id(`L_${next}`)
    }
    if (n.type === "ArrayExpression") return reject("E-OP-UNKNOWN", "Layer.mergeAll")
    if (n.type !== "CallExpression") return reject("E-BIND-SHAPE", "layer")
    const fn = unwrap(node(n, "callee")), a = list(n, "arguments")
    if (fn.type === "MemberExpression" && str(node(fn, "property"), "name") === "pipe") {
      if (a.length !== 1 || a[0]!.type !== "CallExpression") return reject("E-BIND-SHAPE", "layer pipe")
      const h = this.head(node(a[0]!, "callee")), b = list(a[0]!, "arguments")
      if (b.length !== 1) return reject("E-BIND-SHAPE", "layer pipe")
      return { _tag: "method", name: "pipe", base: this.layer(node(fn, "object")), args: [call(h, [this.layer(b[0]!)])] }
    }
    const h = this.head(fn), at = (i: number) => a[i] ?? reject("E-BIND-SHAPE", "arity")
    if (["Layer.succeed", "Layer.effect", "Layer.merge", "Layer.provide", "Layer.provideMerge"].includes(h) && a.length !== 2 ||
        ["Layer.effectDiscard", "Layer.fresh", "Layer.orDie"].includes(h) && a.length !== 1) return reject("E-NODE", "arity")
    if (h === "Layer.succeed") { const key = this.key(at(0)); return call(h, [key, this.provided(key, at(1))]) }
    if (h === "Layer.effect") return call(h, [this.key(at(0)), this.program(at(1), [])])
    if (h === "Layer.effectDiscard") return call(h, [this.program(at(0), [])])
    if (h === "Layer.fresh" || h === "Layer.orDie") return call(h, [this.layer(at(0))])
    if (h === "Layer.merge") return call(h, [this.layer(at(0)), this.layer(at(1))])
    if (h === "Layer.mergeAll") return call(h, a.map(x => this.layer(x)))
    if (h === "Layer.provide" || h === "Layer.provideMerge") return { _tag: "method", name: "pipe", base: this.layer(at(0)), args: [call(h, [this.layer(at(1))])] }
    return reject("E-NODE", "layer")
  }
  cause(n: Node, env: readonly string[]): Expr {
    n = unwrap(n)
    if (n.type !== "CallExpression") return reject("E-FAIL-NOT-DOCUMENTED", "cause")
    const h = this.head(node(n, "callee")), a = list(n, "arguments")
    if (h === "Cause.combine" && a.length === 2) return call(h, a.map(x => this.cause(x, env)))
    if ((h === "Cause.fail" || h === "Cause.die") && a.length === 1 || h === "Cause.interrupt" && a.length <= 1) return call(h, a.map(x => this.term(x, env)))
    return reject("E-FAIL-NOT-DOCUMENTED", "cause")
  }
  loop(n: Node, env: readonly string[]): Expr {
    const ss = list(n, "body"), decl = ss[0], ret = ss[1]
    if (ss.length !== 2 || decl?.type !== "VariableDeclaration" || decl.kind !== "let" || ret?.type !== "ReturnStatement") return reject("E-LOOP", "suspend block")
    const ds = list(decl, "declarations"), d = ds[0]
    if (ds.length !== 1 || !d || node(d, "id").type !== "Identifier") return reject("E-LOOP", "cursor")
    const name = str(node(d, "id"), "name"), inner = [...env, name], c = unwrap(node(ret, "argument")), args = list(c, "arguments")
    if (c.type !== "CallExpression" || this.head(node(c, "callee")) !== "Effect.whileLoop" || args.length !== 1) return reject("E-LOOP", "whileLoop")
    const m = new Map(this.fields(args[0]!, ["while", "body", "step"]))
    const test = this.continuation(m.get("while")!, inner, 0, "term"), body = this.continuation(m.get("body")!, inner, 0)
    const step = unwrap(m.get("step")!), ps = list(step, "params"), block = list(node(step, "body"), "body"), statement = block[0]
    if (ps.length !== 1 || ps[0]!.type !== "Identifier" || block.length !== 1 || statement?.type !== "ExpressionStatement") return reject("E-LOOP", "step")
    const assign = node(statement, "expression")
    if (assign.type !== "AssignmentExpression" || assign.operator !== "=" || this.rawHead(node(assign, "left")) !== name) return reject("E-LOOP", "step assignment")
    const s: Expr = { _tag: "arrowBlock", params: [`a${env.length + 1}`], body: [{ _tag: "assign", name: `a${env.length}`, value: this.term(node(assign, "right"), [...inner, str(ps[0]!, "name")]) }] }
    return call("Effect.suspend", [{ _tag: "arrowBlock", params: [], body: [{ _tag: "letInit", name: `a${env.length}`, value: this.term(node(d, "init"), env) }, { _tag: "ret", value: call("Effect.whileLoop", [{ _tag: "object", fields: [["while", test], ["body", body], ["step", s]] }]) }] }])
  }
  lambdaAtom(n: Node): string {
    const ps = list(n, "params")
    if (ps.length !== 1 || ps[0]!.type !== "Identifier") return reject("E-ARG-CLOSURE", "lambda atom")
    const name = str(ps[0]!, "name"), b = unwrap(node(n, "body"))
    const isParam = (n: Node) => { n = unwrap(n); return n.type === "Identifier" && n.name === name }
    const isNum = (n: Node, v: number) => { n = unwrap(n); return n.type === "Literal" && n.value === v && this.literal(n)._tag === "int" }
    const option = (n: Node, h: string, value?: number): boolean => {
      n = unwrap(n)
      if (n.type !== "CallExpression" || this.head(node(n, "callee")) !== h) return false
      const args = list(n, "arguments")
      return value === undefined ? args.length === 0 : args.length === 1 && isNum(args[0]!, value)
    }
    if (b.type === "BinaryExpression" && isParam(node(b, "left"))) {
      if (b.operator === "+" && isNum(node(b, "right"), 1)) return "incr"
      if (b.operator === "*" && isNum(node(b, "right"), 2)) return "double"
    }
    if (option(b, "Option.none")) return "noChange"
    if (b.type === "ConditionalExpression") {
      const test = unwrap(node(b, "test"))
      if (test.type === "BinaryExpression" && test.operator === ">" && isParam(node(test, "left")) && isNum(node(test, "right"), 0) && option(node(b, "consequent"), "Option.some", 0) && option(node(b, "alternate"), "Option.none")) return "zeroWhenPositive"
    }
    return reject("E-ARG-CLOSURE", "lambda atom")
  }
  program(n: Node, env: readonly string[]): Expr {
    n = unwrap(n)
    if (n.type === "ArrowFunctionExpression" || n.type === "FunctionExpression") return reject(n.typeParameters ? "E-TYPE-PARAM" : "E-PARAM-SHAPE", n.typeParameters ? "generic unit" : "function")
    if (n.type === "ChainExpression") return reject("E-SPINE-ESCAPE", "optional")
    if (["TSAsExpression", "TSSatisfiesExpression", "TSTypeAssertion", "TSNonNullExpression"].includes(n.type)) return reject("E-SPINE-ESCAPE", "assertion")
    if (n.type === "ConditionalExpression") return reject("E-BRANCH", "conditional")
    if (n.type === "Identifier" && !this.bindings.has(str(n, "name"))) {
      const i = env.lastIndexOf(str(n, "name"))
      if (i >= 0 || n.name === "undefined") return this.term(n, env)
      const value = unwrap(this.declaration(n))
      if (value.type === "CallExpression" && this.head(node(value, "callee").type === "CallExpression" ? node(node(value, "callee"), "callee") : node(value, "callee")) === "Context.Service") return call("Effect.service", [this.key(n)])
      const previous = this.referenceCut
      this.referenceCut = offset(this.declarations.get(str(n, "name"))!, "start")
      try { return this.program(value, env) }
      catch (e) { if (e instanceof Refuse) return reject("E-REF-UNBOUND", `${str(n, "name")}: ${e.code}`); throw e }
      finally { this.referenceCut = previous }
    }
    // `sql\`…\`` on a client binder is the derived form; a tag bound to an import refuses with
    // that import's code (drizzle's `sql` is `E-IMPORT-OPAQUE`), any other tag is unresolved.
    if (n.type === "TaggedTemplateExpression") {
      const tag = unwrap(node(n, "tag"))
      if (tag.type === "Identifier") {
        const receiver = env.lastIndexOf(str(tag, "name"))
        if (receiver >= 0) return this.sqlTemplate(receiver, str(tag, "name"), n, env)
      }
      this.head(tag)
      return reject("E-OP-RECEIVER", tag.type === "Identifier" ? str(tag, "name") : "template tag")
    }
    if (n.type !== "CallExpression") {
      if (n.type === "Literal") return this.literal(n)
      // A package key in program position (`yield* SqlClient.SqlClient`) is its service; a
      // property of a binder (`sql.reserve`) is a head the table does not carry.
      const pkg = this.packageOf(n)
      if (pkg) return call("Effect.service", [this.packageKey(pkg)])
      if (n.type === "MemberExpression" && !n.computed) {
        const object = unwrap(node(n, "object"))
        if (object.type === "Identifier" && env.lastIndexOf(str(object, "name")) >= 0) return reject("E-OP-UNKNOWN", str(node(n, "property"), "name"))
      }
      const h = this.head(n)
      return h === "Effect.void" ? call("Effect.succeed", [id("undefined")]) : h === "Effect.yieldNow" ? call("Effect.yieldNowWith", [{ _tag: "int", value: 0 }]) : id(h)
    }
    const callee = unwrap(node(n, "callee")), a = list(n, "arguments")
    if (n.optional || callee.optional) return reject("E-SPINE-ESCAPE", "optional")
    if (a.some(x => x.type === "SpreadElement")) return reject("E-SPINE-ESCAPE", "spread")
    if (callee.type === "MemberExpression" && !callee.computed && str(node(callee, "property"), "name") === "pipe") {
      let value = this.program(node(callee, "object"), env)
      for (const segment of a) value = this.segment(segment, value, env)
      return value
    }
    // A member call on a binder is a method row (or an unknown head); a receiver that is not
    // a binder falls through to head resolution, which refuses it `E-OP-RECEIVER`.
    if (callee.type === "MemberExpression" && !callee.computed) {
      const object = unwrap(node(callee, "object"))
      if (object.type === "Identifier") {
        const receiver = env.lastIndexOf(str(object, "name"))
        if (receiver >= 0) return this.methodCall(receiver, str(node(callee, "property"), "name"), n, env)
      }
    }
    if (callee.type === "CallExpression") {
      if (a.length !== 1) return reject("E-BIND-SHAPE", "arity")
      return this.invoke(this.head(node(callee, "callee")), list(callee, "arguments"), env, this.program(a[0]!, env))
    }
    const h = this.head(callee)
    if (h === "Effect.fn" || h === "Effect.fnUntraced") return reject("E-PARAM-SHAPE", "function")
    if (["Effect.catchTag", "Effect.catchTags", "Effect.mapError", "Effect.match", "Effect.orElseSucceed"].includes(h)) return reject("E-HANDLER", h)
    if (["Effect.promise", "Effect.tryPromise", "Effect.try", "Effect.callback"].includes(h)) return reject("E-ARG-CLOSURE", h)
    if (h === "Effect.whileLoop") return reject("E-LOOP", "whileLoop")
    if (h.startsWith("Cause.") || h.startsWith("Layer.")) return reject("E-NODE", "program fragment")
    if (h === "pipe" || h === "Function.pipe") {
      if (!a[0]) return reject("E-BIND-SHAPE", "arity")
      let value = this.program(a[0], env)
      for (const segment of a.slice(1)) value = this.segment(segment, value, env)
      return value
    }
    const arg = (i: number) => a[i] ?? reject("E-BIND-SHAPE", "arity")
    const arity = (k: number) => { if (a.length !== k) reject("E-BIND-SHAPE", "arity") }
    if (h === "Effect.service") { arity(1); return call(h, [this.key(arg(0))]) }
    if (h === "Effect.succeed") { arity(1); return call(h, [this.term(arg(0), env)]) }
    if (h === "Effect.fail" || h === "Effect.die") {
      arity(1); let value: Expr
      try { value = this.literal(arg(0)) } catch { return reject("E-FAIL-NOT-DOCUMENTED", "literal required") }
      return h === "Effect.fail" ? call(h, [value]) : call("Effect.failCause", [call("Cause.die", [value])])
    }
    if (h === "Effect.provideService") {
      arity(3)
      const body = this.program(arg(0), env), key = this.key(arg(1)), value = this.literal(arg(2))
      if (key._tag !== "call" || key.args[0]?._tag !== "str") return reject("E-NODE", "key")
      const shape = Number(key.args[0].value.split("_")[1]), actual = value._tag === "int" ? 4 : value._tag === "bool" ? 5 : value._tag === "ident" && value.name === "undefined" ? 6 : -1
      if (shape !== actual) return reject("E-ARG-DYNAMIC", "service literal shape")
      return call(h, [body, key, value])
    }
    if (h === "Effect.flatMap" || h === "Effect.catchCause" || h === "Effect.catch" || h === "Effect.onExit") { arity(2); return call(h, [this.program(arg(0), env), this.continuation(arg(1), env, 1)]) }
    if (["Effect.exit", "Effect.uninterruptible", "Effect.interruptible", "Effect.scoped"].includes(h)) { arity(1); return call(h, [this.program(arg(0), env)]) }
    if (h === "Effect.sync") { arity(1); return call(h, [this.continuation(arg(0), env, 0, "term")]) }
    if (h === "Effect.gen") {
      arity(1); const f = unwrap(arg(0))
      if (f.type !== "FunctionExpression" || !f.generator || list(f, "params").length) return reject("E-PARAM-SHAPE", "generator")
      return call(h, [{ _tag: "generator", body: this.statements(list(node(f, "body"), "body"), env) }])
    }
    if (atomNames.has(h)) return this.term(n, env)
    if (!admitted.has(h) && h !== "Effect.map") return reject("E-OP-UNKNOWN", h)
    const types = isNode(n.typeArguments) ? list(n.typeArguments, "params").map(t => this.source.slice(offset(t, "start"), offset(t, "end"))) : []
    return this.invoke(h, a, env, undefined, types)
  }
  statements(ns: readonly Node[], outer: readonly string[]): readonly TsStmt[] {
    const env = [...outer], out: TsStmt[] = []
    for (const n of ns) {
      if (["ForStatement", "ForOfStatement", "ForInStatement"].includes(n.type)) return reject("E-STMT-SHAPE", "for")
      if (n.type === "TryStatement") return reject("E-STMT-SHAPE", "try")
      if (n.type === "VariableDeclaration" && n.kind !== "const") return reject("E-STMT-SHAPE", "let")
      if (n.type === "ReturnStatement") {
        if (!isNode(n.argument)) return reject("E-RETURN-SHAPE", "term")
        if (unwrap(n.argument).type === "YieldExpression") return reject("E-YIELD-POSITION", "return")
        try { out.push({ _tag: "ret", value: this.term(n.argument, env) }) }
        catch (e) { if (e instanceof Refuse && e.code === "E-ANSWER-HIGHER-ORDER") throw e; return reject("E-RETURN-SHAPE", "term") }
        continue
      }
      if (n.type === "VariableDeclaration") {
        const ds = list(n, "declarations"), d = ds[0]
        if (n.kind !== "const" || ds.length !== 1 || !d || node(d, "id").type !== "Identifier") return reject("E-BIND-SHAPE", "binding")
        const y = unwrap(node(d, "init"))
        if (y.type !== "YieldExpression" || !y.delegate) return reject("E-YIELD-POSITION", "binding")
        out.push({ _tag: "constYield", name: `a${env.length}`, value: this.program(node(y, "argument"), env) }); env.push(str(node(d, "id"), "name")); continue
      }
      if (n.type === "ExpressionStatement") {
        const y = unwrap(node(n, "expression"))
        if (y.type !== "YieldExpression" || !y.delegate) return reject("E-STMT-SHAPE", "expression")
        out.push({ _tag: "yieldDiscard", value: this.program(node(y, "argument"), env) }); continue
      }
      if (n.type === "IfStatement") {
        out.push({ _tag: "ifElse", condition: this.term(node(n, "test"), env), thenBranch: this.statements(list(node(n, "consequent"), "body"), env), elseBranch: isNode(n.alternate) ? this.statements(list(n.alternate, "body"), env) : [] }); continue
      }
      if (n.type === "WhileStatement" && node(n, "test").type === "Literal" && node(n, "test").value === true) {
        out.push({ _tag: "whileTrue", body: this.statements(list(node(n, "body"), "body"), env) }); continue
      }
      if (n.type === "BreakStatement" && !n.label) { out.push({ _tag: "breakTo" }); continue }
      return reject("E-STMT-SHAPE", n.type)
    }
    return out
  }
}

const printerStmt = (s: TsStmt): TsStmt => {
  switch (s._tag) {
    case "ifElse": return { ...s, condition: printerOrder(s.condition), thenBranch: s.thenBranch.map(printerStmt), elseBranch: s.elseBranch.map(printerStmt) }
    case "whileTrue": return { ...s, body: s.body.map(printerStmt) }
    case "breakTo": return s
    default: return { ...s, value: printerOrder(s.value) }
  }
}
const printerOrder = (x: Expr): Expr => {
  switch (x._tag) {
    case "object": {
      const fields = x.fields.map(([k, v]) => [k, printerOrder(v)] as const)
      const orders = [["startImmediately", "uninterruptible"], ["onFailure", "onSuccess"], ["while", "body", "step"]]
      const order = orders.find(keys => keys.length === fields.length && keys.every(k => fields.some(([name]) => name === k)))
      return { ...x, fields: order ? order.map(k => fields.find(([name]) => name === k)!) : fields }
    }
    case "call": return { ...x, fn: printerOrder(x.fn), args: x.args.map(printerOrder) }
    case "method": return { ...x, base: printerOrder(x.base), args: x.args.map(printerOrder) }
    case "generic": return { ...x, fn: printerOrder(x.fn) }
    case "arrow": case "lambda": return { ...x, body: printerOrder(x.body) }
    case "arr": return { ...x, items: x.items.map(printerOrder) }
    case "generator": case "arrowBlock": return { ...x, body: x.body.map(printerStmt) }
    case "cond": return { ...x, test: printerOrder(x.test), thenBranch: printerOrder(x.thenBranch), elseBranch: printerOrder(x.elseBranch) }
    default: return x
  }
}

/** Explicit printer-image seam selects the emitted expression; unused module declarations
 * are test context only and never enter the public foreign recognizer through this path. */
export const readPrintedSource = (source: string, filename = "program.ts"): Eff => {
  const parsed = parseSync(filename, source, { lang: "ts", sourceType: "module" })
  if (parsed.errors.length) throw new Error("printer parse")
  const program: unknown = parsed.program
  if (!isNode(program)) throw new Error("printer program")
  const candidates = list(program, "body").flatMap(s => {
    if (s.type === "ExpressionStatement") return [s]
    if (s.type === "ExportNamedDeclaration" && isNode(s.declaration) && s.declaration.type === "VariableDeclaration") return [s.declaration]
    if (s.type === "VariableDeclaration" && list(s, "declarations").some(d => node(d, "id").type === "Identifier" && str(node(d, "id"), "name").startsWith("L_"))) return [s]
    return []
  })
  const constant = (s: Node): Node => {
    if (s.type !== "VariableDeclaration" || s.kind !== "const" || list(s, "declarations").length !== 1) throw new Error("printer declaration")
    const d = list(s, "declarations")[0]!
    if (node(d, "id").type !== "Identifier") throw new Error("printer name")
    return d
  }
  const fragment = (n: Node): Expr => {
    const r = exprOf(n)
    if (Result.isFailure(r)) throw new Error(JSON.stringify(r.failure))
    return printerOrder(r.success)
  }
  const last = candidates.at(-1)
  if (!last) throw new Error("printer program count")
  const declarations: [number[], LayerTerm][] = candidates.slice(0, -1).map(s => {
    const d = constant(s), name = str(node(d, "id"), "name")
    if (!/^L_(0|[1-9][0-9]*)(_(0|[1-9][0-9]*))*$/.test(name)) throw new Error("printer layer path")
    const path = name.slice(2).split("_").map(Number)
    if (!path.every(Number.isSafeInteger)) throw new Error("printer layer path")
    const layer = readLayer(fragment(node(d, "init")))
    if (Result.isFailure(layer)) throw new Error(JSON.stringify(layer.failure))
    return [path, layer.success]
  })
  const r = readEff(0, fragment(last.type === "ExpressionStatement" ? node(last, "expression") : node(constant(last), "init")))
  if (Result.isFailure(r)) throw new Error(JSON.stringify(r.failure))
  const restored = restoreAll(r.success, declarations)
  if (!restored) throw new Error("printer layer target")
  return decodeEff(restored)
}

export function recognizeSource(source: string, filename: string, onParse?: (ok: boolean) => void, onTree?: (tree: unknown) => void): Verdict[] {
  if (!source.includes('from "effect') && !source.includes("from 'effect")) return []
  const parsed = parseSync(filename, source, { lang: filename.endsWith(".tsx") ? "tsx" : "ts", sourceType: "module" })
  if (parsed.errors.length) { onParse?.(false); return [] }
  const tree: unknown = parsed.program
  onParse?.(true)
  onTree?.(tree)
  const bindings = new Map<string, string>()
  for (const imp of parsed.module.staticImports) {
    const mod = imp.moduleRequest.value, base = mod === "effect" ? "" : mod.startsWith("effect/") ? mod.slice(7) : "opaque"
    for (const entry of imp.entries) {
      if (entry.isType) continue
      const name = entry.importName.kind === "Name" ? entry.importName.name : entry.importName.kind === "NamespaceObject" ? "" : "opaque"
      bindings.set(entry.localName.value, base === "opaque" || name === "opaque" ? "opaque" : base === "" && name === "" && entry.localName.value === "Effect" ? "Effect" : [base, name].filter(Boolean).join("."))
    }
  }
  const program: unknown = parsed.program
  if (!isNode(program)) throw new Error("parser returned no program")
  const body = list(program, "body").map(s => s.type === "ExportNamedDeclaration" && isNode(s.declaration) ? s.declaration : s)
  const declarations = new Map<string, Node>()
  for (const s of body) if (s.type === "VariableDeclaration") for (const d of list(s, "declarations")) if (node(d, "id").type === "Identifier" && isNode(d.init)) declarations.set(str(node(d, "id"), "name"), { ...d, declarationKind: s.kind })
  for (const s of body) if (s.type === "ClassDeclaration" && isNode(s.id) && isNode(s.superClass)) declarations.set(str(s.id, "name"), s)
  const result: Verdict[] = []
  for (const s of body) {
    if (s.type !== "VariableDeclaration" || s.kind !== "const") continue
    for (const d of list(s, "declarations")) {
      if (node(d, "id").type !== "Identifier") {
        const names = new Set<string>()
        const collect = (n: Node): void => {
          if (n.type === "Identifier") { names.add(str(n, "name")); return }
          if (n.type === "Property") { collect(node(n, "value")); return }
          for (const v of Object.values(n)) { if (Array.isArray(v)) v.forEach(x => { if (isNode(x)) collect(x) }); else if (isNode(v)) collect(v) }
        }
        collect(node(d, "id"))
        for (const name of names) result.push({ kind: "refusal", unit: { file: filename, name, span: { start: offset(d, "start"), end: offset(d, "end") } }, code: "E-PROGRAM", detail: "program shape: destructured unit" })
        continue
      }
      if (!isNode(d.init)) continue
      const reader = new Normalize(source, bindings, declarations, offset(d, "start")), value = unwrap(d.init)
      if (value.type === "CallExpression") { try { if (reader.head(node(value, "callee")) === "Context.Service") continue } catch { /* Refuse this unit below. */ } }
      try {
        const layer = new Normalize(source, bindings, declarations, offset(d, "start")).layer(value)
        if (Result.isSuccess(readLayer(layer))) continue
      } catch { /* A program or refused declaration remains a unit. */ }
      const unit = { file: filename.replaceAll("\\", "/"), name: str(node(d, "id"), "name"), span: { start: offset(d, "start"), end: offset(d, "end") } }
      try {
        const fragment = reader.program(value, []), r = underTable(() => readEff(0, fragment))
        if (Result.isFailure(r)) reject("E-NODE", r.failure._tag)
        const eff = reader.finish(r.success)
        result.push({ kind: "lifted", unit, eff, keys: reader.keys, layers: reader.layers, wireHex: Buffer.from(encodeProgram(eff)).toString("hex") })
      } catch (e) {
        if (!(e instanceof Refuse)) throw e
        result.push({ kind: "refusal", unit, code: e.code, detail: taxonomy.find(t => t.code === e.code)!.detail.replace("{value}", e.value) })
      }
    }
  }
  let nextEntry = 0
  const entryHeads = new Set(["Effect.runPromise", "Effect.runSync", "Effect.runFork", "Effect.runPromiseExit", "Effect.runSyncExit", "Effect.runCallback"])
  const extra = (name: string, n: Node, forced?: RefusalCode, start = offset(n, "start"), end = offset(n, "end")) => {
    const unit = { file: filename.replaceAll("\\", "/"), name, span: { start, end } }
    if (forced) { result.push({ kind: "refusal", unit, code: forced, detail: taxonomy.find(t => t.code === forced)!.detail.replace("{value}", forced === "E-TYPE-PARAM" ? "generic unit" : "function") }); return }
    const reader = new Normalize(source, bindings, declarations, start)
    try {
      const fragment = reader.program(n, []), r = underTable(() => readEff(0, fragment))
      if (Result.isFailure(r)) reject("E-NODE", r.failure._tag)
      const eff = reader.finish(r.success)
      result.push({ kind: "lifted", unit, eff, keys: reader.keys, layers: reader.layers, wireHex: Buffer.from(encodeProgram(eff)).toString("hex") })
    } catch (e) {
      if (!(e instanceof Refuse)) throw e
      result.push({ kind: "refusal", unit, code: e.code, detail: taxonomy.find(t => t.code === e.code)!.detail.replace("{value}", e.value) })
    }
  }
  const entryCall = (n: Node) => {
    n = unwrap(n)
    if (n.type === "AwaitExpression") n = unwrap(node(n, "argument"))
    if (n.type !== "CallExpression") return
    let h: string
    try { h = new Normalize(source, bindings, declarations, offset(n, "start")).head(node(n, "callee")) } catch { return }
    if (entryHeads.has(h)) for (const a of list(n, "arguments")) extra(`${h}#${nextEntry++}`, a)
  }
  for (const s of body) {
    if (s.type === "ExportDefaultDeclaration") {
      const d = node(s, "declaration")
      extra("default", d, d.type === "FunctionDeclaration" || d.type === "ClassDeclaration" ? d.typeParameters ? "E-TYPE-PARAM" : "E-PARAM-SHAPE" : undefined)
    } else if (s.type === "ExpressionStatement") entryCall(node(s, "expression"))
    else if (s.type === "FunctionDeclaration" || s.type === "ClassDeclaration") {
      const name = isNode(s.id) ? str(s.id, "name") : "default"
      if (s.type === "ClassDeclaration" && isNode(s.superClass)) {
        try {
          const reader = new Normalize(source, bindings, declarations, offset(s, "end")), c = unwrap(s.superClass), inner = node(c, "callee")
          if (c.type === "CallExpression" && reader.head(inner.type === "CallExpression" ? node(inner, "callee") : inner) === "Context.Service") continue
        } catch { /* Non-service classes are parameterized units. */ }
      }
      if (name === "main" && s.type === "FunctionDeclaration") for (const st of list(node(s, "body"), "body")) {
        if (st.type === "ExpressionStatement") entryCall(node(st, "expression"))
        if (st.type === "ReturnStatement" && isNode(st.argument)) entryCall(st.argument)
      }
      extra(name, s, s.typeParameters ? "E-TYPE-PARAM" : "E-PARAM-SHAPE", isNode(s.id) ? offset(s.id, "start") : offset(s, "start"))
    }
  }
  result.sort((a, b) => a.unit.span.start - b.unit.span.start)
  return result
}
