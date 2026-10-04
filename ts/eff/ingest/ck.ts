// Compiler-reading engine, retargeted from foldlab experiments/lift-harness/src/lift.ts at
// 4005d34f. Syntax recognition is independent of read.ts and the oxc engine's walk; derived
// forms consume the shared Lean-owned template fold.
//
// The tree (decisions row 168, route (C), seat J2): this engine walked `typescript@5.9.2`'s
// `createSourceFile` tree. tsgo 7 is the one TypeScript compiler, its API serves source files to
// node only, and this engine runs in bun workers, so it reads the ingest's one parse entry
// (`parseTypeScript`, oxc-parser 0.147.0) and keeps its own walk. Every rule below is the rule it
// had, read off the ESTree the way the TypeScript AST held the same source:
// - a statement under `export`/`export default` is the declaration, exported, whose first token
//   is the wrapper's (`Top`); `export default <expression>` is the export assignment;
// - `unwrap` strips parentheses, and a `ChainExpression` wrapper, which TypeScript does not
//   have: its chain elements carry `optional` where TypeScript carried `questionDotToken`;
// - TypeScript's `NodeFlags.Const` is `const` and `await using`; a parameter is named when its
//   pattern is an identifier with or without a default or a rest marker; an array hole is
//   TypeScript's `OmittedExpression`; `a = b` is an `AssignmentExpression`;
// - `pos` (a declaration's place for the forward-reference cut) is `start`: both orders agree,
//   because no token lies inside another node's leading trivia.
// What the change costs (receipt J2): both engines now read one parse, so the gate tests two
// walks over one tree, not two parsers.
import type { ArrayExpression, Class, Directive, Expression, ExportDefaultDeclarationKind, Function as FunctionNode, FunctionBody, Node as TreeNode, NumericLiteral, ParamPattern, PrivateFieldExpression, Program, SpreadElement, Statement, StaticMemberExpression, StringLiteral, TemplateElement, TSInterfaceDeclaration, TSTupleElement, TSType, VariableDeclaration } from "oxc-parser"
import { childNodes, parseTypeScript } from "./oxc.ts"
import { decodeEff, type Eff, type Term, type Lit, type CauseTerm, type Stmt, type ActionTerm, type LayerTerm, type ServiceKey, type ForkOptions } from "../eff.gen.ts"
import { rows, serviceTypes, serviceTypeFor } from "../profile.gen.ts"
import { readTypeMetadata } from "../metadata.ts"
import { readTupleIndex } from "../tuple-index.ts"
import { targetType, legacyType, recordKeyForm, quoteType } from "../target-types.ts"
import type { Expr } from "../read.ts"

class Decline extends Error {}
const bad = (reason: string): never => { throw new Decline(reason) }
const unit: Term = { _tag: "lit", value: { _tag: "unit" } }

/** An array hole (`[a, , b]`): TypeScript's `OmittedExpression`, a position no rule admits. */
interface Hole { readonly type: "Hole"; readonly start: number; readonly end: number }
const hole: Hole = { type: "Hole", start: -1, end: -1 }
/** An expression position: an expression, a spread argument or an array hole. */
type Ex = Expression | SpreadElement | Hole
const elementsOf = (a: ArrayExpression): readonly Ex[] => a.elements.map(e => e ?? hole)
const isTrue = (x: Ex): boolean => x.type === "Literal" && x.value === true
const isFalse = (x: Ex): boolean => x.type === "Literal" && x.value === false
const isNull = (x: Ex): boolean => x.type === "Literal" && x.value === null && !("regex" in x)
const isNumeric = (x: Ex): x is NumericLiteral => x.type === "Literal" && typeof x.value === "number"
const isString = (x: Ex): x is StringLiteral => x.type === "Literal" && typeof x.value === "string"
/** TypeScript's `NodeFlags.Const`: `const`, and `await using` (whose flags are `Const | Using`). */
const constLike = (d: VariableDeclaration): boolean => d.kind === "const" || d.kind === "await using"
/** TypeScript's `isIdentifier(parameter.name)`: an identifier pattern, with or without a default
 * (`x = 1`) or a rest marker (`...x`). */
const parameterName = (p: ParamPattern): string | undefined => {
  if (p.type === "TSParameterProperty") return parameterName(p.parameter)
  const name = p.type === "AssignmentPattern" ? p.left : p.type === "RestElement" ? p.argument : p
  return name.type === "Identifier" ? name.name : undefined
}
/** A non-computed member's name as TypeScript spells it: a private name keeps its `#`. */
const memberName = (m: StaticMemberExpression | PrivateFieldExpression): string => m.property.type === "PrivateIdentifier" ? "#" + m.property.name : m.property.name
/** A template part's text as TypeScript cooks it. TypeScript keeps an invalid escape of a tagged
 * template raw inside the cooked text; oxc reports no cooked text then, so the raw text stands in. */
const templateText = (q: TemplateElement): string => q.value.cooked ?? q.value.raw

/** A top-level statement as the TypeScript AST holds it: a declaration under `export` or
 * `export default` is the declaration itself, exported, whose first token (`getStart`) is the
 * wrapper's or a decorator's; everything else is itself. */
interface Top { readonly node: Directive | Statement; readonly first: number; readonly exported: boolean }
const isDefaultDeclaration = (d: ExportDefaultDeclarationKind): d is FunctionNode | Class | TSInterfaceDeclaration =>
  d.type === "FunctionDeclaration" || d.type === "TSDeclareFunction" || d.type === "ClassDeclaration" || d.type === "TSInterfaceDeclaration"
const firstToken = (wrapper: { readonly start: number }, d: Statement): number => {
  const decorators: unknown = Reflect.get(d, "decorators")
  const starts = Array.isArray(decorators) ? decorators.map(x => Number(Reflect.get(x, "start"))) : []
  return Math.min(wrapper.start, d.start, ...starts)
}
const topLevel = (program: Program): readonly Top[] => program.body.map((s): Top => {
  if (s.type === "ExportNamedDeclaration" && s.declaration) return { node: s.declaration, first: firstToken(s, s.declaration), exported: true }
  if (s.type === "ExportDefaultDeclaration" && isDefaultDeclaration(s.declaration)) return { node: s.declaration, first: firstToken(s, s.declaration), exported: true }
  return { node: s, first: s.start, exported: false }
})

// Printed identifiers encode paths in canonical decimal. Never parse a rounded Nat.
const layerPath = (name: string): readonly number[] => {
  if (!/^L_(0|[1-9][0-9]*)(_(0|[1-9][0-9]*))*$/.test(name)) return bad("layer name")
  const path = name.slice(2).split("_").map(Number)
  return path.every(Number.isSafeInteger) ? path : bad("layer path")
}

// The seven Program.Refs.Node sorts, walked independently of the OXC reader.
// Paths follow the cons spines; key order keeps provision bodies before providers.
function walkProgram(program: Eff, onLayer: (l: LayerTerm, path: readonly number[]) => LayerTerm,
    onKey: (k: ServiceKey) => ServiceKey = k => k, keyOrder = false): Eff {
  const spine = <T>(items: readonly T[], path: readonly number[], visit: (x: T, p: readonly number[]) => T): readonly T[] =>
    items.map((x, i) => visit(x, [...path, ...Array<number>(i).fill(1), 0]))
  const layer = (input: LayerTerm, path: readonly number[]): LayerTerm => {
    const l = onLayer(input, path), child = (i: number) => [...path, i]
    switch (l._tag) {
      case "succeed": return { ...l, key: onKey(l.key) }
      case "effect": return { ...l, key: onKey(l.key), body: eff(l.body, child(0)) }
      case "effectDiscard": return { ...l, body: eff(l.body, child(0)) }
      case "merge": return { ...l, left: layer(l.left, child(0)), right: layer(l.right, child(1)) }
      case "provide": case "provideMerge": return { ...l, self: layer(l.self, child(0)), that: layer(l.that, child(1)) }
      case "fresh": case "orDie": return { ...l, inner: layer(l.inner, child(0)) }
      case "mergeAll": return { ...l, layers: spine(l.layers, child(0), layer) }
      case "ref": return l
    }
  }
  const stmt = (s: Stmt, path: readonly number[]): Stmt => {
    const child = (i: number) => [...path, i]
    switch (s._tag) {
      case "bindYield": case "yieldDiscard": return { ...s, effect: eff(s.effect, child(0)) }
      case "ifElse": return { ...s, thenB: spine(s.thenB, child(0), stmt), elseB: spine(s.elseB, child(1), stmt) }
      case "whileTrue": return { ...s, body: spine(s.body, child(0), stmt) }
      default: return s
    }
  }
  const action = (a: ActionTerm, path: readonly number[]): ActionTerm => {
    if (a._tag === "fork" || a._tag === "forkIn" || a._tag === "forkScoped") return { ...a, program: eff(a.program, [...path, 0]) }
    if (a._tag === "raceAll") return { ...a, entrants: spine(a.entrants, [...path, 0], eff) }
    return a
  }
  const eff = (e: Eff, path: readonly number[]): Eff => {
    const child = (i: number) => [...path, i]
    switch (e._tag) {
      case "suspend": case "exit": case "uninterruptible": case "interruptible": case "iterate": case "scoped":
        return { ...e, body: eff(e.body, child(0)) }
      case "bind": return { ...e, first: eff(e.first, child(0)), rest: eff(e.rest, child(1)) }
      case "gen": return { ...e, body: spine(e.body, child(0), stmt) }
      case "catchIf":
      case "catchCause": return { ...e, body: eff(e.body, child(0)), handler: eff(e.handler, child(1)) }
      case "matchCause": return { ...e, body: eff(e.body, child(0)), onValue: eff(e.onValue, child(1)), onCause: eff(e.onCause, child(2)) }
      case "onExit": return { ...e, body: eff(e.body, child(0)), finalizer: eff(e.finalizer, child(1)) }
      case "select": return { ...e, arm0: eff(e.arm0, child(0)), arm1: eff(e.arm1, child(1)) }
      case "withFiber": return { ...e, action: action(e.action, child(0)) }
      case "acquireRelease": return { ...e, acquire: eff(e.acquire, child(0)), release: eff(e.release, child(1)) }
      case "provideLayer": {
        if (!keyOrder) return { ...e, layer: layer(e.layer, child(0)), body: eff(e.body, child(1)) }
        const body = eff(e.body, child(1))
        return { ...e, body, layer: layer(e.layer, child(0)) }
      }
      case "service": return { ...e, key: onKey(e.key) }
      case "provideService": {
        const body = eff(e.body, child(0))
        return { ...e, body, key: onKey(e.key) }
      }
      default: return e
    }
  }
  return eff(program, [])
}

function restoreLayer(program: Eff, target: readonly number[], replacement: LayerTerm): Eff {
  let found = false
  const result = walkProgram(program, (layer, path) => {
    if (path.length !== target.length || !path.every((n, i) => n === target[i])) return layer
    found = true
    return replacement
  })
  return found ? result : bad("module path")
}

class CompilerReader {
  constructor(readonly source: string) {}
  /** DI-72 (`763187e1`): a bare value (a literal, `undefined`, a binder) or an application of a
   * name that is no head and no row is no program, and the fragment reader refuses it (`shape`,
   * `unknownHead`). The oxc engine meets it in its second phase, after the whole unit's walk, so
   * any refusal of the walk comes first; this reader keeps the walk as it was (the value read as
   * `fail`) and records the first such position, and `settle` refuses it where the oxc engine
   * reads the fragment: at a unit's end, at the layer probe, at a referenced layer. Until seat
   * J2's step 1b this engine lifted these units. */
  deferred: string | undefined
  defer(reason: string): void { this.deferred ??= reason }
  settle(): void { if (this.deferred !== undefined) bad(this.deferred) }
  /** The node's text, `getText` of the TypeScript AST: its tokens without leading trivia. */
  text(x: { readonly start: number; readonly end: number }): string { return this.source.slice(x.start, x.end) }
  unwrap(x: Ex): Ex {
    while (x.type === "ParenthesizedExpression" || x.type === "ChainExpression") x = x.expression
    return x
  }
  name(x: Ex): string {
    x = this.unwrap(x)
    if (x.type === "Identifier") return x.name
    if (x.type === "MemberExpression" && !x.computed && !x.optional) return `${this.name(x.object)}.${memberName(x)}`
    return bad("head")
  }
  call(x: Ex) {
    x = this.unwrap(x)
    return x.type === "CallExpression" && !x.optional ? x : bad("call")
  }
  arity(args: readonly Ex[], n: number): void { if (args.length !== n) bad("arity") }
  at(args: readonly Ex[], i: number): Ex { return args[i] ?? bad("argument") }
  variable(x: Ex, env: readonly string[]): number | undefined {
    x = this.unwrap(x)
    const i = x.type === "Identifier" ? env.lastIndexOf(x.name) : -1
    return i < 0 ? undefined : i
  }
  literal(x: Ex): Lit {
    x = this.unwrap(x)
    if (isTrue(x)) return { _tag: "bool", value: true }
    if (isFalse(x)) return { _tag: "bool", value: false }
    if (x.type === "Identifier" && x.name === "undefined") return { _tag: "unit" }
    if (isNumeric(x) && Number.isSafeInteger(x.value)) return { _tag: "nat", value: x.value }
    if (isString(x)) return { _tag: "str", value: x.value }
    return bad("literal")
  }
  /** Independent source walk for the printed record forms. The shared metadata decoder
   * validates data after this walk; foreign admission retains its existing profile. */
  metadata(x: Ex): Expr {
    x = this.unwrap(x)
    if (x.type === "ArrayExpression") return { _tag: "arr", items: elementsOf(x).map(item => this.metadata(item)) }
    if (isNumeric(x) && Number.isSafeInteger(x.value) && x.value >= 0) return { _tag: "int", value: x.value }
    if (isString(x)) return { _tag: "str", value: x.value }
    if (isTrue(x) || isFalse(x)) return { _tag: "bool", value: isTrue(x) }
    return bad("metadata expression")
  }
  recordEntries(x: Ex): { keys: "plain" | "quoted" | "computed"; entries: Array<{ name: string; value: Ex } | { spread: Ex }> } {
    x = this.unwrap(x)
    if (x.type !== "ObjectExpression") return bad("record object")
    let keys: "plain" | "quoted" | "computed" | undefined
    const entries: Array<{ name: string; value: Ex } | { spread: Ex }> = []
    for (const property of x.properties) {
      if (property.type === "SpreadElement") { entries.push({ spread: property.argument }); continue }
      if (property.kind !== "init" || property.method || property.shorthand) return bad("record property")
      const key = property.key
      const form = property.computed ? "computed" : key.type === "Identifier" ? "plain" : "quoted"
      const name = key.type === "Identifier" && !property.computed ? key.name :
        key.type === "Literal" && typeof key.value === "string" ? key.value : bad("record key")
      if (keys !== undefined && keys !== form) return bad("record key forms")
      keys = form; entries.push({ name, value: property.value })
    }
    return { keys: keys ?? "plain", entries }
  }
  recordTerm(x: Ex, env: readonly string[]): Term | undefined {
    if (x.type !== "CallExpression" || x.optional) return undefined
    const fn = this.unwrap(x.callee)
    if (fn.type === "Identifier" && x.typeArguments && ["recordValue", "recordRaw"].includes(fn.name)) {
      const raw = fn.name === "recordRaw", types = x.typeArguments.params
      this.arity(x.arguments, raw ? 3 : 2)
      if (types.length !== 1) return bad("record type arguments")
      const declared = readTypeMetadata(this.metadata(this.at(x.arguments, 0)))
      if (declared?._tag !== "record") return bad("record metadata")
      const expected = targetType(declared, legacyType)
      let names: string[], values: readonly Ex[]
      if (raw) {
        const supplied = this.unwrap(this.at(x.arguments, 1)), children = this.unwrap(this.at(x.arguments, 2))
        if (this.text(types[0]!) !== "unknown" || supplied.type !== "ArrayExpression" || children.type !== "ArrayExpression") return bad("raw record frame")
        names = elementsOf(supplied).map(value => isString(value) ? value.value : bad("record supplied name"))
        values = elementsOf(children)
        if (names.length === values.length && expected !== undefined) return bad("unnecessary raw record frame")
      } else {
        const object = this.recordEntries(this.at(x.arguments, 1))
        names = []; const children: Ex[] = []
        for (const entry of object.entries) {
          if ("spread" in entry) return bad("record construction spread")
          names.push(entry.name); children.push(entry.value)
        }
        values = children
        if (expected === undefined || this.text(types[0]!) !== expected || object.keys !== recordKeyForm(names)) return bad("record annotation or keys")
      }
      return { _tag: "record", fields: declared.fields, presentNames: names, values: values.map(value => this.term(value, env)) }
    }
    const update = fn.type === "CallExpression" ? this.unwrap(fn.callee) : undefined
    if (update?.type === "CallExpression" && update.callee.type === "Identifier" && update.callee.name === "recordSet") {
      if (fn.type !== "CallExpression" || fn.optional || update.optional || x.typeArguments || fn.typeArguments ||
          !update.typeArguments || update.typeArguments.params.length !== 1) return bad("record update arguments")
      this.arity(x.arguments, 1); this.arity(fn.arguments, 1); this.arity(update.arguments, 1)
      const key = this.at(update.arguments, 0)
      if (!isString(key) || this.text(update.typeArguments.params[0]!) !== quoteType(key.value)) return bad("record update key")
      return { _tag: "recordSet", target: this.term(this.at(fn.arguments, 0), env), name: key.value, value: this.term(this.at(x.arguments, 0), env) }
    }
    if (fn.type !== "CallExpression" || fn.optional || !fn.typeArguments || fn.callee.type !== "Identifier") return undefined
    const head = fn.callee.name
    if (head !== "recordRequired" && head !== "recordOptional") return undefined
    if (x.typeArguments || fn.typeArguments.params.length !== 1) return bad("record field type arguments")
    this.arity(x.arguments, 1); this.arity(fn.arguments, 1)
    const key = this.at(fn.arguments, 0)
    if (!isString(key) || this.text(fn.typeArguments.params[0]!) !== quoteType(key.value)) return bad("record field key")
    return { _tag: "field", mode: head === "recordRequired" ? "required" : "optional", target: this.term(this.at(x.arguments, 0), env), name: key.value }
  }
  tupleTerm(x: Ex, env: readonly string[]): Term | undefined {
    if (x.type !== "CallExpression" || x.optional) return undefined
    const marker = this.unwrap(x.callee)
    if (marker.type !== "CallExpression" || marker.optional || marker.callee.type !== "Identifier" ||
        marker.callee.name !== "tupleAt" || !marker.typeArguments) return undefined
    if (x.typeArguments || marker.typeArguments.params.length !== 1) return bad("tuple index type arguments")
    this.arity(x.arguments, 1); this.arity(marker.arguments, 1)
    const key = this.at(marker.arguments, 0)
    if (!isString(key) || this.text(marker.typeArguments.params[0]!) !== quoteType(key.value)) return bad("tuple index marker")
    const index = readTupleIndex(key.value)
    if (index === undefined) return bad("tuple index outside canonical safe-natural profile")
    return { _tag: "tupleAt", target: this.term(this.at(x.arguments, 0), env), index }
  }
  term(x: Ex, env: readonly string[]): Term {
    x = this.unwrap(x)
    const i = this.variable(x, env)
    if (i !== undefined) return { _tag: "var", index: i }
    const tuple = this.tupleTerm(x, env)
    if (tuple !== undefined) return tuple
    const record = this.recordTerm(x, env)
    if (record !== undefined) return record
    if (x.type === "CallExpression") return { _tag: "app", atom: this.name(x.callee), args: x.arguments.map(a => this.term(a, env)) }
    return { _tag: "lit", value: this.literal(x) }
  }
  arrow(x: Ex, env: readonly string[], count: number): { body: FunctionBody | Expression; env: readonly string[] } {
    x = this.unwrap(x)
    if (x.type !== "ArrowFunctionExpression" || x.params.length !== count) return bad("closure")
    const names = x.params.map(p => parameterName(p) ?? bad("parameter"))
    return { body: x.body, env: [...env, ...names] }
  }
  expression(x: FunctionBody | Expression): Expression { return x.type === "BlockStatement" ? bad("block") : x }
  fields(x: Ex): Map<string, Ex> {
    x = this.unwrap(x)
    if (x.type !== "ObjectExpression") return bad("object")
    const out = new Map<string, Ex>()
    for (const p of x.properties) {
      if (p.type !== "Property" || p.kind !== "init" || p.method || p.shorthand || p.computed || p.key.type !== "Identifier" || out.has(p.key.name)) return bad("property")
      out.set(p.key.name, p.value)
    }
    return out
  }
  field(m: Map<string, Ex>, k: string): Ex { return m.get(k) ?? bad(`field ${k}`) }
  key(x: Ex): ServiceKey {
    const c = this.call(x)
    if (this.name(c.callee) !== "Context.Service" || c.arguments.length !== 1) return bad("key")
    const v = this.literal(this.at(c.arguments, 0))
    if (v._tag !== "str") return bad("key name")
    const m = /^k(0|[1-9][0-9]*)_(0|[1-9][0-9]*)$/.exec(v.value)
    if (!m) return bad("key number")
    const name = Number(m[1]), service = Number(m[2])
    return { name: { value: name }, service: { value: service } }
  }
  cause(x: Ex, env: readonly string[]): CauseTerm {
    const c = this.call(x), h = this.name(c.callee), a = c.arguments
    if (h === "Cause.fail" || h === "Cause.die") {
      this.arity(a, 1); const t = this.term(this.at(a, 0), env)
      return h === "Cause.fail" ? { _tag: "fail", error: t } : { _tag: "die", defect: t }
    }
    if (h === "Cause.interrupt" && a.length <= 1) return { _tag: "interrupt", interruptor: a.length ? this.term(this.at(a, 0), env) : null }
    if (h === "Cause.combine") { this.arity(a, 2); return { _tag: "both", left: this.cause(this.at(a, 0), env), right: this.cause(this.at(a, 1), env) } }
    return bad("cause")
  }
  options(x: Ex, daemon: boolean): ForkOptions {
    const m = this.fields(x), s = this.literal(this.field(m, "startImmediately")), u = this.literal(this.field(m, "uninterruptible"))
    if (m.size !== 2 || s._tag !== "bool") return bad("fork options")
    const maskMode = u._tag === "bool" ? (u.value ? "uninterruptible" : "interruptible") : u._tag === "str" && u.value === "inherit" ? "inherit" : bad("mask")
    return { startImmediately: s.value, daemon, maskMode }
  }
  layer(x: Ex): LayerTerm {
    x = this.unwrap(x)
    if (x.type === "Identifier") return { _tag: "ref", target: layerPath(x.name) }
    const c = this.call(x)
    const callee = this.unwrap(c.callee)
    if (callee.type === "MemberExpression" && !callee.computed && memberName(callee) === "pipe") {
      this.arity(c.arguments, 1)
      const segment = this.call(this.at(c.arguments, 0)), h = this.name(segment.callee)
      this.arity(segment.arguments, 1)
      const self = this.layer(callee.object), that = this.layer(this.at(segment.arguments, 0))
      if (h === "Layer.provide") return { _tag: "provide", self, that }
      if (h === "Layer.provideMerge") return { _tag: "provideMerge", self, that }
      return bad("layer pipe")
    }
    const h = this.name(c.callee), a = c.arguments
    switch (h) {
      case "Layer.succeed": this.arity(a, 2); return { _tag: "succeed", key: this.key(this.at(a, 0)), value: this.literal(this.at(a, 1)) }
      case "Layer.effect": this.arity(a, 2); return { _tag: "effect", key: this.key(this.at(a, 0)), body: this.eff(this.at(a, 1), []) }
      case "Layer.effectDiscard": this.arity(a, 1); return { _tag: "effectDiscard", body: this.eff(this.at(a, 0), []) }
      case "Layer.merge": this.arity(a, 2); return { _tag: "merge", left: this.layer(this.at(a, 0)), right: this.layer(this.at(a, 1)) }
      case "Layer.mergeAll": return { _tag: "mergeAll", layers: a.map(l => this.layer(l)) }
      case "Layer.provide": case "Layer.provideMerge": this.arity(a, 2); return { _tag: h === "Layer.provide" ? "provide" : "provideMerge", self: this.layer(this.at(a, 0)), that: this.layer(this.at(a, 1)) }
      case "Layer.fresh": case "Layer.orDie": this.arity(a, 1); return { _tag: h === "Layer.fresh" ? "fresh" : "orDie", inner: this.layer(this.at(a, 0)) }
      default: return bad("layer")
    }
  }
  stmts(input: readonly (Directive | Statement)[], initial: readonly string[]): readonly Stmt[] {
    let env = [...initial]
    const out: Stmt[] = []
    for (const s of input) {
      if (s.type === "VariableDeclaration" && constLike(s)) {
        const d = s.declarations[0]
        if (s.declarations.length !== 1 || !d || d.id.type !== "Identifier" || !d.init) return bad("binding")
        const y = this.unwrap(d.init)
        if (y.type !== "YieldExpression" || !y.delegate || !y.argument) return bad("yield binding")
        out.push({ _tag: "bindYield", effect: this.eff(y.argument, env) }); env.push(d.id.name)
      } else if (s.type === "ExpressionStatement") {
        const y = this.unwrap(s.expression)
        if (y.type !== "YieldExpression" || !y.delegate || !y.argument) return bad("yield statement")
        out.push({ _tag: "yieldDiscard", effect: this.eff(y.argument, env) })
      } else if (s.type === "ReturnStatement" && s.argument) out.push({ _tag: "ret", value: this.term(s.argument, env) })
      else if (s.type === "BreakStatement" && !s.label) out.push({ _tag: "breakLoop" })
      else if (s.type === "IfStatement") {
        const thenS = s.consequent, elseS = s.alternate
        if (thenS.type !== "BlockStatement" || (elseS && elseS.type !== "BlockStatement")) return bad("if body")
        out.push({ _tag: "ifElse", test: this.term(s.test, env), thenB: this.stmts(thenS.body, env), elseB: elseS && elseS.type === "BlockStatement" ? this.stmts(elseS.body, env) : [] })
      } else if (s.type === "WhileStatement" && isTrue(this.unwrap(s.test)) && s.body.type === "BlockStatement") {
        out.push({ _tag: "whileTrue", body: this.stmts(s.body.body, env) })
      } else return bad("statement")
    }
    return out
  }
  recordSelect(x: Ex, env: readonly string[]): Eff | undefined {
    if (x.type !== "CallExpression" || x.optional || x.typeArguments || x.callee.type !== "Identifier" || x.callee.name !== "caseTagR") return undefined
    this.arity(x.arguments, 4)
    const tag = this.at(x.arguments, 1)
    if (!isString(tag)) return bad("record decision tag")
    const hit = this.arrow(this.at(x.arguments, 2), env, 1)
    const miss = this.arrow(this.at(x.arguments, 3), env, 1)
    return { _tag: "select", scrutinee: this.term(this.at(x.arguments, 0), env), decision: { _tag: "recordTag", tag: tag.value },
      arm0: this.eff(this.expression(hit.body), hit.env), arm1: this.eff(this.expression(miss.body), miss.env) }
  }
  eff(x: Ex, env: readonly string[]): Eff {
    x = this.unwrap(x)
    const selected = this.recordSelect(x, env)
    if (selected !== undefined) return selected
    // DI-72: the three positions `deferred` names; the walk reads them as it did.
    const variable = this.variable(x, env)
    if (variable !== undefined) { this.defer("shape"); return { _tag: "fail", error: { _tag: "var", index: variable } } }
    if (x.type !== "CallExpression") {
      if (x.type === "Identifier" || x.type === "MemberExpression" && !x.computed) {
        const h = this.name(x)
        if (h === "Effect.fiberId") return { _tag: "withFiber", action: { _tag: "getId" } }
        const row = rows.find(r => r.row.spelling === h && r.row.shape === "value")
        if (row) return { _tag: "perform", op: row.op, request: unit }
      }
      const t = this.term(x, env)
      if (t._tag === "lit") this.defer("shape")
      return { _tag: "fail", error: t }
    }
    const h = this.name(x.callee), a = x.arguments
    const arg = (i: number) => this.at(a, i)
    const e = (i: number) => this.eff(arg(i), env)
    const t = (i: number) => this.term(arg(i), env)
    const k = (i: number, count = 1) => { const fn = this.arrow(arg(i), env, count); return this.eff(this.expression(fn.body), fn.env) }
    switch (h) {
      case "Effect.succeed": this.arity(a, 1); return { _tag: "succeed", value: t(0) }
      case "Effect.fail": this.arity(a, 1); return { _tag: "fail", error: t(0) }
      case "Effect.failCause": this.arity(a, 1); return { _tag: "failCause", cause: this.cause(arg(0), env) }
      case "Effect.sync": { this.arity(a, 1); const fn = this.arrow(arg(0), env, 0); return { _tag: "sync", thunk: this.term(this.expression(fn.body), fn.env) } }
      case "Effect.suspend": {
        this.arity(a, 1); const fn = this.arrow(arg(0), env, 0)
        if (fn.body.type === "BlockStatement") return this.loop(fn.body, env)
        const b = this.unwrap(fn.body)
        if (b.type === "ConditionalExpression") return { _tag: "select", scrutinee: this.term(b.test, env), decision: { _tag: "bool" }, arm0: this.eff(b.consequent, env), arm1: this.eff(b.alternate, env) }
        return { _tag: "suspend", body: this.eff(b, env) }
      }
      case "Effect.flatMap": this.arity(a, 2); return { _tag: "bind", first: e(0), rest: k(1) }
      case "Effect.catchCause": this.arity(a, 2); return { _tag: "catchCause", body: e(0), handler: k(1) }
      case "Effect.catch": this.arity(a, 2); return { _tag: "catchIf", test: { _tag: "lit", value: { _tag: "bool", value: true } }, body: e(0), handler: k(1) }
      case "Effect.catchIf": {
        this.arity(a, 4)
        const predicate = this.arrow(arg(1), env, 1)
        const value = this.unwrap(this.expression(predicate.body))
        if (this.name(arg(3)) !== "undefined" || isTrue(value)) return bad("noncanonical catchIf")
        return { _tag: "catchIf", test: this.term(value, predicate.env), body: e(0), handler: k(2) }
      }
      case "Effect.onExit": this.arity(a, 2); return { _tag: "onExit", body: e(0), finalizer: k(1) }
      case "Effect.acquireRelease": this.arity(a, 2); return { _tag: "acquireRelease", acquire: e(0), release: k(1, 2) }
      case "Effect.gen": {
        this.arity(a, 1); const fn = this.unwrap(arg(0))
        if (fn.type !== "FunctionExpression" || !fn.generator || fn.params.length || !fn.body) return bad("generator")
        return { _tag: "gen", body: this.stmts(fn.body.body, env) }
      }
      case "Effect.matchCauseEffect": {
        this.arity(a, 2); const m = this.fields(arg(1)); if (m.size !== 2) return bad("match fields")
        const failure = this.arrow(this.field(m, "onFailure"), env, 1), success = this.arrow(this.field(m, "onSuccess"), env, 1)
        return { _tag: "matchCause", body: e(0), onValue: this.eff(this.expression(success.body), success.env), onCause: this.eff(this.expression(failure.body), failure.env) }
      }
      case "Effect.exit": case "Effect.uninterruptible": case "Effect.interruptible": case "Effect.scoped": {
        this.arity(a, 1); const tag = h === "Effect.exit" ? "exit" : h === "Effect.scoped" ? "scoped" : h === "Effect.interruptible" ? "interruptible" : "uninterruptible"
        return { _tag: tag, body: e(0) }
      }
      case "Effect.yieldNowWith": { this.arity(a, 1); const l = this.literal(arg(0)); return l._tag === "nat" ? { _tag: "yieldNow", priority: l.value } : bad("priority") }
      case "Effect.service": this.arity(a, 1); return { _tag: "service", key: this.key(arg(0)) }
      case "Effect.provideService": this.arity(a, 3); return { _tag: "provideService", body: e(0), key: this.key(arg(1)), value: t(2) }
      case "Effect.provide": {
        if (a.length !== 2 && a.length !== 3) return bad("provide")
        if (a.length === 3) { const m = this.fields(arg(2)), l = this.literal(this.field(m, "local")); if (m.size !== 1 || l._tag !== "bool" || !l.value) return bad("local") }
        return { _tag: "provideLayer", body: e(0), layer: this.layer(arg(1)), isLocal: a.length === 3 }
      }
      case "Fiber.join": case "Fiber.await": this.arity(a, 1); return { _tag: "awaitFiber", fiber: t(0), mode: h === "Fiber.join" ? "joinEffect" : "awaitValue" }
      case "Effect.forkChild": case "Effect.forkDetach": this.arity(a, 2); return { _tag: "withFiber", action: { _tag: "fork", program: e(0), options: this.options(arg(1), h === "Effect.forkDetach") } }
      case "Effect.forkScoped": this.arity(a, 2); return { _tag: "withFiber", action: { _tag: "forkScoped", program: e(0), options: this.options(arg(1), true) } }
      case "Effect.forkIn": this.arity(a, 3); return { _tag: "withFiber", action: { _tag: "forkIn", program: e(0), scope: t(1), options: this.options(arg(2), true) } }
      case "Fiber.interrupt": this.arity(a, 1); return { _tag: "withFiber", action: { _tag: "interrupt", target: t(0) } }
      case "Fiber.interruptAll": case "Fiber.interruptAllAs": this.arity(a, h === "Fiber.interruptAll" ? 1 : 2); return { _tag: "withFiber", action: { _tag: "interruptAll", targets: t(0), interruptor: a.length === 1 ? null : t(1) } }
      case "Fiber.awaitAll": this.arity(a, 1); return { _tag: "withFiber", action: { _tag: "awaitAll", targets: t(0) } }
      case "Effect.context": this.arity(a, 0); return { _tag: "withFiber", action: { _tag: "getContext" } }
      case "Scope.close": this.arity(a, 2); return { _tag: "withFiber", action: { _tag: "closeScope", scope: t(0), exit: t(1) } }
      case "Effect.raceAll": { this.arity(a, 1); const list = this.unwrap(arg(0)); if (list.type !== "ArrayExpression") return bad("entrants"); return { _tag: "withFiber", action: { _tag: "raceAll", entrants: elementsOf(list).map(y => this.eff(y, env)) } } }
      case "Effect.withFiber": {
        this.arity(a, 1); const fn = this.arrow(arg(0), env, 0)
        if (fn.body.type !== "BlockStatement" || fn.body.body.length !== 2) return bad("runIn callback")
        const [link, ret] = fn.body.body
        if (!link || link.type !== "ExpressionStatement" || !ret || ret.type !== "ReturnStatement" || !ret.argument || this.name(ret.argument) !== "Effect.void") return bad("runIn body")
        const c = this.call(link.expression); this.arity(c.arguments, 2)
        if (this.name(c.callee) !== "Fiber.runIn") return bad("runIn head")
        return { _tag: "withFiber", action: { _tag: "runIn", target: this.term(this.at(c.arguments, 0), env), scope: this.term(this.at(c.arguments, 1), env) } }
      }
    }
    const trailingName = (z: Ex): string | undefined => { z = this.unwrap(z); return isString(z) ? JSON.stringify(z.value) : z.type === "Identifier" ? z.name : undefined }
    for (const r of rows.filter(r => r.row.spelling === h && r.row.shape !== "value")) {
      const count = r.row.shape === "tupleCall" ? 2 : r.row.request._tag === "unit" ? 0 : 1
      if (a.length !== count + r.row.trailing.length || !r.row.trailing.every((v, i) => trailingName(arg(count + i)) === v)) continue
      const types = x.typeArguments?.params.map(n => this.text(n)) ?? []
      if (types.join(",") !== r.row.typeArgs.join(",")) continue
      let request = unit
      if (count === 1) request = t(0)
      if (count === 2) {
        const left = t(0), right = t(1)
        const x0 = this.unwrap(arg(0)), x1 = this.unwrap(arg(1))
        let saved: Ex | undefined
        if (x0.type === "CallExpression" && x1.type === "CallExpression" && this.name(x0.callee) === "fst" && this.name(x1.callee) === "snd" && x0.arguments.length === 1 && x1.arguments.length === 1) {
          const p = this.unwrap(this.at(x0.arguments, 0)), q = this.unwrap(this.at(x1.arguments, 0))
          if (p.type === "Identifier" && q.type === "Identifier" && p.name === q.name) saved = p
        }
        request = saved ? this.term(saved, env) : { _tag: "app", atom: "pair", args: [left, right] }
      }
      return { _tag: "perform", op: r.op, request }
    }
    const application = this.term(x, env)
    this.defer("unknownHead")
    return { _tag: "fail", error: application }
  }
  typeNode(t?: TSType | TSTupleElement): Ty {
    if (!t) return { _tag: "unit" }
    if (t.type === "TSNumberKeyword") return { _tag: "nat" }
    if (t.type === "TSBooleanKeyword") return { _tag: "bool" }
    if (t.type === "TSStringKeyword") return { _tag: "string" }
    if (t.type === "TSVoidKeyword" || t.type === "TSUndefinedKeyword") return { _tag: "unit" }
    if (t.type === "TSNeverKeyword") return { _tag: "never" }
    if (t.type === "TSTypeReference") {
      const name = this.text(t.typeName), args = t.typeArguments?.params
      if (name === "Option.Option" && args?.length === 1) return { _tag: "option", inner: this.typeNode(args[0]) }
      if (name === "ReadonlyArray" && args?.length === 1) return { _tag: "list", inner: this.typeNode(args[0]) }
      return { _tag: "handle", target: name }
    }
    if (t.type === "TSTupleType" && t.elementTypes.length === 2) {
      return { _tag: "prod", left: this.typeNode(t.elementTypes[0]), right: this.typeNode(t.elementTypes[1]) }
    }
    return bad("type node")
  }
  /** The loop image's tail, `Effect.map(Effect.whileLoop({…}), () => result)`: the loop's call and
   * the result's thunk. The printed seam reads the printer's spelling only; the foreign reader also
   * reads the pipe spellings of the same dual call (`ForeignCompilerReader.loopTail`). */
  loopTail(x: Ex): { readonly loop: Ex; readonly result: Ex } {
    const mapCall = this.call(x); this.arity(mapCall.arguments, 2)
    if (this.name(mapCall.callee) !== "Effect.map") return bad("loop map head")
    return { loop: this.at(mapCall.arguments, 0), result: this.at(mapCall.arguments, 1) }
  }
  loop(block: FunctionBody, env: readonly string[]): Eff {
    const [init, ret] = block.body
    if (block.body.length !== 2 || !init || init.type !== "VariableDeclaration" || !ret || ret.type !== "ReturnStatement" || !ret.argument) return bad("loop")
    const decl = init.declarations[0]
    if (!decl || init.declarations.length !== 1 || decl.id.type !== "Identifier" || !decl.init) return bad("cursor")
    const cursor = decl.id.name
    const tail = this.loopTail(ret.argument)
    const c = this.call(tail.loop); this.arity(c.arguments, 1)
    if (this.name(c.callee) !== "Effect.whileLoop") return bad("loop head")
    const resultArrow = this.arrow(tail.result, env, 0)
    const result = this.term(this.expression(resultArrow.body), resultArrow.env)
    const m = this.fields(this.at(c.arguments, 0)), inner = [...env, cursor]
    if (m.size !== 3) return bad("loop fields")
    const test = this.arrow(this.field(m, "while"), inner, 0), body = this.arrow(this.field(m, "body"), inner, 0), step = this.arrow(this.field(m, "step"), inner, 1)
    if (step.body.type !== "BlockStatement" || step.body.body.length !== 1) return bad("step")
    const s = step.body.body[0]
    if (!s || s.type !== "ExpressionStatement" || s.expression.type !== "AssignmentExpression" || s.expression.operator !== "=" || this.text(s.expression.left) !== cursor) return bad("step assignment")
    // An unannotated cursor has no type (`cursorTy: Ty | null`, DI-91, `5185a6cd`); this read
    // `unit` until seat J2's step 1b, which made every printed loop a different program.
    const annotation = decl.id.typeAnnotation
    const cursorTy: Ty | null = annotation ? this.typeNode(annotation.typeAnnotation) : null
    return { _tag: "iterate", cursorTy, initial: this.term(decl.init, env), test: this.term(this.expression(test.body), inner), body: this.eff(this.expression(body.body), inner), step: this.term(s.expression.right, step.env), result }
  }

}

/** Explicit printer-image test seam. Never called by foreign recognition. */
export function readPrintedSource(source: string, filename = "program.ts"): Eff {
  const parsed = parseTypeScript(filename, source, "ts")
  if (parsed.errors.length) return bad("parse")
  // Keep the existing test-context projection, adding only named layer declarations.
  const statements = topLevel(parsed.program).filter(({ node: s, exported }) => s.type === "ExpressionStatement" || s.type === "VariableDeclaration" &&
    (exported || s.declarations.some(d => d.id.type === "Identifier" && d.id.name.startsWith("L_")))).map(t => t.node)
  const last = statements.at(-1)
  if (!last) return bad("program")
  const constant = (s: Directive | Statement): { name: string; value: Ex } => {
    if (s.type !== "VariableDeclaration" || !constLike(s) || s.declarations.length !== 1) return bad("program statement")
    const d = s.declarations[0]!
    if (d.id.type !== "Identifier" || !d.init) return bad("program initializer")
    return { name: d.id.name, value: d.init }
  }
  const reader = new CompilerReader(source)
  const declarations = statements.slice(0, -1).map(s => {
    const d = constant(s)
    return { path: layerPath(d.name), layer: reader.layer(d.value) }
  })
  // Restore a containing definition first, so its nested target has a position.
  declarations.sort((a, b) => {
    for (let i = 0; i < Math.min(a.path.length, b.path.length); i++) {
      if (a.path[i] !== b.path[i]) return a.path[i]! < b.path[i]! ? -1 : 1
    }
    return a.path.length - b.path.length
  })
  let program = reader.eff(last.type === "ExpressionStatement" ? last.expression : constant(last).value, [])
  reader.settle()
  for (const d of declarations) program = restoreLayer(program, d.path, d.layer)
  return decodeEff(program)
}

import type { Verdict, RefusalCode, Key, LayerBinding } from "./contract.ts"
import { taxonomy } from "../taxonomy.gen.ts"
import { atomNames, heads } from "../profile.gen.ts"
import { forms } from "../forms.gen.ts"
import { encodeProgram } from "../wire.gen.ts"
import type { Ty } from "../eff.gen.ts"
import type { Package } from "../packages.gen.ts"
import { bindText, internServiceKey, isStringList, methodArgs, methodRow, packageByHead, stringsTerm } from "./package-rows.ts"
import { foldSql, isRefusal, type Bind, type SqlArg, type SqlPart } from "./sql-fold.ts"
import { expandForm, effectSlot, fixedEffect, type FormAlgebra, type FormArguments } from "./forms.ts"

class ForeignRefusal extends Error {
  constructor(readonly code: RefusalCode, readonly value: string) { super(code) }
}
const refuseForeign = (code: RefusalCode, value: string): never => { throw new ForeignRefusal(code, value) }
const knownHeads = new Set<string>([...heads, ...rows.map(r => r.row.spelling), ...forms.rows.map(r => r.head)])
// The pure atoms are read, not copied (DI-40): `atomNames` is `Effect4.Program.nativeAtom`'s
// own name list, emitted into `profile.gen.ts` by `tools/Tools/TsGen.lean` and checked there
// against `nativeAtomTy`. An atom appended in Lean reaches this recognizer by regeneration.
const atoms = atomNames

const effForms: FormAlgebra<Eff, Term, ServiceKey> = {
  literal: value => ({ _tag: "lit", value }),
  variable: index => ({ _tag: "var", index }),
  succeed: value => ({ _tag: "succeed", value }),
  die: defect => ({ _tag: "failCause", cause: { _tag: "die", defect } }),
  bind: (first, rest) => ({ _tag: "bind", first, rest }),
  onExit: (body, finalizer) => ({ _tag: "onExit", body, finalizer }),
  matchCause: (body, onValue, onCause) => ({ _tag: "matchCause", body, onValue, onCause }),
  service: key => ({ _tag: "service", key }),
  yieldNow: priority => ({ _tag: "yieldNow", priority }),
  fork: (program, options) => ({ _tag: "withFiber", action: { _tag: "fork", program, options } }),
  forkIn: (program, scope, options) => ({ _tag: "withFiber", action: { _tag: "forkIn", program, scope, options } }),
  forkScoped: (program, options) => ({ _tag: "withFiber", action: { _tag: "forkScoped", program, options } }),
  acquireRelease: (acquire, release) => ({ _tag: "acquireRelease", acquire, release }),
}
const lowerForm = (name: string, depth: number, args: FormArguments<Eff, Term, ServiceKey>): Eff => {
  const result = expandForm(name, depth, args, effForms)
  return result.ok ? result.value : refuseForeign("E-NODE", `form lowering: ${result.error}`)
}

/** TypeScript's `collect` over a destructured declaration's name: a binding element whose name is
 * an identifier contributes it and stops; any other node is walked through its children in
 * `forEachChild`'s order (a computed key, the nested pattern, then the default), so a binding
 * element nested anywhere in it contributes too. ESTree has no binding element: an object pattern's
 * property, an array pattern's element and a rest element play its part; and a pattern binds only
 * in a binding position (a parameter, a declarator, a catch clause), never as an assignment target,
 * which TypeScript reads as an object or array literal. */
function bindingNames(pattern: object, push: (name: string) => void): void {
  type Any = { readonly type: string; readonly [k: string]: unknown }
  const isAny = (v: unknown): v is Any => typeof v === "object" && v !== null && typeof Reflect.get(v, "type") === "string"
  const field = (n: Any, k: string): Any | undefined => { const v = n[k]; return isAny(v) ? v : undefined }
  const element = (target: Any, key: Any | undefined): void => {
    let name = target, init: Any | undefined
    if (name.type === "AssignmentPattern") { init = field(name, "right"); name = field(name, "left") ?? name }
    if (name.type === "RestElement") name = field(name, "argument") ?? name
    if (name.type === "Identifier" && typeof name.name === "string") { push(name.name); return }
    if (key) scan(key)
    patternOf(name)
    if (init) scan(init)
  }
  const patternOf = (p: Any): void => {
    if (p.type === "ObjectPattern" && Array.isArray(p.properties)) {
      for (const prop of p.properties) {
        if (!isAny(prop)) continue
        const value = field(prop, "value")
        if (prop.type === "RestElement") element(prop, undefined)
        else if (value) element(value, prop.computed === true ? field(prop, "key") : undefined)
      }
    } else if (p.type === "ArrayPattern" && Array.isArray(p.elements)) {
      for (const el of p.elements) if (isAny(el)) element(el, undefined)
    } else scan(p)
  }
  // A parameter (or a declarator, or a catch clause) is not a binding element: its name
  // contributes only when it is a pattern. Decorators first, then the name, its type, its default.
  const parameter = (p: Any): void => {
    if (p.type === "TSParameterProperty") { for (const d of childNodes(p)) if (isAny(d) && d.type === "Decorator") scan(d); const inner = field(p, "parameter"); if (inner) parameter(inner); return }
    if (p.type === "AssignmentPattern") { const left = field(p, "left"), right = field(p, "right"); if (left) parameter(left); if (right) scan(right); return }
    if (p.type === "ObjectPattern" || p.type === "ArrayPattern" || p.type === "RestElement") {
      for (const d of childNodes(p)) if (isAny(d) && d.type === "Decorator") scan(d)
      const name = p.type === "RestElement" ? field(p, "argument") : p
      if (name && (name.type === "ObjectPattern" || name.type === "ArrayPattern")) patternOf(name)
      else if (name && name !== p) parameter(name)
      const annotation = field(p, "typeAnnotation")
      if (annotation) scan(annotation)
      return
    }
    scan(p)
  }
  const scan = (n: Any): void => {
    const params = Array.isArray(n.params) && n.type !== "TSTypeParameterDeclaration" && n.type !== "TSTypeParameterInstantiation" ? n.params.filter(isAny) : []
    const bound = n.type === "VariableDeclarator" ? field(n, "id") : n.type === "CatchClause" ? field(n, "param") : undefined
    for (const child of childNodes(n)) {
      if (!isAny(child)) continue
      if (params.includes(child) || child === bound) parameter(child)
      else scan(child)
    }
  }
  if (isAny(pattern)) patternOf(pattern)
}

class ForeignCompilerReader extends CompilerReader {
  readonly keys: Key[] = []
  readonly layers: LayerBinding[] = []
  private readonly layerDefinitions: { sourceName: string; value: LayerTerm }[] = []
  private referenceCut: number | undefined
  constructor(source: string, readonly bindings: Map<string, string>, readonly declarations: Map<string, { at: number; value: Ex; constant?: boolean }>, readonly current: number) { super(source) }
  finish(program: Eff): Eff {
    if (this.layerDefinitions.length === 0) return decodeEff(program)
    const targets = new Map<number, readonly number[]>()
    const resolve = (layer: LayerTerm, path: readonly number[]): LayerTerm => {
      if (layer._tag !== "ref") return layer
      const index = layer.target[0]!, definition = this.layerDefinitions[index]
      if (layer.target.length !== 1 || !definition) return refuseForeign("E-REF-UNBOUND", "layer")
      const target = targets.get(index)
      if (target) return { _tag: "ref", target }
      targets.set(index, path)
      const binding = { sourceName: definition.sourceName, target: path }
      this.layers.push(binding)
      const value = resolve(definition.value, path)
      // An alias of a previously placed definition uses that definition's path.
      if (value._tag === "ref") { targets.set(index, value.target); binding.target = value.target }
      return value
    }
    const restored = walkProgram(program, resolve)
    const oldKeys = [...this.keys]
    this.keys.length = 0
    return decodeEff(walkProgram(restored, l => l, key => {
      const old = oldKeys.find(k => k.ordinal === key.name.value)
      if (!old) return refuseForeign("E-REF-UNBOUND", "service key")
      let entry = this.keys.find(k => k.sourceId === old.sourceId)
      if (!entry) { entry = { ...old, ordinal: this.keys.length + serviceTypes.firstFreeName }; this.keys.push(entry) }
      return { name: { value: entry.ordinal }, service: key.service }
    }, true))
  }
  override name(x: Ex): string {
    const rawName = (e: Ex): string => {
      e = this.unwrap(e)
      if (e.type === "Identifier") return e.name
      if (e.type === "MemberExpression" && !e.computed && !e.optional) return rawName(e.object) + "." + memberName(e)
      return refuseForeign("E-SPINE-ESCAPE", "member")
    }
    const raw = rawName(x), [root, ...tail] = raw.split(".")
    const binding = this.bindings.get(root!)
    if (binding !== undefined) {
      if (binding === "opaque") return refuseForeign("E-IMPORT-OPAQUE", raw)
      return [binding, ...tail].filter(Boolean).join(".")
    }
    if (raw === "undefined" || atoms.has(raw) || forms.lambdas.some(l => l.atom === raw)) return raw
    return refuseForeign("E-OP-RECEIVER", raw)
  }
  override literal(x: Ex): Lit {
    const y = this.unwrap(x)
    if (y.type === "NewExpression") return refuseForeign("E-NODE-SHAPE", "new")
    if (y.type === "AwaitExpression") return refuseForeign("E-NODE-SHAPE", "await")
    if (y.type === "YieldExpression") return refuseForeign("E-YIELD-POSITION", "expression")
    if (y.type === "TemplateLiteral") return refuseForeign("E-NODE-SHAPE", "template")
    if (isNumeric(y) && (!/^(0|[1-9][0-9]*)$/.test(this.text(y)) || !Number.isSafeInteger(y.value))) return refuseForeign("E-ARG-DYNAMIC", "number")
    if (isString(y) && this.text(y).slice(1, -1) !== JSON.stringify(y.value).slice(1, -1)) return refuseForeign("E-ARG-DYNAMIC", "string")
    try { return super.literal(y) } catch (e) { if (e instanceof Decline) return refuseForeign("E-ARG-DYNAMIC", "literal"); throw e }
  }
  override recordTerm(_x: Ex, _env: readonly string[]): Term | undefined { return undefined }
  override recordSelect(_x: Ex, _env: readonly string[]): Eff | undefined { return undefined }
  override term(x: Ex, env: readonly string[]): Term {
    const y = this.unwrap(x)
    if (y.type === "Identifier" && y.name !== "undefined" && this.variable(y, env) === undefined) return refuseForeign("E-REF-UNBOUND", y.name)
    if (y.type === "CallExpression") {
      if (this.variable(y.callee, env) !== undefined) return refuseForeign("E-ANSWER-HIGHER-ORDER", super.name(y.callee))
      if (!atoms.has(this.name(y.callee))) return refuseForeign("E-ARG-DYNAMIC", "term")
    }
    return super.term(y, env)
  }
  override arrow(x: Ex, env: readonly string[], count: number): { body: FunctionBody | Expression; env: readonly string[] } {
    const a = this.unwrap(x)
    if (a.type !== "ArrowFunctionExpression") return refuseForeign("E-ARG-CLOSURE", "continuation")
    if (a.params.length !== count || a.params.some(p => parameterName(p) === undefined)) return refuseForeign("E-BIND-SHAPE", "parameters")
    return super.arrow(a, env, count)
  }
  override stmts(input: readonly (Directive | Statement)[], initial: readonly string[]): readonly Stmt[] {
    const out: Stmt[] = [], env = [...initial]
    for (const s of input) {
      if (s.type === "ForStatement" || s.type === "ForOfStatement" || s.type === "ForInStatement") return refuseForeign("E-STMT-SHAPE", "for")
      if (s.type === "TryStatement") return refuseForeign("E-STMT-SHAPE", "try")
      if (s.type === "VariableDeclaration" && !constLike(s)) return refuseForeign("E-STMT-SHAPE", "let")
      if (s.type === "ReturnStatement") {
        if (!s.argument) return refuseForeign("E-RETURN-SHAPE", "term")
        if (this.unwrap(s.argument).type === "YieldExpression") return refuseForeign("E-YIELD-POSITION", "return")
        try { out.push({ _tag: "ret", value: this.term(s.argument, env) }) }
        catch (e) { if (e instanceof ForeignRefusal && e.code === "E-ANSWER-HIGHER-ORDER") throw e; return refuseForeign("E-RETURN-SHAPE", "term") }
        continue
      }
      const rows = super.stmts([s], env)
      out.push(...rows)
      if (s.type === "VariableDeclaration") { const d = s.declarations[0]; if (d && d.id.type === "Identifier") env.push(d.id.name) }
    }
    return out
  }
  declaration(id: { readonly name: string }): Ex {
    if (this.bindings.has(id.name)) return refuseForeign("E-IMPORT-OPAQUE", id.name)
    const d = this.declarations.get(id.name)
    if (!d) return refuseForeign("E-REF-UNBOUND", id.name)
    if (d.at >= (this.referenceCut ?? this.current)) return refuseForeign("E-REF-FORWARD", id.name)
    return d.value
  }
  /** A package key (spec §5.9, host rows step 5): a member head that resolves through an
   * `effect` import to a package's service, `SqlClient.SqlClient`; never a local declaration. */
  packageOf(x: Ex): Package | undefined {
    x = this.unwrap(x)
    if (x.type !== "MemberExpression" || x.computed || x.optional) return undefined
    let head: string
    try { head = this.name(x) } catch { return undefined }
    return packageByHead.get(head)
  }
  packageKey(pkg: Package): ServiceKey {
    const interned = internServiceKey(this.keys, pkg.key, pkg.service)
    if (!interned.ok) return refuseForeign("E-TYPE-PARAM", "service identity has conflicting shapes")
    const entry = interned.key
    return { name: { value: entry.ordinal }, service: { value: pkg.service } }
  }
  /** A method on a binder (`sql.unsafe(text, params)`, `store.get(k)`): a `method` row of the
   * canonical package table, its request `pair(receiver, args)` (Lean `addReceiver`); a member
   * the table does not carry is `E-OP-UNKNOWN` (decision 13: `withTransaction`). */
  methodCall(receiver: number, spelling: string, x: { readonly arguments: readonly Ex[]; readonly typeArguments?: { readonly params: readonly TSType[] } | null }, env: readonly string[]): Eff {
    const found = methodRow(spelling)
    if (!found) return refuseForeign("E-OP-UNKNOWN", spelling)
    const types = x.typeArguments?.params.map(n => this.text(n)) ?? []
    if (types.join(",") !== found.row.typeArgs.join(",")) return refuseForeign("E-OP-UNKNOWN", spelling)
    const { count, types: tys } = methodArgs(found.row)
    // rc.112's `unsafe(sql, params?)`: an omitted trailing parameter list is the empty list.
    const omitted = x.arguments.length === count - 1 && count > 0 && isStringList(tys[count - 1]!)
    if (x.arguments.length !== count && !omitted) return refuseForeign("E-BIND-SHAPE", "arity")
    const arg = (i: number): Term => i < x.arguments.length ? this.rowArgument(this.at(x.arguments, i), tys[i]!, env) : stringsTerm([])
    const request: Term = count === 0 ? unit : count === 1 ? arg(0) : { _tag: "app", atom: "pair", args: [arg(0), arg(1)] }
    const full: Term = { _tag: "app", atom: "pair", args: [{ _tag: "var", index: receiver }, request] }
    const op = { _tag: "external" as const, index: found.index }
    return { _tag: "perform", op, request: full }
  }
  /** A bind-parameter list is an array literal of bind literals, carried as JSON text through
   * `strings` (DB-15); anything else there, and every other position, is a term. */
  rowArgument(x: Ex, ty: Ty, env: readonly string[]): Term {
    const y = this.unwrap(x)
    if (isStringList(ty) && y.type === "ArrayExpression") {
      const texts: string[] = []
      for (const e of elementsOf(y)) {
        const z = this.unwrap(e)
        const value = isString(z) ? z.value : isNumeric(z) ? z.value
          : isTrue(z) ? true : isFalse(z) ? false
          : isNull(z) ? null : undefined
        const text = value === undefined ? undefined : bindText(value)
        if (text === undefined) return refuseForeign("E-ARG-DYNAMIC", "bind")
        texts.push(text)
      }
      return stringsTerm(texts)
    }
    return this.term(x, env)
  }
  /** The `sql\`` derived form (spec §5.5): a tagged template on a client binder is the static
   * fold under the sqlite dialect into the `unsafe` row, `pair(receiver, pair(text, strings(params)))`.
   * The fold itself is `sql-fold.ts`, shared with the other engine; this reads the tree into its
   * part language. A generic tag `sql<Row>\`…\`` is the same form. */
  sqlTemplate(receiver: number, tag: string, x: { readonly quasi: { readonly quasis: readonly TemplateElement[]; readonly expressions: readonly Expression[] } }, env: readonly string[]): Eff {
    const folded = foldSql(this.sqlParts(x, tag, env))
    if (isRefusal(folded)) return refuseForeign(folded.code, folded.detail)
    const found = methodRow("unsafe")
    if (!found) return refuseForeign("E-OP-UNKNOWN", "unsafe")
    const text: Term = { _tag: "lit", value: { _tag: "str", value: folded.text } }
    const request: Term = { _tag: "app", atom: "pair", args: [{ _tag: "var", index: receiver }, { _tag: "app", atom: "pair", args: [text, stringsTerm(folded.params)] }] }
    return { _tag: "perform", op: { _tag: "external", index: found.index }, request }
  }
  sqlParts(x: { readonly quasi: { readonly quasis: readonly TemplateElement[]; readonly expressions: readonly Expression[] } }, tag: string, env: readonly string[]): SqlPart & { kind: "template" } {
    const t = x.quasi
    return { kind: "template", quasis: t.quasis.map(templateText), parts: t.expressions.map(e => this.sqlPart(e, tag, env)) }
  }
  sqlBind(y: Ex): Bind | undefined {
    if (isString(y)) return y.value
    if (isNumeric(y)) return /^(0|[1-9][0-9]*)$/.test(this.text(y)) && Number.isSafeInteger(y.value) ? y.value : undefined
    if (isTrue(y)) return true
    if (isFalse(y)) return false
    if (isNull(y)) return null
    return undefined
  }
  sqlPart(e: Ex, tag: string, env: readonly string[]): SqlPart {
    const y = this.unwrap(e)
    const value = this.sqlBind(y)
    if (value !== undefined) return { kind: "bind", value }
    if (y.type === "TaggedTemplateExpression") {
      const inner = this.unwrap(y.tag)
      return inner.type === "Identifier" && inner.name === tag ? this.sqlParts(y, tag, env) : { kind: "dynamic", detail: "bind" }
    }
    if (y.type === "CallExpression") {
      const callee = this.unwrap(y.callee)
      if (callee.type === "MemberExpression" && !callee.computed && memberName(callee) === "returning" && y.arguments.length === 1) {
        return { kind: "returning", base: this.sqlPart(callee.object, tag, env), value: this.sqlPart(this.at(y.arguments, 0), tag, env) }
      }
      if (callee.type === "Identifier" && callee.name === tag) return { kind: "helper", name: "ident", args: y.arguments.map(a => this.sqlArg(a, tag, env)) }
      if (callee.type === "MemberExpression" && !callee.computed) {
        const object = this.unwrap(callee.object)
        if (object.type === "Identifier" && object.name === tag) return { kind: "helper", name: memberName(callee), args: y.arguments.map(a => this.sqlArg(a, tag, env)) }
      }
    }
    return { kind: "dynamic", detail: "bind" }
  }
  sqlArg(a: Ex, tag: string, env: readonly string[]): SqlArg {
    const y = this.unwrap(a)
    if (y.type === "ArrayExpression") return { kind: "list", items: elementsOf(y).map(el => this.sqlArg(el, tag, env)) }
    if (y.type === "ObjectExpression") {
      const fields: (readonly [string, SqlPart])[] = []
      for (const p of y.properties) {
        if (p.type !== "Property" || p.kind !== "init" || p.method || p.shorthand) return { kind: "dynamic", detail: "record key" }
        const k = p.key
        const key = p.computed ? undefined : k.type === "Identifier" ? k.name : k.type === "PrivateIdentifier" ? undefined : isString(k) ? k.value : isNumeric(k) ? String(k.value) : undefined
        if (key === undefined) return { kind: "dynamic", detail: "record key" }
        fields.push([key, this.sqlPart(p.value, tag, env)])
      }
      return { kind: "record", fields }
    }
    return this.sqlPart(a, tag, env)
  }
  override key(x: Ex): ServiceKey {
    x = this.unwrap(x)
    const pkg = this.packageOf(x)
    if (pkg) return this.packageKey(pkg)
    if (x.type === "Identifier") x = this.declaration(x)
    const c = this.call(x)
    const inner = this.unwrap(c.callee)
    const factory = inner.type === "CallExpression" ? inner : c
    if (this.name(factory.callee) !== "Context.Service") return refuseForeign("E-OP-UNKNOWN", "key")
    this.arity(c.arguments, 1)
    const last = factory.typeArguments?.params.at(-1)
    const shape = last ? this.text(last) : ""
    const [root, ...tail] = shape.split("."), binding = this.bindings.get(root!)
    if (binding === "opaque") return refuseForeign("E-IMPORT-OPAQUE", shape)
    const resolved = binding === undefined ? shape : [binding, ...tail].filter(Boolean).join(".")
    const canonical = packageByHead.get(resolved)?.target ?? resolved
    const service = serviceTypes.ordinary.find(entry => entry.rendered === canonical)?.code
      ?? refuseForeign("E-TYPE-PARAM", "service shape")
    const id = this.literal(this.at(c.arguments, 0))
    if (id._tag !== "str") return refuseForeign("E-ARG-DYNAMIC", "service identifier")
    const interned = internServiceKey(this.keys, id.value, service)
    if (!interned.ok) return refuseForeign("E-TYPE-PARAM", "service identity has conflicting shapes")
    const entry = interned.key
    return { name: { value: entry.ordinal }, service: { value: service } }
  }
  segment(head: string, args: readonly Ex[], first: Eff, env: readonly string[]): Eff {
    const at = (i: number) => this.at(args, i)
    const cont = (x: Ex, count = 1): Eff => {
      const a = this.arrow(x, env, count)
      return this.eff(this.expression(a.body), a.env)
    }
    if (head === "Effect.map") {
      this.arity(args, 1)
      const fn = this.arrow(at(0), env, 1)
      try { return { _tag: "bind", first, rest: { _tag: "succeed", value: this.term(this.expression(fn.body), fn.env) } } }
      catch { return refuseForeign("E-ARG-CLOSURE", "map") }
    }
    if (head === "Effect.flatMap") { this.arity(args, 1); return { _tag: "bind", first, rest: cont(at(0)) } }
    if (head === "Effect.catchCause") { this.arity(args, 1); return { _tag: "catchCause", body: first, handler: cont(at(0)) } }
    if (head === "Effect.catch") { this.arity(args, 1); return { _tag: "catchIf", test: { _tag: "lit", value: { _tag: "bool", value: true } }, body: first, handler: cont(at(0)) } }
    if (head === "Effect.catchIf") {
      if (args.length === 3) {
        if (this.name(at(2)) !== "undefined") return refuseForeign("E-BIND-SHAPE", "catchIf fallback")
      } else this.arity(args, 2)
      const predicate = this.arrow(at(0), env, 1)
      return { _tag: "catchIf", test: this.term(this.expression(predicate.body), predicate.env), body: first, handler: cont(at(1)) }
    }
    if (head === "Effect.onExit") { this.arity(args, 1); return { _tag: "onExit", body: first, finalizer: cont(at(0)) } }
    if (head === "Effect.andThen" || head === "Effect.tap") {
      this.arity(args, 1)
      const x = this.unwrap(at(0))
      const base = head === "Effect.tap" ? "tap" : "andThen"
      if (x.type === "ArrowFunctionExpression" && x.params.length) {
        const a = this.arrow(x, env, 1)
        return lowerForm(`${base}Continuation`, env.length, { effects: [fixedEffect(first),
          effectSlot(a.env, env.length, inner => this.eff(this.expression(a.body), inner))] })
      }
      const name = base === "andThen" && x.type === "ArrowFunctionExpression" ? "andThenThunk" : `${base}Effect`
      const body = x.type === "ArrowFunctionExpression" ? this.expression(x.body) : x
      return lowerForm(name, env.length, { effects: [fixedEffect(first),
        effectSlot(env, env.length, inner => this.eff(body, inner))] })
    }
    if (head === "Effect.as" || head === "Effect.asVoid") {
      this.arity(args, head === "Effect.as" ? 1 : 0)
      return lowerForm(head === "Effect.as" ? "as" : "asVoid", env.length,
        { effects: [fixedEffect(first)], terms: head === "Effect.as" ? [{ _tag: "lit", value: this.literal(at(0)) }] : [] })
    }
    if (head === "Effect.ensuring") {
      this.arity(args, 1)
      return lowerForm("ensuring", env.length, { effects: [fixedEffect(first),
        effectSlot(env, env.length, inner => this.eff(at(0), inner))] })
    }
    if (["Effect.exit", "Effect.scoped", "Effect.interruptible", "Effect.uninterruptible"].includes(head)) {
      this.arity(args, 0)
      const tag = head === "Effect.exit" ? "exit" : head === "Effect.scoped" ? "scoped" : head === "Effect.interruptible" ? "interruptible" : "uninterruptible"
      return { _tag: tag, body: first }
    }
    if (head === "Effect.matchCause" || head === "Effect.matchCauseEffect") {
      this.arity(args, 1); const m = this.fields(at(0))
      if (m.size !== 2) return refuseForeign("E-BIND-SHAPE", "match fields")
      const arm = (key: string) => {
        const a = this.arrow(this.field(m, key), env, 1), x = this.expression(a.body)
        return { value: x, env: a.env }
      }
      if (head === "Effect.matchCause") {
        const termArm = (name: string) => { const a = arm(name); return this.term(a.value, a.env) }
        return lowerForm("matchCause", env.length, { effects: [fixedEffect(first)],
          terms: [termArm("onSuccess"), termArm("onFailure")] })
      }
      const effectArm = (name: string) => (offset: number, count: number) => {
        const a = arm(name)
        return effectSlot(a.env, env.length, inner => this.eff(a.value, inner))(offset, count)
      }
      return lowerForm("matchCauseEffect", env.length, { effects: [fixedEffect(first),
        effectArm("onSuccess"), effectArm("onFailure")] })
    }
    if (head === "Effect.provideService") { this.arity(args, 2); const key = this.key(at(0)); return { _tag: "provideService", body: first, key, value: { _tag: "lit", value: this.provided(key, at(1)) } } }
    if (head === "Effect.provide") {
      if (args.length < 1 || args.length > 2) return refuseForeign("E-BIND-SHAPE", "arity")
      if (this.unwrap(at(0)).type === "ArrayExpression") return refuseForeign("E-OP-UNKNOWN", "Layer.mergeAll")
      const layer = this.layer(at(0))
      let isLocal = false
      if (args.length === 2) { const m = this.fields(at(1)), l = this.literal(this.field(m, "local")); if (m.size !== 1 || l._tag !== "bool" || !l.value) return refuseForeign("E-BIND-SHAPE", "provide options"); isLocal = true }
      return { _tag: "provideLayer", body: first, layer, isLocal }
    }
    if (["Effect.forkChild", "Effect.forkDetach", "Effect.forkIn", "Effect.forkScoped"].includes(head)) {
      const inScope = head === "Effect.forkIn", index = inScope ? 1 : 0
      const daemon = head !== "Effect.forkChild"
      if (args.length !== index && args.length !== index + 1) return refuseForeign("E-BIND-SHAPE", "arity")
      if (args.length === index) return lowerForm(`${head.slice("Effect.".length)}Default`, env.length,
        { effects: [fixedEffect(first)], terms: inScope ? [this.term(at(0), env)] : [] })
      const options = this.options(at(index), daemon)
      return { _tag: "withFiber", action: inScope ? { _tag: "forkIn", program: first, scope: this.term(at(0), env), options } : head === "Effect.forkScoped" ? { _tag: "forkScoped", program: first, options } : { _tag: "fork", program: first, options } }
    }
    if (!knownHeads.has(head)) return refuseForeign("E-OP-UNKNOWN", head)
    return refuseForeign("E-BIND-SHAPE", "pipe segment")
  }
  pipeSegment(x: Ex, first: Eff, env: readonly string[]): Eff {
    x = this.unwrap(x)
    if (x.type === "ArrowFunctionExpression") {
      const p0 = x.params[0], name = p0 ? parameterName(p0) : undefined
      if (x.params.length !== 1 || name === undefined || x.body.type === "BlockStatement") return refuseForeign("E-BIND-SHAPE", "eta")
      const body = this.call(x.body), callee = this.unwrap(body.callee)
      if (callee.type === "MemberExpression" && !callee.computed && memberName(callee) === "pipe" && this.unwrap(callee.object).type === "Identifier" && super.name(callee.object) === name) {
        let out = first
        for (const seg of body.arguments) out = this.pipeSegment(seg, out, env)
        return out
      }
      const args = body.arguments
      if (!args[0] || this.unwrap(args[0]).type !== "Identifier" || super.name(args[0]) !== name) return refuseForeign("E-BIND-SHAPE", "eta")
      let duplicate = false
      // TypeScript's `forEachChild` walk: a function whose own parameters rebind the name is not
      // searched; every identifier node elsewhere (a property name included) is a use.
      const visit = (n: TreeNode): void => {
        if ((n.type === "ArrowFunctionExpression" || n.type === "FunctionExpression") && n.params.some(p => parameterName(p) === name)) return
        if (n.type === "Identifier" && n.name === name) duplicate = true
        for (const child of childNodes(n)) visit(child)
      }
      args.slice(1).forEach(visit)
      if (duplicate) return refuseForeign("E-BIND-SHAPE", "eta reuse")
      return this.segment(this.name(callee), args.slice(1), first, env)
    }
    if (x.type === "CallExpression") return this.segment(this.name(x.callee), x.arguments, first, env)
    const head = this.name(x)
    if (!(forms.unaryRefs as readonly string[]).includes(head)) return refuseForeign("E-BIND-SHAPE", "unary reference")
    return this.segment(head, [], first, env)
  }
  /** The loop image's tail in every spelling the foreign styles give a dual call: `Effect.map(W, k)`,
   * `(W).pipe(Effect.map(k))`, `(W).pipe((s) => Effect.map(s, k))`, `pipe(W, Effect.map(k))` and
   * `Effect.map(k)(W)`. Anything else is read as the printed seam reads it (and declined there). */
  override loopTail(x: Ex): { readonly loop: Ex; readonly result: Ex } {
    const y = this.unwrap(x)
    const heads = (e: Ex, h: string): boolean => { try { return this.name(e) === h } catch { return false } }
    // A pipe segment that maps by `k`: `Effect.map(k)`, or the eta `(s) => Effect.map(s, k)` whose
    // `k` does not use `s`.
    const mapping = (segment: Ex): Ex | undefined => {
      const z = this.unwrap(segment)
      if (z.type === "CallExpression" && !z.optional && z.arguments.length === 1 && heads(z.callee, "Effect.map")) return z.arguments[0]
      if (z.type !== "ArrowFunctionExpression" || z.params.length !== 1 || z.body.type === "BlockStatement") return undefined
      const p0 = z.params[0], s = p0 ? parameterName(p0) : undefined, body = this.unwrap(z.body)
      if (s === undefined || body.type !== "CallExpression" || body.optional || body.arguments.length !== 2 || !heads(body.callee, "Effect.map")) return undefined
      const [self, k] = body.arguments
      if (!self || !k || this.unwrap(self).type !== "Identifier" || this.variable(self, [s]) !== 0) return undefined
      let uses = false
      const visit = (n: TreeNode): void => { if (n.type === "Identifier" && n.name === s) uses = true; for (const child of childNodes(n)) visit(child) }
      visit(k)
      return uses ? undefined : k
    }
    if (y.type === "CallExpression" && !y.optional) {
      const callee = this.unwrap(y.callee)
      if (callee.type === "MemberExpression" && !callee.computed && !callee.optional && memberName(callee) === "pipe" && y.arguments.length === 1) {
        const k = mapping(this.at(y.arguments, 0))
        if (k) return { loop: callee.object, result: k }
      }
      if (callee.type !== "CallExpression" && y.arguments.length === 2 && (heads(callee, "pipe") || heads(callee, "Function.pipe"))) {
        const k = mapping(this.at(y.arguments, 1))
        if (k) return { loop: this.at(y.arguments, 0), result: k }
      }
      if (callee.type === "CallExpression" && !callee.optional && callee.arguments.length === 1 && y.arguments.length === 1 && heads(callee.callee, "Effect.map")) {
        return { loop: this.at(y.arguments, 0), result: this.at(callee.arguments, 0) }
      }
    }
    return super.loopTail(x)
  }
  lambdaAtom(x: Ex): string {
    x = this.unwrap(x)
    const p0 = x.type === "ArrowFunctionExpression" ? x.params[0] : undefined
    const name = p0 ? parameterName(p0) : undefined
    if (x.type !== "ArrowFunctionExpression" || x.params.length !== 1 || name === undefined || x.body.type === "BlockStatement") return refuseForeign("E-ARG-CLOSURE", "lambda atom")
    const b = this.unwrap(x.body)
    const param = (e: Ex) => { e = this.unwrap(e); return e.type === "Identifier" && e.name === name }
    const number = (e: Ex, n: number) => { const v = this.literal(e); return v._tag === "nat" && v.value === n }
    const option = (e: Ex, head: string, n?: number) => {
      e = this.unwrap(e)
      if (e.type !== "CallExpression" || this.name(e.callee) !== head) return false
      return n === undefined ? e.arguments.length === 0 : e.arguments.length === 1 && number(this.at(e.arguments, 0), n)
    }
    if (b.type === "BinaryExpression" && b.left.type !== "PrivateIdentifier" && param(b.left)) {
      if (b.operator === "+" && number(b.right, 1)) return "incr"
      if (b.operator === "*" && number(b.right, 2)) return "double"
    }
    if (option(b, "Option.none")) return "noChange"
    if (b.type === "ConditionalExpression") {
      const test = this.unwrap(b.test)
      if (test.type === "BinaryExpression" && test.operator === ">" && param(test.left) && number(test.right, 0) && option(b.consequent, "Option.some", 0) && option(b.alternate, "Option.none")) return "zeroWhenPositive"
    }
    return refuseForeign("E-ARG-CLOSURE", "lambda atom")
  }
  duration(x: Ex): number {
    x = this.unwrap(x)
    let numerator: bigint, denominator = 1n, factor = 1n, divisor = 1n
    if (x.type === "CallExpression") {
      const h = this.name(x.callee)
      const scale: Record<string, bigint> = { "Duration.millis": 1n, "Duration.seconds": 1000n, "Duration.minutes": 60000n, "Duration.hours": 3600000n, "Duration.days": 86400000n, "Duration.weeks": 604800000n }
      if (!scale[h] || x.arguments.length !== 1) return refuseForeign("E-ARG-DYNAMIC", "duration")
      const n = this.literal(this.at(x.arguments, 0)); if (n._tag !== "nat") return refuseForeign("E-ARG-DYNAMIC", "duration")
      numerator = BigInt(n.value); factor = scale[h]!
    } else {
      const v = this.literal(x)
      if (v._tag === "nat") numerator = BigInt(v.value)
      else if (v._tag === "str") {
        const m = /^(-?\d+(?:\.\d+)?)\s+(nanos?|micros?|millis?|seconds?|minutes?|hours?|days?|weeks?)$/.exec(v.value)
        if (!m || m[1]!.startsWith("-")) return refuseForeign("E-ARG-DYNAMIC", "duration")
        const [whole, frac = ""] = m[1]!.split("."); numerator = BigInt(whole! + frac); denominator = 10n ** BigInt(frac.length)
        const name = m[2]!.replace(/s$/, "")
        const scales: Record<string, bigint> = { nano: 1n, micro: 1n, milli: 1n, second: 1000n, minute: 60000n, hour: 3600000n, day: 86400000n, week: 604800000n }
        factor = scales[name]!; divisor = name === "nano" ? 1000000n : name === "micro" ? 1000n : 1n
      } else return refuseForeign("E-ARG-DYNAMIC", "duration")
    }
    const top = numerator * factor, bottom = denominator * divisor
    if (top % bottom || top / bottom >= 9007199254740992n) return refuseForeign("E-ARG-DYNAMIC", "duration")
    return Number(top / bottom)
  }
  provided(key: ServiceKey, x: Ex): Lit {
    const value = this.literal(x), expected = serviceTypeFor(key)?.ty._tag
    const actual = value._tag === "str" ? "string" : value._tag
    if (actual !== expected) return refuseForeign("E-ARG-DYNAMIC", "service literal shape")
    return value
  }
  override layer(x: Ex): LayerTerm {
    x = this.unwrap(x)
    if (x.type === "Identifier") {
      const value = this.declaration(x), declaration = this.declarations.get(x.name)!
      if (!declaration.constant) return refuseForeign("E-REF-UNBOUND", x.name)
      const sourceName = x.name
      const existing = this.layerDefinitions.findIndex(d => d.sourceName === sourceName)
      if (existing >= 0) return { _tag: "ref", target: [existing] }
      const previous = this.referenceCut, outer = this.deferred
      this.referenceCut = declaration.at
      this.deferred = undefined
      let layer: LayerTerm
      try {
        layer = this.layer(value)
        // The oxc engine reads the definition here (`readLayer`), and its refusal is this one.
        if (this.deferred !== undefined) refuseForeign("E-NODE", "layer")
        this.deferred = outer
      }
      catch (e) {
        const code = e instanceof ForeignRefusal ? e.code : e instanceof Decline ? "E-NODE" : undefined
        if (code) return refuseForeign("E-REF-UNBOUND", `${sourceName}: ${code}`)
        throw e
      } finally { this.referenceCut = previous }
      const index = this.layerDefinitions.length
      this.layerDefinitions.push({ sourceName, value: layer })
      return { _tag: "ref", target: [index] }
    }
    const c = this.call(x), callee = this.unwrap(c.callee)
    if (callee.type === "MemberExpression" && !callee.computed && memberName(callee) === "pipe") return super.layer(x)
    if (this.name(c.callee) === "Layer.succeed") {
      this.arity(c.arguments, 2)
      const key = this.key(this.at(c.arguments, 0))
      return { _tag: "succeed", key, value: this.provided(key, this.at(c.arguments, 1)) }
    }
    return super.layer(x)
  }
  override eff(x: Ex, env: readonly string[]): Eff {
    x = this.unwrap(x)
    if (x.type === "ArrowFunctionExpression" || x.type === "FunctionExpression") return refuseForeign(x.typeParameters?.params.length ? "E-TYPE-PARAM" : "E-PARAM-SHAPE", x.typeParameters?.params.length ? "generic unit" : "function")
    if (x.type === "ConditionalExpression") return refuseForeign("E-BRANCH", "conditional")
    if (x.type === "TSAsExpression" || x.type === "TSSatisfiesExpression" || x.type === "TSTypeAssertion" || x.type === "TSNonNullExpression") return refuseForeign("E-SPINE-ESCAPE", "assertion")
    if (this.variable(x, env) !== undefined) return super.eff(x, env)
    // A package key in program position (`yield* SqlClient.SqlClient`) is its service; a
    // property of a binder (`sql.reserve`) is a head the table does not carry.
    if (x.type !== "CallExpression") {
      const pkg = this.packageOf(x)
      if (pkg) return lowerForm("yieldKey", env.length, { effects: [], keys: [this.packageKey(pkg)] })
      if (x.type === "MemberExpression" && !x.computed && this.variable(x.object, env) !== undefined) return refuseForeign("E-OP-UNKNOWN", memberName(x))
    }
    // `sql\`…\`` on a client binder is the derived form; a tag bound to an import refuses with
    // that import's code (drizzle's `sql` is `E-IMPORT-OPAQUE`), any other tag is unresolved.
    if (x.type === "TaggedTemplateExpression") {
      const tag = this.unwrap(x.tag)
      const receiver = this.variable(tag, env)
      if (receiver !== undefined && tag.type === "Identifier") return this.sqlTemplate(receiver, tag.name, x, env)
      this.name(tag)
      return refuseForeign("E-OP-RECEIVER", tag.type === "Identifier" ? tag.name : "template tag")
    }
    if (x.type === "Identifier" && this.variable(x, env) === undefined && x.name !== "undefined" && !this.bindings.has(x.name)) {
      const decl = this.unwrap(this.declaration(x))
      if (decl.type === "CallExpression" && this.name(this.unwrap(decl.callee).type === "CallExpression" ? this.call(decl.callee).callee : decl.callee) === "Context.Service") return lowerForm("yieldKey", env.length, { effects: [], keys: [this.key(x)] })
      const previous = this.referenceCut
      this.referenceCut = this.declarations.get(x.name)!.at
      try { return this.eff(decl, env) }
      catch (e) { if (e instanceof ForeignRefusal) return refuseForeign("E-REF-UNBOUND", `${x.name}: ${e.code}`); throw e }
      finally { this.referenceCut = previous }
    }
    if (x.type === "CallExpression") {
      const callee = this.unwrap(x.callee)
      if (x.optional || (callee.type === "MemberExpression" && !callee.computed && callee.optional)) return refuseForeign("E-SPINE-ESCAPE", "optional")
      if (x.arguments.some(a => a.type === "SpreadElement")) return refuseForeign("E-SPINE-ESCAPE", "spread")
      if (callee.type === "MemberExpression" && !callee.computed && memberName(callee) === "pipe") {
        let first = this.eff(callee.object, env)
        for (const segment of x.arguments) first = this.pipeSegment(segment, first, env)
        return first
      }
      // A member call on a binder is a method row (or an unknown head); a receiver that is
      // not a binder falls through to head resolution, which refuses it `E-OP-RECEIVER`.
      if (callee.type === "MemberExpression" && !callee.computed) {
        const receiver = this.variable(callee.object, env)
        if (receiver !== undefined) return this.methodCall(receiver, memberName(callee), x, env)
      }
      if (callee.type === "CallExpression") {
        this.arity(x.arguments, 1)
        return this.segment(this.name(callee.callee), callee.arguments, this.eff(this.at(x.arguments, 0), env), env)
      }
      const h = this.name(x.callee)
      if (h === "Effect.fn" || h === "Effect.fnUntraced") return refuseForeign("E-PARAM-SHAPE", "function")
      if (["Effect.catchTag", "Effect.catchTags", "Effect.mapError", "Effect.match", "Effect.orElseSucceed"].includes(h)) return refuseForeign("E-HANDLER", h)
      if (["Effect.promise", "Effect.tryPromise", "Effect.try", "Effect.callback"].includes(h)) return refuseForeign("E-ARG-CLOSURE", h)
      if (h === "Effect.whileLoop") return refuseForeign("E-LOOP", "whileLoop")
      if (h.startsWith("Cause.") || h.startsWith("Layer.")) return refuseForeign("E-NODE", "program fragment")
      if (h === "pipe" || h === "Function.pipe") {
        let first = this.eff(this.at(x.arguments, 0), env)
        for (const segment of x.arguments.slice(1)) first = this.pipeSegment(segment, first, env)
        return first
      }
      if (forms.duals.some(d => d.head === h) || h === "Effect.asVoid") {
        const first = this.eff(this.at(x.arguments, 0), env)
        return this.segment(h, x.arguments.slice(1), first, env)
      }
      if (h === "Effect.acquireRelease") {
        this.arity(x.arguments, 2)
        const release = this.unwrap(this.at(x.arguments, 1))
        if (release.type !== "ArrowFunctionExpression" || release.params.length < 1 || release.params.length > 2) return refuseForeign("E-ARG-CLOSURE", "release")
        const fn = this.arrow(release, env, release.params.length)
        const acquire = this.eff(this.at(x.arguments, 0), env)
        if (release.params.length === 1) return lowerForm("releaseOne", env.length,
          { effects: [fixedEffect(acquire), effectSlot(fn.env, env.length,
            inner => this.eff(this.expression(fn.body), inner))] })
        return { _tag: "acquireRelease", acquire, release: this.eff(this.expression(fn.body), fn.env) }
      }
      if (h === "Effect.sleep") {
        this.arity(x.arguments, 1)
        const r = rows.find(r => r.row.spelling === h)!
        return { _tag: "perform", op: r.op, request: { _tag: "lit", value: { _tag: "nat", value: this.duration(this.at(x.arguments, 0)) } } }
      }
      if (h === "Effect.fail" || h === "Effect.die") {
        this.arity(x.arguments, 1)
        let value: Lit
        try { value = this.literal(this.at(x.arguments, 0)) } catch { return refuseForeign("E-FAIL-NOT-DOCUMENTED", "literal required") }
        const t: Term = { _tag: "lit", value }
        return h === "Effect.fail" ? { _tag: "fail", error: t } : lowerForm("die", env.length, { effects: [], terms: [t] })
      }
      if (h === "Effect.provideService") {
        this.arity(x.arguments, 3)
        const body = this.eff(this.at(x.arguments, 0), env), key = this.key(this.at(x.arguments, 1)), value = this.provided(key, this.at(x.arguments, 2))
        return { _tag: "provideService", body, key, value: { _tag: "lit", value } }
      }
      if (x.arguments.some(a => this.unwrap(a).type === "ArrowFunctionExpression") && rows.some(r => r.row.spelling === h)) {
        for (const r of rows.filter(r => r.row.spelling === h)) {
          const count = r.row.shape === "tupleCall" ? 2 : r.row.request._tag === "unit" ? 0 : 1
          if (x.arguments.length !== count + r.row.trailing.length) continue
          const trailing = x.arguments.slice(count).map(a => this.unwrap(a).type === "ArrowFunctionExpression" ? this.lambdaAtom(a) : this.name(a))
          if (!r.row.trailing.every((name, i) => trailing[i] === name)) continue
          const request = count === 0 ? unit : count === 1 ? this.term(this.at(x.arguments, 0), env) : { _tag: "app" as const, atom: "pair", args: [this.term(this.at(x.arguments, 0), env), this.term(this.at(x.arguments, 1), env)] }
          return { _tag: "perform", op: r.op, request }
        }
        return refuseForeign("E-ARG-CLOSURE", "lambda atom")
      }
      if (!knownHeads.has(h) && !atoms.has(h)) return refuseForeign("E-OP-UNKNOWN", h)
    }
    if (x.type !== "CallExpression" && (x.type === "Identifier" || x.type === "MemberExpression" && !x.computed)) {
      const h = this.name(x)
      if (h === "Effect.void" || h === "Effect.yieldNow") return lowerForm(h.slice("Effect.".length), env.length, { effects: [] })
    }
    return super.eff(x, env)
  }
}

/** Strict foreign admission. The printer-image entrypoint is never a fallback. */
export function recognizeSource(source: string, filename: string, onParse?: (ok: boolean) => void, onTree?: (tree: Program) => void): Verdict[] {
  if (!source.includes('from "effect') && !source.includes("from 'effect")) return []
  const parsed = parseTypeScript(filename, source)
  if (parsed.errors.length) { onParse?.(false); return [] }
  onParse?.(true)
  const file = parsed.program
  onTree?.(file)
  const statements = topLevel(file)
  const bindings = new Map<string, string>()
  const declarations = new Map<string, { at: number; value: Ex; constant?: boolean }>()
  for (const { node: s } of statements) {
    if (s.type === "ImportDeclaration" && s.importKind !== "type") {
      const mod = s.source.value
      const base = mod === "effect" ? "" : mod.startsWith("effect/") ? mod.slice(7) : "opaque"
      for (const i of s.specifiers) {
        if (i.type === "ImportDefaultSpecifier") bindings.set(i.local.name, "opaque")
        else if (i.type === "ImportNamespaceSpecifier") bindings.set(i.local.name, base === "" && i.local.name === "Effect" ? "Effect" : base)
        else if (i.importKind !== "type") bindings.set(i.local.name, base === "opaque" ? base : [base, i.imported.type === "Identifier" ? i.imported.name : i.imported.value].filter(Boolean).join("."))
      }
    }
    if (s.type === "ClassDeclaration" && s.id && s.superClass) declarations.set(s.id.name, { at: s.start, value: s.superClass })
    if (s.type === "VariableDeclaration") for (const d of s.declarations) if (d.id.type === "Identifier" && d.init) declarations.set(d.id.name, { at: d.start, value: d.init, constant: constLike(s) })
  }
  const result: Verdict[] = []
  for (const { node: s } of statements) {
    if (s.type !== "VariableDeclaration" || !constLike(s)) continue
    for (const d of s.declarations) {
      if (d.id.type !== "Identifier") {
        const names: string[] = []
        bindingNames(d.id, name => names.push(name))
        for (const name of names) result.push({ kind: "refusal", unit: { file: filename, name, span: { start: d.start, end: d.end } }, code: "E-PROGRAM", detail: "program shape: destructured unit" })
        continue
      }
      if (!d.init) continue
      const reader = new ForeignCompilerReader(source, bindings, declarations, d.start)
      const value = reader.unwrap(d.init)
      if (value.type === "CallExpression") {
        try { if (reader.name(value.callee) === "Context.Service") continue } catch { /* The unit receives the refusal below. */ }
      }
      try { const probe = new ForeignCompilerReader(source, bindings, declarations, d.start); probe.layer(value); probe.settle(); continue } catch { /* A program or refused declaration remains a unit. */ }
      const unit = { file: filename.replaceAll("\\", "/"), name: d.id.name, span: { start: d.start, end: d.end } }
      try {
        const read = reader.eff(value, [])
        reader.settle()
        const eff = reader.finish(read)
        result.push({ kind: "lifted", unit, eff, keys: reader.keys, layers: reader.layers, wireHex: Buffer.from(encodeProgram(eff)).toString("hex") })
      } catch (e) {
        const failure = e instanceof ForeignRefusal ? e : e instanceof Decline ? new ForeignRefusal("E-NODE", e.message) : undefined
        if (!failure) throw e
        const template = taxonomy.find(t => t.code === failure.code)!.detail
        result.push({ kind: "refusal", unit, code: failure.code, detail: template.replace("{value}", failure.value) })
      }
    }
  }
  // I3's additional roots. Their names are stable under trivia and unused declarations.
  let entryIndex = 0
  const entries = new Set(["Effect.runPromise", "Effect.runSync", "Effect.runFork", "Effect.runPromiseExit", "Effect.runSyncExit", "Effect.runCallback"])
  const extra = (name: string, value: Ex | undefined, start: number, end: number, forced?: RefusalCode) => {
    const unit = { file: filename.replaceAll("\\", "/"), name, span: { start, end } }
    if (forced) { result.push({ kind: "refusal", unit, code: forced, detail: taxonomy.find(t => t.code === forced)!.detail.replace("{value}", forced === "E-TYPE-PARAM" ? "generic unit" : "function") }); return }
    const reader = new ForeignCompilerReader(source, bindings, declarations, start)
    try {
      const read = reader.eff(value!, [])
      reader.settle()
      const eff = reader.finish(read)
      result.push({ kind: "lifted", unit, eff, keys: reader.keys, layers: reader.layers, wireHex: Buffer.from(encodeProgram(eff)).toString("hex") })
    } catch (e) {
      const r = e instanceof ForeignRefusal ? e : e instanceof Decline ? new ForeignRefusal("E-NODE", e.message) : undefined
      if (!r) throw e
      result.push({ kind: "refusal", unit, code: r.code, detail: taxonomy.find(t => t.code === r.code)!.detail.replace("{value}", r.value) })
    }
  }
  const entryCall = (x: Ex) => {
    x = new CompilerReader(source).unwrap(x)
    if (x.type !== "CallExpression") return
    let name: string
    try { name = new ForeignCompilerReader(source, bindings, declarations, x.start).name(x.callee) } catch { return }
    if (!entries.has(name)) return
    for (const a of x.arguments) extra(`${name}#${entryIndex++}`, a, a.start, a.end)
  }
  for (const { node: s, first } of statements) {
    if (s.type === "ExportDefaultDeclaration") {
      // `export default <expression>`, TypeScript's export assignment (a declaration under
      // `export default` is the declaration itself: `topLevel`).
      const d = s.declaration
      if (!isDefaultDeclaration(d)) extra("default", d, d.start, d.end)
    }
    else if (s.type === "ExpressionStatement") entryCall(s.expression)
    else if (s.type === "FunctionDeclaration" || s.type === "TSDeclareFunction") {
      if (s.id?.name === "main" && s.body) {
        for (const st of s.body.body) {
          if (st.type === "ExpressionStatement") entryCall(st.expression.type === "AwaitExpression" ? st.expression.argument : st.expression)
          if (st.type === "ReturnStatement" && st.argument) entryCall(st.argument.type === "AwaitExpression" ? st.argument.argument : st.argument)
        }
      }
      extra(s.id?.name ?? "default", undefined, s.id?.start ?? first, s.end, s.typeParameters?.params.length ? "E-TYPE-PARAM" : "E-PARAM-SHAPE")
    } else if (s.type === "ClassDeclaration") {
      const base = s.superClass
      let service = false
      if (base) try {
        const reader = new ForeignCompilerReader(source, bindings, declarations, s.end), c = reader.call(base), inner = reader.unwrap(c.callee)
        service = reader.name(inner.type === "CallExpression" ? inner.callee : c.callee) === "Context.Service"
      } catch { /* A different class is a parameterized unit. */ }
      if (!service) extra(s.id?.name ?? "default", undefined, s.id?.start ?? first, s.end, s.typeParameters?.params.length ? "E-TYPE-PARAM" : "E-PARAM-SHAPE")
    }
  }
  result.sort((a, b) => a.unit.span.start - b.unit.span.start)
  return result
}
