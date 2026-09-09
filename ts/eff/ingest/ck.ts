// Compiler API engine, retargeted from foldlab experiments/lift-harness/src/lift.ts
// at 4005d34f. Independent of read.ts and the oxc engine; shared tables are data only.
import ts from "typescript"
import { decodeEff, type Eff, type Term, type Lit, type CauseTerm, type Stmt, type ActionTerm, type LayerTerm, type ServiceKey, type ForkOptions } from "../eff.gen.ts"
import { rows } from "../profile.gen.ts"

class Decline extends Error {}
const bad = (reason: string): never => { throw new Decline(reason) }
const unit: Term = { _tag: "lit", value: { _tag: "unit" } }

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
      case "suspend": case "exit": case "uninterruptible": case "interruptible": case "whileLoop": case "scoped":
        return { ...e, body: eff(e.body, child(0)) }
      case "bind": return { ...e, first: eff(e.first, child(0)), rest: eff(e.rest, child(1)) }
      case "gen": return { ...e, body: spine(e.body, child(0), stmt) }
      case "catchCause": return { ...e, body: eff(e.body, child(0)), handler: eff(e.handler, child(1)) }
      case "matchCause": return { ...e, body: eff(e.body, child(0)), onValue: eff(e.onValue, child(1)), onCause: eff(e.onCause, child(2)) }
      case "onExit": return { ...e, body: eff(e.body, child(0)), finalizer: eff(e.finalizer, child(1)) }
      case "branch": return { ...e, thenB: eff(e.thenB, child(0)), elseB: eff(e.elseB, child(1)) }
      case "withFiber": return { ...e, action: action(e.action, child(0)) }
      case "acquireRelease": return { ...e, acquire: eff(e.acquire, child(0)), release: eff(e.release, child(1)) }
      case "choose": return { ...e, left: eff(e.left, child(0)), right: eff(e.right, child(1)) }
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
  constructor(readonly file: ts.SourceFile) {}
  unwrap(x: ts.Expression): ts.Expression {
    while (ts.isParenthesizedExpression(x)) x = x.expression
    return x
  }
  name(x: ts.Expression): string {
    x = this.unwrap(x)
    if (ts.isIdentifier(x)) return x.text
    if (ts.isPropertyAccessExpression(x) && !x.questionDotToken) return `${this.name(x.expression)}.${x.name.text}`
    return bad("head")
  }
  call(x: ts.Expression): ts.CallExpression {
    x = this.unwrap(x)
    return ts.isCallExpression(x) && !x.questionDotToken ? x : bad("call")
  }
  arity(args: readonly ts.Expression[], n: number): void { if (args.length !== n) bad("arity") }
  at(args: readonly ts.Expression[], i: number): ts.Expression { return args[i] ?? bad("argument") }
  variable(x: ts.Expression, env: readonly string[]): number | undefined {
    x = this.unwrap(x)
    const i = ts.isIdentifier(x) ? env.lastIndexOf(x.text) : -1
    return i < 0 ? undefined : i
  }
  literal(x: ts.Expression): Lit {
    x = this.unwrap(x)
    if (x.kind === ts.SyntaxKind.TrueKeyword) return { _tag: "bool", value: true }
    if (x.kind === ts.SyntaxKind.FalseKeyword) return { _tag: "bool", value: false }
    if (ts.isIdentifier(x) && x.text === "undefined") return { _tag: "unit" }
    if (ts.isNumericLiteral(x) && Number.isSafeInteger(Number(x.text))) return { _tag: "nat", value: Number(x.text) }
    if (ts.isStringLiteral(x)) return { _tag: "str", value: x.text }
    return bad("literal")
  }
  term(x: ts.Expression, env: readonly string[]): Term {
    x = this.unwrap(x)
    const i = this.variable(x, env)
    if (i !== undefined) return { _tag: "var", index: i }
    if (ts.isCallExpression(x)) return { _tag: "app", atom: this.name(x.expression), args: x.arguments.map(a => this.term(a, env)) }
    return { _tag: "lit", value: this.literal(x) }
  }
  arrow(x: ts.Expression, env: readonly string[], count: number): { body: ts.ConciseBody; env: readonly string[] } {
    x = this.unwrap(x)
    if (!ts.isArrowFunction(x) || x.parameters.length !== count) return bad("closure")
    const names = x.parameters.map(p => ts.isIdentifier(p.name) ? p.name.text : bad("parameter"))
    return { body: x.body, env: [...env, ...names] }
  }
  expression(x: ts.ConciseBody): ts.Expression { return ts.isBlock(x) ? bad("block") : x }
  fields(x: ts.Expression): Map<string, ts.Expression> {
    x = this.unwrap(x)
    if (!ts.isObjectLiteralExpression(x)) return bad("object")
    const out = new Map<string, ts.Expression>()
    for (const p of x.properties) {
      if (!ts.isPropertyAssignment(p) || !ts.isIdentifier(p.name) || out.has(p.name.text)) return bad("property")
      out.set(p.name.text, p.initializer)
    }
    return out
  }
  field(m: Map<string, ts.Expression>, k: string): ts.Expression { return m.get(k) ?? bad(`field ${k}`) }
  key(x: ts.Expression): ServiceKey {
    const c = this.call(x)
    if (this.name(c.expression) !== "Context.Service" || c.arguments.length !== 1) return bad("key")
    const v = this.literal(this.at(c.arguments, 0))
    if (v._tag !== "str") return bad("key name")
    const m = /^k(0|[1-9][0-9]*)_(0|[1-9][0-9]*)$/.exec(v.value)
    if (!m) return bad("key number")
    const name = Number(m[1]), service = Number(m[2])
    return { name: { value: name }, service: { value: service } }
  }
  cause(x: ts.Expression, env: readonly string[]): CauseTerm {
    const c = this.call(x), h = this.name(c.expression), a = c.arguments
    if (h === "Cause.fail" || h === "Cause.die") {
      this.arity(a, 1); const t = this.term(this.at(a, 0), env)
      return h === "Cause.fail" ? { _tag: "fail", error: t } : { _tag: "die", defect: t }
    }
    if (h === "Cause.interrupt" && a.length <= 1) return { _tag: "interrupt", interruptor: a.length ? this.term(this.at(a, 0), env) : null }
    if (h === "Cause.combine") { this.arity(a, 2); return { _tag: "both", left: this.cause(this.at(a, 0), env), right: this.cause(this.at(a, 1), env) } }
    return bad("cause")
  }
  options(x: ts.Expression, daemon: boolean): ForkOptions {
    const m = this.fields(x), s = this.literal(this.field(m, "startImmediately")), u = this.literal(this.field(m, "uninterruptible"))
    if (m.size !== 2 || s._tag !== "bool") return bad("fork options")
    const maskMode = u._tag === "bool" ? (u.value ? "uninterruptible" : "interruptible") : u._tag === "str" && u.value === "inherit" ? "inherit" : bad("mask")
    return { startImmediately: s.value, daemon, maskMode }
  }
  layer(x: ts.Expression): LayerTerm {
    x = this.unwrap(x)
    if (ts.isIdentifier(x)) return { _tag: "ref", target: layerPath(x.text) }
    const c = this.call(x)
    const callee = this.unwrap(c.expression)
    if (ts.isPropertyAccessExpression(callee) && callee.name.text === "pipe") {
      this.arity(c.arguments, 1)
      const segment = this.call(this.at(c.arguments, 0)), h = this.name(segment.expression)
      this.arity(segment.arguments, 1)
      const self = this.layer(callee.expression), that = this.layer(this.at(segment.arguments, 0))
      if (h === "Layer.provide") return { _tag: "provide", self, that }
      if (h === "Layer.provideMerge") return { _tag: "provideMerge", self, that }
      return bad("layer pipe")
    }
    const h = this.name(c.expression), a = c.arguments
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
  stmts(input: readonly ts.Statement[], initial: readonly string[]): readonly Stmt[] {
    let env = [...initial]
    const out: Stmt[] = []
    for (const s of input) {
      if (ts.isVariableStatement(s) && s.declarationList.flags & ts.NodeFlags.Const) {
        const d = s.declarationList.declarations[0]
        if (s.declarationList.declarations.length !== 1 || !d || !ts.isIdentifier(d.name) || !d.initializer) return bad("binding")
        const y = this.unwrap(d.initializer)
        if (!ts.isYieldExpression(y) || !y.asteriskToken || !y.expression) return bad("yield binding")
        out.push({ _tag: "bindYield", effect: this.eff(y.expression, env) }); env.push(d.name.text)
      } else if (ts.isExpressionStatement(s)) {
        const y = this.unwrap(s.expression)
        if (!ts.isYieldExpression(y) || !y.asteriskToken || !y.expression) return bad("yield statement")
        out.push({ _tag: "yieldDiscard", effect: this.eff(y.expression, env) })
      } else if (ts.isReturnStatement(s) && s.expression) out.push({ _tag: "ret", value: this.term(s.expression, env) })
      else if (ts.isBreakStatement(s) && !s.label) out.push({ _tag: "breakLoop" })
      else if (ts.isIfStatement(s)) {
        if (!ts.isBlock(s.thenStatement) || (s.elseStatement && !ts.isBlock(s.elseStatement))) return bad("if body")
        out.push({ _tag: "ifElse", test: this.term(s.expression, env), thenB: this.stmts(s.thenStatement.statements, env), elseB: s.elseStatement ? this.stmts(s.elseStatement.statements, env) : [] })
      } else if (ts.isWhileStatement(s) && this.unwrap(s.expression).kind === ts.SyntaxKind.TrueKeyword && ts.isBlock(s.statement)) {
        out.push({ _tag: "whileTrue", body: this.stmts(s.statement.statements, env) })
      } else return bad("statement")
    }
    return out
  }
  eff(x: ts.Expression, env: readonly string[]): Eff {
    x = this.unwrap(x)
    const variable = this.variable(x, env)
    if (variable !== undefined) return { _tag: "yieldError", error: { _tag: "var", index: variable } }
    if (!ts.isCallExpression(x)) {
      if (ts.isIdentifier(x) || ts.isPropertyAccessExpression(x)) {
        const h = this.name(x)
        if (h === "Effect.fiberId") return { _tag: "withFiber", action: { _tag: "getId" } }
        const row = rows.find(r => r.row.spelling === h && r.row.shape === "value")
        if (row) return row.row.kind === "async" ? { _tag: "callback", register: row.op, request: unit } : { _tag: "perform", op: row.op, request: unit }
      }
      return { _tag: "yieldError", error: this.term(x, env) }
    }
    const h = this.name(x.expression), a = x.arguments
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
        if (ts.isBlock(fn.body)) return this.loop(fn.body, env)
        const b = this.unwrap(fn.body)
        if (ts.isConditionalExpression(b)) return { _tag: "branch", test: this.term(b.condition, env), thenB: this.eff(b.whenTrue, env), elseB: this.eff(b.whenFalse, env) }
        return { _tag: "suspend", body: this.eff(b, env) }
      }
      case "Effect.flatMap": this.arity(a, 2); return { _tag: "bind", first: e(0), rest: k(1) }
      case "Effect.catchCause": this.arity(a, 2); return { _tag: "catchCause", body: e(0), handler: k(1) }
      case "Effect.onExit": this.arity(a, 2); return { _tag: "onExit", body: e(0), finalizer: k(1) }
      case "Effect.acquireRelease": this.arity(a, 2); return { _tag: "acquireRelease", acquire: e(0), release: k(1, 2) }
      case "Effect.gen": {
        this.arity(a, 1); const fn = this.unwrap(arg(0))
        if (!ts.isFunctionExpression(fn) || !fn.asteriskToken || fn.parameters.length) return bad("generator")
        return { _tag: "gen", body: this.stmts(fn.body.statements, env) }
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
      case "Effect.raceAll": { this.arity(a, 1); const list = this.unwrap(arg(0)); if (!ts.isArrayLiteralExpression(list)) return bad("entrants"); return { _tag: "withFiber", action: { _tag: "raceAll", entrants: list.elements.map(y => this.eff(y, env)) } } }
      case "Effect.withFiber": {
        this.arity(a, 1); const fn = this.arrow(arg(0), env, 0)
        if (!ts.isBlock(fn.body) || fn.body.statements.length !== 2) return bad("runIn callback")
        const [link, ret] = fn.body.statements
        if (!link || !ts.isExpressionStatement(link) || !ret || !ts.isReturnStatement(ret) || !ret.expression || this.name(ret.expression) !== "Effect.void") return bad("runIn body")
        const c = this.call(link.expression); this.arity(c.arguments, 2)
        if (this.name(c.expression) !== "Fiber.runIn") return bad("runIn head")
        return { _tag: "withFiber", action: { _tag: "runIn", target: this.term(this.at(c.arguments, 0), env), scope: this.term(this.at(c.arguments, 1), env) } }
      }
    }
    const trailingName = (z: ts.Expression): string | undefined => { z = this.unwrap(z); return ts.isStringLiteral(z) ? JSON.stringify(z.text) : ts.isIdentifier(z) ? z.text : undefined }
    for (const r of rows.filter(r => r.row.spelling === h && r.row.shape !== "value")) {
      const count = r.row.shape === "tupleCall" ? 2 : r.row.request._tag === "unit" ? 0 : 1
      if (a.length !== count + r.row.trailing.length || !r.row.trailing.every((v, i) => trailingName(arg(count + i)) === v)) continue
      const types = x.typeArguments?.map(n => n.getText(this.file)) ?? []
      if (types.join(",") !== r.row.typeArgs.join(",")) continue
      let request = unit
      if (count === 1) request = t(0)
      if (count === 2) {
        const left = t(0), right = t(1)
        const x0 = this.unwrap(arg(0)), x1 = this.unwrap(arg(1))
        let saved: ts.Expression | undefined
        if (ts.isCallExpression(x0) && ts.isCallExpression(x1) && this.name(x0.expression) === "fst" && this.name(x1.expression) === "snd" && x0.arguments.length === 1 && x1.arguments.length === 1) {
          const p = this.unwrap(this.at(x0.arguments, 0)), q = this.unwrap(this.at(x1.arguments, 0))
          if (ts.isIdentifier(p) && ts.isIdentifier(q) && p.text === q.text) saved = p
        }
        request = saved ? this.term(saved, env) : { _tag: "app", atom: "pair", args: [left, right] }
      }
      return r.row.kind === "async" ? { _tag: "callback", register: r.op, request } : { _tag: "perform", op: r.op, request }
    }
    return { _tag: "yieldError", error: this.term(x, env) }
  }
  loop(block: ts.Block, env: readonly string[]): Eff {
    const [init, ret] = block.statements
    if (block.statements.length !== 2 || !init || !ts.isVariableStatement(init) || !ret || !ts.isReturnStatement(ret) || !ret.expression) return bad("loop")
    const decl = init.declarationList.declarations[0]
    if (!decl || init.declarationList.declarations.length !== 1 || !ts.isIdentifier(decl.name) || !decl.initializer) return bad("cursor")
    const c = this.call(ret.expression); this.arity(c.arguments, 1)
    if (this.name(c.expression) !== "Effect.whileLoop") return bad("loop head")
    const m = this.fields(this.at(c.arguments, 0)), inner = [...env, decl.name.text]
    if (m.size !== 3) return bad("loop fields")
    const test = this.arrow(this.field(m, "while"), inner, 0), body = this.arrow(this.field(m, "body"), inner, 0), step = this.arrow(this.field(m, "step"), inner, 1)
    if (!ts.isBlock(step.body) || step.body.statements.length !== 1) return bad("step")
    const s = step.body.statements[0]
    if (!s || !ts.isExpressionStatement(s) || !ts.isBinaryExpression(s.expression) || s.expression.operatorToken.kind !== ts.SyntaxKind.EqualsToken || s.expression.left.getText(this.file) !== decl.name.text) return bad("step assignment")
    return { _tag: "whileLoop", initial: this.term(decl.initializer, env), test: this.term(this.expression(test.body), inner), body: this.eff(this.expression(body.body), inner), step: this.term(s.expression.right, step.env) }
  }
}

/** Explicit printer-image test seam. Never called by foreign recognition. */
export function readPrintedSource(source: string, filename = "program.ts"): Eff {
  const file = ts.createSourceFile(filename, source, ts.ScriptTarget.Latest, false, ts.ScriptKind.TS)
  if ((file as ts.SourceFile & { parseDiagnostics: readonly ts.Diagnostic[] }).parseDiagnostics.length) return bad("parse")
  // Keep the existing test-context projection, adding only named layer declarations.
  const statements = file.statements.filter(s => ts.isExpressionStatement(s) || ts.isVariableStatement(s) &&
    (s.modifiers?.some(m => m.kind === ts.SyntaxKind.ExportKeyword) || s.declarationList.declarations.some(d => ts.isIdentifier(d.name) && d.name.text.startsWith("L_"))))
  const last = statements.at(-1)
  if (!last) return bad("program")
  const constant = (s: ts.Statement): { name: string; value: ts.Expression } => {
    if (!ts.isVariableStatement(s) || !(s.declarationList.flags & ts.NodeFlags.Const) || s.declarationList.declarations.length !== 1) return bad("program statement")
    const d = s.declarationList.declarations[0]!
    if (!ts.isIdentifier(d.name) || !d.initializer) return bad("program initializer")
    return { name: d.name.text, value: d.initializer }
  }
  const reader = new CompilerReader(file)
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
  let program = reader.eff(ts.isExpressionStatement(last) ? last.expression : constant(last).value, [])
  for (const d of declarations) program = restoreLayer(program, d.path, d.layer)
  return decodeEff(program)
}

import type { Verdict, RefusalCode, Key, LayerBinding } from "./contract.ts"
import { taxonomy } from "../taxonomy.gen.ts"
import { heads } from "../profile.gen.ts"
import { forms } from "../forms.gen.ts"
import { encodeProgram } from "../wire.gen.ts"

class ForeignRefusal extends Error {
  constructor(readonly code: RefusalCode, readonly value: string) { super(code) }
}
const refuseForeign = (code: RefusalCode, value: string): never => { throw new ForeignRefusal(code, value) }
const knownHeads = new Set<string>([...heads, ...rows.map(r => r.row.spelling), ...forms.rows.map(r => r.head)])
const atoms = new Set(["succ", "pred", "isZero", "not", "add", "lt", "eq", "pair", "fst", "snd", "strings"])

class ForeignCompilerReader extends CompilerReader {
  readonly keys: Key[] = []
  readonly layers: LayerBinding[] = []
  private readonly layerDefinitions: { sourceName: string; value: LayerTerm }[] = []
  private referenceCut: number | undefined
  constructor(file: ts.SourceFile, readonly bindings: Map<string, string>, readonly declarations: Map<string, { at: number; value: ts.Expression; constant?: boolean }>, readonly current: number) { super(file) }
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
      if (!entry) { entry = { ...old, ordinal: this.keys.length + 4 }; this.keys.push(entry) }
      return { name: { value: entry.ordinal }, service: key.service }
    }, true))
  }
  override name(x: ts.Expression): string {
    const rawName = (e: ts.Expression): string => {
      e = this.unwrap(e)
      if (ts.isIdentifier(e)) return e.text
      if (ts.isPropertyAccessExpression(e) && !e.questionDotToken) return rawName(e.expression) + "." + e.name.text
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
  override literal(x: ts.Expression): Lit {
    const y = this.unwrap(x)
    if (ts.isNewExpression(y)) return refuseForeign("E-NODE-SHAPE", "new")
    if (ts.isAwaitExpression(y)) return refuseForeign("E-NODE-SHAPE", "await")
    if (ts.isYieldExpression(y)) return refuseForeign("E-YIELD-POSITION", "expression")
    if (ts.isTemplateExpression(y) || ts.isNoSubstitutionTemplateLiteral(y)) return refuseForeign("E-NODE-SHAPE", "template")
    if (ts.isNumericLiteral(y) && (!/^(0|[1-9][0-9]*)$/.test(y.getText(this.file)) || !Number.isSafeInteger(Number(y.text)))) return refuseForeign("E-ARG-DYNAMIC", "number")
    if (ts.isStringLiteral(y) && y.getText(this.file).slice(1, -1) !== JSON.stringify(y.text).slice(1, -1)) return refuseForeign("E-ARG-DYNAMIC", "string")
    try { return super.literal(y) } catch (e) { if (e instanceof Decline) return refuseForeign("E-ARG-DYNAMIC", "literal"); throw e }
  }
  override term(x: ts.Expression, env: readonly string[]): Term {
    const y = this.unwrap(x)
    if (ts.isIdentifier(y) && y.text !== "undefined" && this.variable(y, env) === undefined) return refuseForeign("E-REF-UNBOUND", y.text)
    if (ts.isCallExpression(y)) {
      if (this.variable(y.expression, env) !== undefined) return refuseForeign("E-ANSWER-HIGHER-ORDER", super.name(y.expression))
      if (!atoms.has(this.name(y.expression))) return refuseForeign("E-ARG-DYNAMIC", "term")
    }
    return super.term(y, env)
  }
  override arrow(x: ts.Expression, env: readonly string[], count: number): { body: ts.ConciseBody; env: readonly string[] } {
    const a = this.unwrap(x)
    if (!ts.isArrowFunction(a)) return refuseForeign("E-ARG-CLOSURE", "continuation")
    if (a.parameters.length !== count || a.parameters.some(p => !ts.isIdentifier(p.name))) return refuseForeign("E-BIND-SHAPE", "parameters")
    return super.arrow(a, env, count)
  }
  override stmts(input: readonly ts.Statement[], initial: readonly string[]): readonly Stmt[] {
    const out: Stmt[] = [], env = [...initial]
    for (const s of input) {
      if (ts.isForStatement(s) || ts.isForOfStatement(s) || ts.isForInStatement(s)) return refuseForeign("E-STMT-SHAPE", "for")
      if (ts.isTryStatement(s)) return refuseForeign("E-STMT-SHAPE", "try")
      if (ts.isVariableStatement(s) && !(s.declarationList.flags & ts.NodeFlags.Const)) return refuseForeign("E-STMT-SHAPE", "let")
      if (ts.isReturnStatement(s)) {
        if (!s.expression) return refuseForeign("E-RETURN-SHAPE", "term")
        if (ts.isYieldExpression(this.unwrap(s.expression))) return refuseForeign("E-YIELD-POSITION", "return")
        try { out.push({ _tag: "ret", value: this.term(s.expression, env) }) }
        catch (e) { if (e instanceof ForeignRefusal && e.code === "E-ANSWER-HIGHER-ORDER") throw e; return refuseForeign("E-RETURN-SHAPE", "term") }
        continue
      }
      const rows = super.stmts([s], env)
      out.push(...rows)
      if (ts.isVariableStatement(s)) { const d = s.declarationList.declarations[0]; if (d && ts.isIdentifier(d.name)) env.push(d.name.text) }
    }
    return out
  }
  declaration(id: ts.Identifier): ts.Expression {
    if (this.bindings.has(id.text)) return refuseForeign("E-IMPORT-OPAQUE", id.text)
    const d = this.declarations.get(id.text)
    if (!d) return refuseForeign("E-REF-UNBOUND", id.text)
    if (d.at >= (this.referenceCut ?? this.current)) return refuseForeign("E-REF-FORWARD", id.text)
    return d.value
  }
  override key(x: ts.Expression): ServiceKey {
    x = this.unwrap(x)
    if (ts.isIdentifier(x)) x = this.declaration(x)
    const c = this.call(x)
    const inner = this.unwrap(c.expression)
    const factory = ts.isCallExpression(inner) ? inner : c
    if (this.name(factory.expression) !== "Context.Service") return refuseForeign("E-OP-UNKNOWN", "key")
    this.arity(c.arguments, 1)
    const shape = factory.typeArguments?.at(-1)?.getText(this.file)
    const service = shape === "number" ? 4 : shape === "boolean" ? 5 : shape === "void" || shape === "unknown" ? 6 : shape === "Ref.Ref<number>" ? 7 : refuseForeign("E-TYPE-PARAM", "service shape")
    const id = this.literal(this.at(c.arguments, 0))
    if (id._tag !== "str") return refuseForeign("E-ARG-DYNAMIC", "service identifier")
    let entry = this.keys.find(k => k.sourceId === id.value)
    if (!entry) { entry = { ordinal: this.keys.length + 4, service, sourceId: id.value }; this.keys.push(entry) }
    if (entry.service !== service) return refuseForeign("E-TYPE-PARAM", "service identity has conflicting shapes")
    return { name: { value: entry.ordinal }, service: { value: service } }
  }
  segment(head: string, args: readonly ts.Expression[], first: Eff, env: readonly string[]): Eff {
    const at = (i: number) => this.at(args, i)
    const cont = (x: ts.Expression, count = 1): Eff => {
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
    if (head === "Effect.onExit") { this.arity(args, 1); return { _tag: "onExit", body: first, finalizer: cont(at(0)) } }
    if (head === "Effect.andThen" || head === "Effect.tap") {
      this.arity(args, 1)
      const x = this.unwrap(at(0))
      let rest: Eff
      if (ts.isArrowFunction(x)) rest = x.parameters.length ? cont(x) : this.eff(this.expression(x.body), [...env, "\u0000"])
      else rest = this.eff(x, [...env, "\u0000"])
      if (head === "Effect.tap") rest = { _tag: "bind", first: rest, rest: { _tag: "succeed", value: { _tag: "var", index: env.length } } }
      return { _tag: "bind", first, rest }
    }
    if (head === "Effect.as" || head === "Effect.asVoid") {
      this.arity(args, head === "Effect.as" ? 1 : 0)
      return { _tag: "bind", first, rest: { _tag: "succeed", value: head === "Effect.as" ? { _tag: "lit", value: this.literal(at(0)) } : unit } }
    }
    if (head === "Effect.ensuring") { this.arity(args, 1); return { _tag: "onExit", body: first, finalizer: this.eff(at(0), [...env, "\u0000"]) } }
    if (["Effect.exit", "Effect.scoped", "Effect.interruptible", "Effect.uninterruptible"].includes(head)) {
      this.arity(args, 0)
      const tag = head === "Effect.exit" ? "exit" : head === "Effect.scoped" ? "scoped" : head === "Effect.interruptible" ? "interruptible" : "uninterruptible"
      return { _tag: tag, body: first }
    }
    if (head === "Effect.matchCause" || head === "Effect.matchCauseEffect") {
      this.arity(args, 1); const m = this.fields(at(0))
      if (m.size !== 2) return refuseForeign("E-BIND-SHAPE", "match fields")
      const arm = (key: string): Eff => {
        const a = this.arrow(this.field(m, key), env, 1), x = this.expression(a.body)
        return head === "Effect.matchCause" ? { _tag: "succeed", value: this.term(x, a.env) } : this.eff(x, a.env)
      }
      return { _tag: "matchCause", body: first, onValue: arm("onSuccess"), onCause: arm("onFailure") }
    }
    if (head === "Effect.provideService") { this.arity(args, 2); const key = this.key(at(0)); return { _tag: "provideService", body: first, key, value: { _tag: "lit", value: this.provided(key, at(1)) } } }
    if (head === "Effect.provide") {
      if (args.length < 1 || args.length > 2) return refuseForeign("E-BIND-SHAPE", "arity")
      if (ts.isArrayLiteralExpression(this.unwrap(at(0)))) return refuseForeign("E-OP-UNKNOWN", "Layer.mergeAll")
      const layer = this.layer(at(0))
      let isLocal = false
      if (args.length === 2) { const m = this.fields(at(1)), l = this.literal(this.field(m, "local")); if (m.size !== 1 || l._tag !== "bool" || !l.value) return refuseForeign("E-BIND-SHAPE", "provide options"); isLocal = true }
      return { _tag: "provideLayer", body: first, layer, isLocal }
    }
    if (["Effect.forkChild", "Effect.forkDetach", "Effect.forkIn", "Effect.forkScoped"].includes(head)) {
      const inScope = head === "Effect.forkIn", index = inScope ? 1 : 0
      const daemon = head !== "Effect.forkChild"
      if (args.length !== index && args.length !== index + 1) return refuseForeign("E-BIND-SHAPE", "arity")
      const options = args[index] ? this.options(at(index), daemon) : { startImmediately: false, daemon, maskMode: "inherit" as const }
      return { _tag: "withFiber", action: inScope ? { _tag: "forkIn", program: first, scope: this.term(at(0), env), options } : head === "Effect.forkScoped" ? { _tag: "forkScoped", program: first, options } : { _tag: "fork", program: first, options } }
    }
    if (!knownHeads.has(head)) return refuseForeign("E-OP-UNKNOWN", head)
    return refuseForeign("E-BIND-SHAPE", "pipe segment")
  }
  pipeSegment(x: ts.Expression, first: Eff, env: readonly string[]): Eff {
    x = this.unwrap(x)
    if (ts.isArrowFunction(x)) {
      if (x.parameters.length !== 1 || !ts.isIdentifier(x.parameters[0]!.name) || ts.isBlock(x.body)) return refuseForeign("E-BIND-SHAPE", "eta")
      const name = x.parameters[0]!.name.text, body = this.call(x.body), callee = this.unwrap(body.expression)
      if (ts.isPropertyAccessExpression(callee) && callee.name.text === "pipe" && ts.isIdentifier(this.unwrap(callee.expression)) && super.name(callee.expression) === name) {
        let out = first
        for (const seg of body.arguments) out = this.pipeSegment(seg, out, env)
        return out
      }
      const args = body.arguments
      if (!args[0] || !ts.isIdentifier(this.unwrap(args[0])) || super.name(args[0]) !== name) return refuseForeign("E-BIND-SHAPE", "eta")
      let duplicate = false
      const visit = (n: ts.Node) => {
        if ((ts.isArrowFunction(n) || ts.isFunctionExpression(n)) && n.parameters.some(p => ts.isIdentifier(p.name) && p.name.text === name)) return
        if (ts.isIdentifier(n) && n.text === name) duplicate = true
        ts.forEachChild(n, visit)
      }
      args.slice(1).forEach(visit)
      if (duplicate) return refuseForeign("E-BIND-SHAPE", "eta reuse")
      return this.segment(this.name(callee), args.slice(1), first, env)
    }
    if (ts.isCallExpression(x)) return this.segment(this.name(x.expression), x.arguments, first, env)
    const head = this.name(x)
    if (!(forms.unaryRefs as readonly string[]).includes(head)) return refuseForeign("E-BIND-SHAPE", "unary reference")
    return this.segment(head, [], first, env)
  }
  lambdaAtom(x: ts.Expression): string {
    x = this.unwrap(x)
    if (!ts.isArrowFunction(x) || x.parameters.length !== 1 || !ts.isIdentifier(x.parameters[0]!.name) || ts.isBlock(x.body)) return refuseForeign("E-ARG-CLOSURE", "lambda atom")
    const name = x.parameters[0]!.name.text, b = this.unwrap(x.body)
    const param = (e: ts.Expression) => { e = this.unwrap(e); return ts.isIdentifier(e) && e.text === name }
    const number = (e: ts.Expression, n: number) => { const v = this.literal(e); return v._tag === "nat" && v.value === n }
    const option = (e: ts.Expression, head: string, n?: number) => {
      e = this.unwrap(e)
      if (!ts.isCallExpression(e) || this.name(e.expression) !== head) return false
      return n === undefined ? e.arguments.length === 0 : e.arguments.length === 1 && number(this.at(e.arguments, 0), n)
    }
    if (ts.isBinaryExpression(b) && param(b.left)) {
      if (b.operatorToken.kind === ts.SyntaxKind.PlusToken && number(b.right, 1)) return "incr"
      if (b.operatorToken.kind === ts.SyntaxKind.AsteriskToken && number(b.right, 2)) return "double"
    }
    if (option(b, "Option.none")) return "noChange"
    if (ts.isConditionalExpression(b)) {
      const test = this.unwrap(b.condition)
      if (ts.isBinaryExpression(test) && test.operatorToken.kind === ts.SyntaxKind.GreaterThanToken && param(test.left) && number(test.right, 0) && option(b.whenTrue, "Option.some", 0) && option(b.whenFalse, "Option.none")) return "zeroWhenPositive"
    }
    return refuseForeign("E-ARG-CLOSURE", "lambda atom")
  }
  duration(x: ts.Expression): number {
    x = this.unwrap(x)
    let numerator: bigint, denominator = 1n, factor = 1n, divisor = 1n
    if (ts.isCallExpression(x)) {
      const h = this.name(x.expression)
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
  provided(key: ServiceKey, x: ts.Expression): Lit {
    const value = this.literal(x), expected = key.service.value === 4 ? "nat" : key.service.value === 5 ? "bool" : key.service.value === 6 ? "unit" : "handle"
    if (value._tag !== expected) return refuseForeign("E-ARG-DYNAMIC", "service literal shape")
    return value
  }
  override layer(x: ts.Expression): LayerTerm {
    x = this.unwrap(x)
    if (ts.isIdentifier(x)) {
      const value = this.declaration(x), declaration = this.declarations.get(x.text)!
      if (!declaration.constant) return refuseForeign("E-REF-UNBOUND", x.text)
      const existing = this.layerDefinitions.findIndex(d => d.sourceName === x.text)
      if (existing >= 0) return { _tag: "ref", target: [existing] }
      const previous = this.referenceCut
      this.referenceCut = declaration.at
      let layer: LayerTerm
      try { layer = this.layer(value) }
      catch (e) {
        const code = e instanceof ForeignRefusal ? e.code : e instanceof Decline ? "E-NODE" : undefined
        if (code) return refuseForeign("E-REF-UNBOUND", `${x.text}: ${code}`)
        throw e
      } finally { this.referenceCut = previous }
      const index = this.layerDefinitions.length
      this.layerDefinitions.push({ sourceName: x.text, value: layer })
      return { _tag: "ref", target: [index] }
    }
    const c = this.call(x), callee = this.unwrap(c.expression)
    if (ts.isPropertyAccessExpression(callee) && callee.name.text === "pipe") return super.layer(x)
    if (this.name(c.expression) === "Layer.succeed") {
      this.arity(c.arguments, 2)
      const key = this.key(this.at(c.arguments, 0))
      return { _tag: "succeed", key, value: this.provided(key, this.at(c.arguments, 1)) }
    }
    return super.layer(x)
  }
  override eff(x: ts.Expression, env: readonly string[]): Eff {
    x = this.unwrap(x)
    if (ts.isArrowFunction(x) || ts.isFunctionExpression(x)) return refuseForeign(x.typeParameters?.length ? "E-TYPE-PARAM" : "E-PARAM-SHAPE", x.typeParameters?.length ? "generic unit" : "function")
    if (ts.isConditionalExpression(x)) return refuseForeign("E-BRANCH", "conditional")
    if (ts.isAsExpression(x) || ts.isSatisfiesExpression(x) || ts.isTypeAssertionExpression(x) || ts.isNonNullExpression(x)) return refuseForeign("E-SPINE-ESCAPE", "assertion")
    if (this.variable(x, env) !== undefined) return super.eff(x, env)
    if (ts.isIdentifier(x) && this.variable(x, env) === undefined && x.text !== "undefined" && !this.bindings.has(x.text)) {
      const decl = this.unwrap(this.declaration(x))
      if (ts.isCallExpression(decl) && this.name(ts.isCallExpression(this.unwrap(decl.expression)) ? this.call(decl.expression).expression : decl.expression) === "Context.Service") return { _tag: "service", key: this.key(x) }
      const previous = this.referenceCut
      this.referenceCut = this.declarations.get(x.text)!.at
      try { return this.eff(decl, env) }
      catch (e) { if (e instanceof ForeignRefusal) return refuseForeign("E-REF-UNBOUND", `${x.text}: ${e.code}`); throw e }
      finally { this.referenceCut = previous }
    }
    if (ts.isCallExpression(x)) {
      const callee = this.unwrap(x.expression)
      if (x.questionDotToken || (ts.isPropertyAccessExpression(callee) && callee.questionDotToken)) return refuseForeign("E-SPINE-ESCAPE", "optional")
      if (x.arguments.some(ts.isSpreadElement)) return refuseForeign("E-SPINE-ESCAPE", "spread")
      if (ts.isPropertyAccessExpression(callee) && callee.name.text === "pipe") {
        let first = this.eff(callee.expression, env)
        for (const segment of x.arguments) first = this.pipeSegment(segment, first, env)
        return first
      }
      if (ts.isCallExpression(callee)) {
        this.arity(x.arguments, 1)
        return this.segment(this.name(callee.expression), callee.arguments, this.eff(this.at(x.arguments, 0), env), env)
      }
      const h = this.name(x.expression)
      if (h === "Effect.fn" || h === "Effect.fnUntraced") return refuseForeign("E-PARAM-SHAPE", "function")
      if (["Effect.catchTag", "Effect.catchTags", "Effect.catchIf", "Effect.catch", "Effect.mapError", "Effect.match", "Effect.orElseSucceed"].includes(h)) return refuseForeign("E-HANDLER", h)
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
        if (!ts.isArrowFunction(release) || release.parameters.length < 1 || release.parameters.length > 2) return refuseForeign("E-ARG-CLOSURE", "release")
        const fn = this.arrow(release, env, release.parameters.length)
        return { _tag: "acquireRelease", acquire: this.eff(this.at(x.arguments, 0), env), release: this.eff(this.expression(fn.body), release.parameters.length === 1 ? [...fn.env, "\u0000"] : fn.env) }
      }
      if (h === "Effect.sleep") {
        this.arity(x.arguments, 1)
        const r = rows.find(r => r.row.spelling === h)!
        return { _tag: "callback", register: r.op, request: { _tag: "lit", value: { _tag: "nat", value: this.duration(this.at(x.arguments, 0)) } } }
      }
      if (h === "Effect.fail" || h === "Effect.die") {
        this.arity(x.arguments, 1)
        let value: Lit
        try { value = this.literal(this.at(x.arguments, 0)) } catch { return refuseForeign("E-FAIL-NOT-DOCUMENTED", "literal required") }
        const t: Term = { _tag: "lit", value }
        return h === "Effect.fail" ? { _tag: "fail", error: t } : { _tag: "failCause", cause: { _tag: "die", defect: t } }
      }
      if (h === "Effect.provideService") {
        this.arity(x.arguments, 3)
        const body = this.eff(this.at(x.arguments, 0), env), key = this.key(this.at(x.arguments, 1)), value = this.provided(key, this.at(x.arguments, 2))
        return { _tag: "provideService", body, key, value: { _tag: "lit", value } }
      }
      if (x.arguments.some(a => ts.isArrowFunction(this.unwrap(a))) && rows.some(r => r.row.spelling === h)) {
        for (const r of rows.filter(r => r.row.spelling === h)) {
          const count = r.row.shape === "tupleCall" ? 2 : r.row.request._tag === "unit" ? 0 : 1
          if (x.arguments.length !== count + r.row.trailing.length) continue
          const trailing = x.arguments.slice(count).map(a => ts.isArrowFunction(this.unwrap(a)) ? this.lambdaAtom(a) : this.name(a))
          if (!r.row.trailing.every((name, i) => trailing[i] === name)) continue
          const request = count === 0 ? unit : count === 1 ? this.term(this.at(x.arguments, 0), env) : { _tag: "app" as const, atom: "pair", args: [this.term(this.at(x.arguments, 0), env), this.term(this.at(x.arguments, 1), env)] }
          return r.row.kind === "async" ? { _tag: "callback", register: r.op, request } : { _tag: "perform", op: r.op, request }
        }
        return refuseForeign("E-ARG-CLOSURE", "lambda atom")
      }
      if (!knownHeads.has(h) && !atoms.has(h)) return refuseForeign("E-OP-UNKNOWN", h)
    }
    if (!ts.isCallExpression(x) && (ts.isIdentifier(x) || ts.isPropertyAccessExpression(x))) {
      const h = this.name(x)
      if (h === "Effect.void") return { _tag: "succeed", value: unit }
      if (h === "Effect.yieldNow") return { _tag: "yieldNow", priority: 0 }
    }
    return super.eff(x, env)
  }
}

/** Strict foreign admission. The printer-image entrypoint is never a fallback. */
export function recognizeSource(source: string, filename: string, onParse?: (ok: boolean) => void, onTree?: (tree: ts.SourceFile) => void): Verdict[] {
  if (!source.includes('from "effect') && !source.includes("from 'effect")) return []
  const file = ts.createSourceFile(filename, source, ts.ScriptTarget.Latest, false, filename.endsWith(".tsx") ? ts.ScriptKind.TSX : ts.ScriptKind.TS)
  if ((file as ts.SourceFile & { parseDiagnostics: readonly ts.Diagnostic[] }).parseDiagnostics.length) { onParse?.(false); return [] }
  onParse?.(true)
  onTree?.(file)
  const bindings = new Map<string, string>()
  const declarations = new Map<string, { at: number; value: ts.Expression; constant?: boolean }>()
  for (const s of file.statements) {
    if (ts.isImportDeclaration(s) && ts.isStringLiteral(s.moduleSpecifier) && !s.importClause?.isTypeOnly) {
      const mod = s.moduleSpecifier.text, cl = s.importClause
      const base = mod === "effect" ? "" : mod.startsWith("effect/") ? mod.slice(7) : "opaque"
      if (cl?.name) bindings.set(cl.name.text, "opaque")
      const n = cl?.namedBindings
      if (n && ts.isNamespaceImport(n)) bindings.set(n.name.text, base === "" && n.name.text === "Effect" ? "Effect" : base)
      if (n && ts.isNamedImports(n)) for (const i of n.elements) if (!i.isTypeOnly) bindings.set(i.name.text, base === "opaque" ? base : [base, (i.propertyName ?? i.name).text].filter(Boolean).join("."))
    }
    if (ts.isClassDeclaration(s) && s.name) {
      const base = s.heritageClauses?.find(h => h.token === ts.SyntaxKind.ExtendsKeyword)?.types[0]?.expression
      if (base) declarations.set(s.name.text, { at: s.pos, value: base })
    }
    if (ts.isVariableStatement(s)) for (const d of s.declarationList.declarations) if (ts.isIdentifier(d.name) && d.initializer) declarations.set(d.name.text, { at: d.pos, value: d.initializer, constant: Boolean(s.declarationList.flags & ts.NodeFlags.Const) })
  }
  const result: Verdict[] = []
  for (const s of file.statements) {
    if (!ts.isVariableStatement(s) || !(s.declarationList.flags & ts.NodeFlags.Const)) continue
    for (const d of s.declarationList.declarations) {
      if (!ts.isIdentifier(d.name)) {
        const names: string[] = []
        const collect = (n: ts.Node) => { if (ts.isBindingElement(n) && ts.isIdentifier(n.name)) names.push(n.name.text); else ts.forEachChild(n, collect) }
        collect(d.name)
        for (const name of names) result.push({ kind: "refusal", unit: { file: filename, name, span: { start: d.getStart(file), end: d.end } }, code: "E-PROGRAM", detail: "program shape: destructured unit" })
        continue
      }
      if (!d.initializer) continue
      const reader = new ForeignCompilerReader(file, bindings, declarations, d.pos)
      const value = reader.unwrap(d.initializer)
      if (ts.isCallExpression(value)) {
        try { if (reader.name(value.expression) === "Context.Service") continue } catch { /* The unit receives the refusal below. */ }
      }
      try { new ForeignCompilerReader(file, bindings, declarations, d.pos).layer(value); continue } catch { /* A program or refused declaration remains a unit. */ }
      const unit = { file: filename.replaceAll("\\", "/"), name: d.name.text, span: { start: d.getStart(file), end: d.end } }
      try {
        const eff = reader.finish(reader.eff(value, []))
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
  const extra = (name: string, value: ts.Expression | undefined, start: number, end: number, forced?: RefusalCode) => {
    const unit = { file: filename.replaceAll("\\", "/"), name, span: { start, end } }
    if (forced) { result.push({ kind: "refusal", unit, code: forced, detail: taxonomy.find(t => t.code === forced)!.detail.replace("{value}", forced === "E-TYPE-PARAM" ? "generic unit" : "function") }); return }
    const reader = new ForeignCompilerReader(file, bindings, declarations, start)
    try {
      const eff = reader.finish(reader.eff(value!, []))
      result.push({ kind: "lifted", unit, eff, keys: reader.keys, layers: reader.layers, wireHex: Buffer.from(encodeProgram(eff)).toString("hex") })
    } catch (e) {
      const r = e instanceof ForeignRefusal ? e : e instanceof Decline ? new ForeignRefusal("E-NODE", e.message) : undefined
      if (!r) throw e
      result.push({ kind: "refusal", unit, code: r.code, detail: taxonomy.find(t => t.code === r.code)!.detail.replace("{value}", r.value) })
    }
  }
  const entryCall = (x: ts.Expression) => {
    x = new CompilerReader(file).unwrap(x)
    if (!ts.isCallExpression(x)) return
    let name: string
    try { name = new ForeignCompilerReader(file, bindings, declarations, x.pos).name(x.expression) } catch { return }
    if (!entries.has(name)) return
    for (const a of x.arguments) extra(`${name}#${entryIndex++}`, a, a.getStart(file), a.end)
  }
  for (const s of file.statements) {
    if (ts.isExportAssignment(s) && !s.isExportEquals) extra("default", s.expression, s.expression.getStart(file), s.expression.end)
    else if (ts.isExpressionStatement(s)) entryCall(s.expression)
    else if (ts.isFunctionDeclaration(s)) {
      if (s.name?.text === "main" && s.body) {
        for (const st of s.body.statements) {
          if (ts.isExpressionStatement(st)) entryCall(ts.isAwaitExpression(st.expression) ? st.expression.expression : st.expression)
          if (ts.isReturnStatement(st) && st.expression) entryCall(ts.isAwaitExpression(st.expression) ? st.expression.expression : st.expression)
        }
      }
      extra(s.name?.text ?? "default", undefined, s.name?.getStart(file) ?? s.getStart(file), s.end, s.typeParameters?.length ? "E-TYPE-PARAM" : "E-PARAM-SHAPE")
    } else if (ts.isClassDeclaration(s)) {
      const base = s.heritageClauses?.find(h => h.token === ts.SyntaxKind.ExtendsKeyword)?.types[0]?.expression
      let service = false
      if (base) try {
        const reader = new ForeignCompilerReader(file, bindings, declarations, s.end), c = reader.call(base), inner = reader.unwrap(c.expression)
        service = reader.name(ts.isCallExpression(inner) ? inner.expression : c.expression) === "Context.Service"
      } catch { /* A different class is a parameterized unit. */ }
      if (!service) extra(s.name?.text ?? "default", undefined, s.name?.getStart(file) ?? s.getStart(file), s.end, s.typeParameters?.length ? "E-TYPE-PARAM" : "E-PARAM-SHAPE")
    }
  }
  result.sort((a, b) => a.unit.span.start - b.unit.span.start)
  return result
}
