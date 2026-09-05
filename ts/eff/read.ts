// read.ts — TypeScript text into an Eff node. The one hand-written path of this package.
//
//   readTypeScript(source)
//     │ parseSync           text → oxc's ESTree                             (oxc-parser)
//     │ programExprOf       the one expression a program file holds          § 2
//     │ exprOf              ESTree → the fragment the Lean printer emits      § 2
//     │ readEff(0, ·)       fragment → Eff, src/Effect4/Codegen/Read.lean clause for clause   § 3
//     └ decodeEff           the node checked against the schema             (eff.gen.ts)
//
// Everything else in this package is generated from Lean: the nodes (eff.gen.ts), their
// JSON (json.gen.ts), the operation table (profile.gen.ts). This file holds the two things
// that are logic and not data: what oxc calls things (§ 2), and the reading rules (§ 3).

import { Result } from "effect"
import { parseSync } from "oxc-parser"
import type { ActionTerm, CauseTerm, Eff, ForkOptions, Stmt, Term } from "./eff.gen.ts"
import { decodeEff } from "./eff.gen.ts"
import { heads, rows, type Entry, type Head } from "./profile.gen.ts"

export type { Eff } from "./eff.gen.ts"

/* ============================================================ § 0  the function */

/**
 * Why a reading declined. The first seven are `Effect4.Program.ReadRefusal` verbatim; the
 * last three belong to the layer under it: a tree oxc built that the printer never emits
 * (`node`), a file that is not one program (`program`), text oxc could not parse (`parse`).
 * A refusal is data, never a guess.
 */
export type Refusal =
  | { readonly _tag: "unknownHead"; readonly name: string }
  | { readonly _tag: "unknownIdent"; readonly name: string }
  | { readonly _tag: "arity"; readonly head: string }
  | { readonly _tag: "binder"; readonly expected: string }
  | { readonly _tag: "shape"; readonly what: string }
  | { readonly _tag: "negative"; readonly value: number }
  | { readonly _tag: "unsupportedStmt" }
  | { readonly _tag: "node"; readonly type: string; readonly where: string }
  | { readonly _tag: "program"; readonly what: string }
  | { readonly _tag: "parse"; readonly messages: ReadonlyArray<string> }

export type Read<A> = Result.Result<A, Refusal>

/** One program file's text into an Eff node, or the refusal that names what was not readable. */
export const readTypeScript = (source: string, filename = "program.ts"): Read<Eff> => {
  const parsed = parseSync(filename, source, { sourceType: "module", lang: "ts" })
  if (parsed.errors.length > 0) return refuse({ _tag: "parse", messages: parsed.errors.map((e) => e.message) })
  const program = parsed.program as unknown
  if (!isNode(program)) return refuse({ _tag: "program", what: "no program" })
  const expression = programExprOf(program)
  if (failed(expression)) return again(expression)
  const fragment = exprOf(expression.success)
  if (failed(fragment)) return again(fragment)
  const eff = readEff(0, fragment.success)
  if (failed(eff)) return again(eff)
  // The reader mints nodes by construction; the decode is the receipt that they are the schema's.
  return ok(decodeEff(eff.success))
}

export const showRefusal = (r: Refusal): string => {
  switch (r._tag) {
    case "unknownHead": return `unknownHead ${r.name}`
    case "unknownIdent": return `unknownIdent ${r.name}`
    case "arity": return `arity ${r.head}`
    case "binder": return `binder ${r.expected}`
    case "shape": return `shape ${r.what}`
    case "negative": return `negative ${r.value}`
    case "unsupportedStmt": return "unsupportedStmt"
    case "node": return `node ${r.type} (${r.where})`
    case "program": return `program ${r.what}`
    case "parse": return `parse ${r.messages.join("; ")}`
  }
}

const ok = <A>(value: A): Read<A> => Result.succeed(value)
const refuse = (refusal: Refusal): Result.Result<never, Refusal> => Result.fail(refusal)
const failed = <A>(r: Read<A>): r is Result.Failure<A, Refusal> => Result.isFailure(r)
const again = (f: Result.Failure<unknown, Refusal>): Result.Result<never, Refusal> => Result.fail(f.failure)

/* ============================================================ § 1  the profile */

// profile.gen.ts is generated and checks its own stamp at import. Each entry is already a
// `NativeOp` node and a `Row` node, decoded through the generated schemas; the reader
// derives what it needs from the row (`printRow` in Print.lean: a value row is the bare
// spelling, a call row on a `unit` request prints the trailing names alone).

/** The entry a (spelling, trailing names) pair names: `nativeSpell` of `Read.lean`. */
const spell = (spelling: string, trailing: ReadonlyArray<string>): Entry | undefined =>
  rows.find((e) =>
    e.row.spelling === spelling && e.row.trailing.length === trailing.length &&
    e.row.trailing.every((name, i) => name === trailing[i])
  )

const isValueRow = (e: Entry): boolean => e.row.shape === "value"
const unitRequest = (e: Entry): boolean => e.row.request._tag === "unit"

/* ============================================================ § 2  oxc's tree → the printer's fragment */

// `Expr` and `Stmt` are the formers of lean4-typescript's `TypeScript.Expr` / `TypeScript.Stmt`
// that `src/Effect4/Codegen/Print.lean` uses, nothing more: the printer's image is exactly this
// fragment, so § 3 is a port of `Read.lean` over the same tree and this section is the one
// place that knows what oxc calls things. It admits exactly the shapes the printer emits and
// refuses every other node by its ESTree type name. Two facts of oxc's output are folded
// here: a dotted head such as `Effect.flatMap` arrives as a member chain of identifiers, and
// oxc-parser keeps parentheses as `ParenthesizedExpression` nodes.

type Expr =
  | { readonly _tag: "ident"; readonly name: string }
  | { readonly _tag: "str"; readonly value: string }
  | { readonly _tag: "int"; readonly value: number }
  | { readonly _tag: "bool"; readonly value: boolean }
  | { readonly _tag: "call"; readonly fn: Expr; readonly args: ReadonlyArray<Expr> }
  | { readonly _tag: "object"; readonly fields: ReadonlyArray<readonly [string, Expr]> }
  | { readonly _tag: "arr"; readonly items: ReadonlyArray<Expr> }
  /** `() => body` */
  | { readonly _tag: "arrow"; readonly body: Expr }
  /** `(a, b) => body` */
  | { readonly _tag: "lambda"; readonly params: ReadonlyArray<string>; readonly body: Expr }
  /** `function* () { body }` */
  | { readonly _tag: "generator"; readonly body: ReadonlyArray<TsStmt> }
  | { readonly _tag: "cond"; readonly test: Expr; readonly thenBranch: Expr; readonly elseBranch: Expr }
  /** `(a) => { body }` */
  | { readonly _tag: "arrowBlock"; readonly params: ReadonlyArray<string>; readonly body: ReadonlyArray<TsStmt> }

type TsStmt =
  /** `const name = yield* value` */
  | { readonly _tag: "constYield"; readonly name: string; readonly value: Expr }
  | { readonly _tag: "ret"; readonly value: Expr }
  /** `yield* value` */
  | { readonly _tag: "yieldDiscard"; readonly value: Expr }
  /** `let name = value` */
  | { readonly _tag: "letInit"; readonly name: string; readonly value: Expr }
  /** `name = value` */
  | { readonly _tag: "assign"; readonly name: string; readonly value: Expr }
  /** `while (true) { body }` */
  | { readonly _tag: "whileTrue"; readonly body: ReadonlyArray<TsStmt> }
  | { readonly _tag: "ifElse"; readonly condition: Expr; readonly thenBranch: ReadonlyArray<TsStmt>; readonly elseBranch: ReadonlyArray<TsStmt> }
  | { readonly _tag: "breakTo" }

/** Any node oxc built: a `type` and whatever fields that type carries. */
interface Node {
  readonly type: string
  readonly [key: string]: unknown
}

const isNode = (v: unknown): v is Node =>
  typeof v === "object" && v !== null && typeof (v as { type?: unknown }).type === "string"

const nodeAt = (n: Node, key: string): Node | undefined => {
  const v = n[key]
  return isNode(v) ? v : undefined
}

const listAt = (n: Node, key: string): ReadonlyArray<unknown> | undefined => {
  const v = n[key]
  return Array.isArray(v) ? v : undefined
}

const unsupported = (n: Node, where: string) => refuse({ _tag: "node", type: n.type, where })

const unwrap = (n: Node): Node => {
  if (n.type === "ParenthesizedExpression") {
    const inner = nodeAt(n, "expression")
    if (inner) return unwrap(inner)
  }
  return n
}

/** `A.b.c` as one name, from a chain of non-computed member accesses on identifiers. */
const dotted = (n: Node): string | undefined => {
  if (n.type === "Identifier" && typeof n.name === "string") return n.name
  if (n.type === "MemberExpression" && n.computed === false && n.optional !== true) {
    const object = nodeAt(n, "object")
    const property = nodeAt(n, "property")
    if (!object || !property || property.type !== "Identifier" || typeof property.name !== "string") return undefined
    const head = dotted(unwrap(object))
    return head === undefined ? undefined : `${head}.${property.name}`
  }
  return undefined
}

/** Plain identifier parameters: no annotations, no defaults, no rest. */
const paramNames = (n: Node): ReadonlyArray<string> | undefined => {
  const params = listAt(n, "params")
  if (!params) return undefined
  const names: string[] = []
  for (const p of params) {
    if (!isNode(p) || p.type !== "Identifier" || typeof p.name !== "string" || p.typeAnnotation) return undefined
    names.push(p.name)
  }
  return names
}

const yieldStar = (n: Node): Node | undefined =>
  n.type === "YieldExpression" && n.delegate === true ? nodeAt(n, "argument") : undefined

const exprOf = (raw: Node): Read<Expr> => {
  const n = unwrap(raw)
  switch (n.type) {
    case "Identifier":
      return typeof n.name === "string" ? ok({ _tag: "ident", name: n.name }) : unsupported(n, "identifier")
    case "MemberExpression": {
      const name = dotted(n)
      return name === undefined ? unsupported(n, "member") : ok({ _tag: "ident", name })
    }
    case "Literal": {
      const v = n.value
      if (typeof v === "number") {
        return Number.isInteger(v) && v >= 0
          ? ok({ _tag: "int", value: v })
          : refuse({ _tag: "node", type: `Literal ${String(n.raw)}`, where: "number" })
      }
      if (typeof v === "string") return ok({ _tag: "str", value: v })
      if (typeof v === "boolean") return ok({ _tag: "bool", value: v })
      return unsupported(n, "literal")
    }
    case "CallExpression": {
      if (n.optional === true || n.typeArguments) return unsupported(n, "call")
      const callee = nodeAt(n, "callee")
      if (!callee) return unsupported(n, "callee")
      const fn = exprOf(callee)
      if (failed(fn)) return again(fn)
      const args = exprsOf(listAt(n, "arguments") ?? [], "argument")
      if (failed(args)) return again(args)
      return ok({ _tag: "call", fn: fn.success, args: args.success })
    }
    case "ArrowFunctionExpression": {
      if (n.async === true || n.typeParameters || n.returnType) return unsupported(n, "arrow")
      const params = paramNames(n)
      if (!params) return unsupported(n, "arrow params")
      const body = nodeAt(n, "body")
      if (!body) return unsupported(n, "arrow body")
      if (n.expression === true) {
        const b = exprOf(body)
        if (failed(b)) return again(b)
        return params.length === 0 ? ok({ _tag: "arrow", body: b.success }) : ok({ _tag: "lambda", params, body: b.success })
      }
      if (body.type !== "BlockStatement") return unsupported(body, "arrow block")
      const block = stmtsOf(listAt(body, "body") ?? [])
      if (failed(block)) return again(block)
      return ok({ _tag: "arrowBlock", params, body: block.success })
    }
    case "FunctionExpression": {
      if (n.generator !== true || n.async === true || n.id || n.typeParameters || n.returnType) return unsupported(n, "function")
      const params = paramNames(n)
      if (!params || params.length !== 0) return unsupported(n, "generator params")
      const body = nodeAt(n, "body")
      if (!body || body.type !== "BlockStatement") return unsupported(n, "generator body")
      const block = stmtsOf(listAt(body, "body") ?? [])
      if (failed(block)) return again(block)
      return ok({ _tag: "generator", body: block.success })
    }
    case "ObjectExpression": {
      const fields: Array<readonly [string, Expr]> = []
      for (const p of listAt(n, "properties") ?? []) {
        if (!isNode(p)) return unsupported(n, "property")
        if (p.type !== "Property" || p.kind !== "init" || p.computed === true || p.method === true || p.shorthand === true) {
          return unsupported(p, "property")
        }
        const key = nodeAt(p, "key")
        if (!key || key.type !== "Identifier" || typeof key.name !== "string") return unsupported(key ?? p, "property key")
        const value = nodeAt(p, "value")
        if (!value) return unsupported(p, "property value")
        const v = exprOf(value)
        if (failed(v)) return again(v)
        fields.push([key.name, v.success])
      }
      return ok({ _tag: "object", fields })
    }
    case "ArrayExpression": {
      const items = exprsOf(listAt(n, "elements") ?? [], "array item")
      if (failed(items)) return again(items)
      return ok({ _tag: "arr", items: items.success })
    }
    case "ConditionalExpression": {
      const test = nodeAt(n, "test")
      const consequent = nodeAt(n, "consequent")
      const alternate = nodeAt(n, "alternate")
      if (!test || !consequent || !alternate) return unsupported(n, "conditional")
      const t = exprOf(test)
      if (failed(t)) return again(t)
      const a = exprOf(consequent)
      if (failed(a)) return again(a)
      const b = exprOf(alternate)
      if (failed(b)) return again(b)
      return ok({ _tag: "cond", test: t.success, thenBranch: a.success, elseBranch: b.success })
    }
    default:
      return unsupported(n, "expression")
  }
}

const exprsOf = (items: ReadonlyArray<unknown>, where: string): Read<ReadonlyArray<Expr>> => {
  const out: Expr[] = []
  for (const item of items) {
    if (!isNode(item)) return refuse({ _tag: "node", type: item === null ? "hole" : typeof item, where })
    if (item.type === "SpreadElement") return unsupported(item, where)
    const e = exprOf(item)
    if (failed(e)) return again(e)
    out.push(e.success)
  }
  return ok(out)
}

const stmtOf = (n: Node): Read<TsStmt> => {
  switch (n.type) {
    case "VariableDeclaration": {
      const decls = listAt(n, "declarations")
      const d = decls && decls.length === 1 ? decls[0] : undefined
      if (!isNode(d)) return unsupported(n, "declaration")
      const id = nodeAt(d, "id")
      const init = nodeAt(d, "init")
      if (!id || id.type !== "Identifier" || typeof id.name !== "string" || id.typeAnnotation || !init) return unsupported(n, "declarator")
      if (n.kind === "const") {
        const argument = yieldStar(unwrap(init))
        if (!argument) return unsupported(init, "const without yield*")
        const v = exprOf(argument)
        if (failed(v)) return again(v)
        return ok({ _tag: "constYield", name: id.name, value: v.success })
      }
      if (n.kind === "let") {
        const v = exprOf(init)
        if (failed(v)) return again(v)
        return ok({ _tag: "letInit", name: id.name, value: v.success })
      }
      return unsupported(n, "declaration kind")
    }
    case "ExpressionStatement": {
      const e = nodeAt(n, "expression")
      if (!e) return unsupported(n, "expression statement")
      const inner = unwrap(e)
      const argument = yieldStar(inner)
      if (argument) {
        const v = exprOf(argument)
        if (failed(v)) return again(v)
        return ok({ _tag: "yieldDiscard", value: v.success })
      }
      if (inner.type === "AssignmentExpression" && inner.operator === "=") {
        const left = nodeAt(inner, "left")
        const right = nodeAt(inner, "right")
        if (!left || left.type !== "Identifier" || typeof left.name !== "string" || !right) return unsupported(inner, "assignment")
        const v = exprOf(right)
        if (failed(v)) return again(v)
        return ok({ _tag: "assign", name: left.name, value: v.success })
      }
      return unsupported(inner, "statement expression")
    }
    case "ReturnStatement": {
      const argument = nodeAt(n, "argument")
      if (!argument) return unsupported(n, "bare return")
      const v = exprOf(argument)
      if (failed(v)) return again(v)
      return ok({ _tag: "ret", value: v.success })
    }
    case "WhileStatement": {
      const test = nodeAt(n, "test")
      const body = nodeAt(n, "body")
      if (!test || unwrap(test).type !== "Literal" || unwrap(test).value !== true) return unsupported(test ?? n, "while test")
      if (!body || body.type !== "BlockStatement") return unsupported(body ?? n, "while body")
      const block = stmtsOf(listAt(body, "body") ?? [])
      if (failed(block)) return again(block)
      return ok({ _tag: "whileTrue", body: block.success })
    }
    case "IfStatement": {
      const test = nodeAt(n, "test")
      const consequent = nodeAt(n, "consequent")
      const alternate = nodeAt(n, "alternate")
      if (!test || !consequent || consequent.type !== "BlockStatement") return unsupported(n, "if")
      if (alternate && alternate.type !== "BlockStatement") return unsupported(alternate, "else")
      const t = exprOf(test)
      if (failed(t)) return again(t)
      const a = stmtsOf(listAt(consequent, "body") ?? [])
      if (failed(a)) return again(a)
      const b = alternate ? stmtsOf(listAt(alternate, "body") ?? []) : ok<ReadonlyArray<TsStmt>>([])
      if (failed(b)) return again(b)
      return ok({ _tag: "ifElse", condition: t.success, thenBranch: a.success, elseBranch: b.success })
    }
    case "BreakStatement":
      return n.label ? unsupported(n, "labelled break") : ok({ _tag: "breakTo" })
    default:
      return unsupported(n, "statement")
  }
}

const stmtsOf = (items: ReadonlyArray<unknown>): Read<ReadonlyArray<TsStmt>> => {
  const out: TsStmt[] = []
  for (const item of items) {
    if (!isNode(item)) return refuse({ _tag: "node", type: typeof item, where: "statement" })
    const s = stmtOf(item)
    if (failed(s)) return again(s)
    out.push(s.success)
  }
  return ok(out)
}

/**
 * The one expression a program file holds: a bare expression statement (the generated
 * corpus), or `export const name = expression` with any declared type (the truth files).
 * Imports are skipped; anything else is not one program.
 */
const programExprOf = (program: Node): Read<Node> => {
  const body = (listAt(program, "body") ?? []).filter((s) => isNode(s) && s.type !== "ImportDeclaration")
  if (body.length !== 1 || !isNode(body[0])) return refuse({ _tag: "program", what: `${body.length} statements after imports` })
  const s = body[0]
  if (s.type === "ExpressionStatement") {
    const e = nodeAt(s, "expression")
    return e ? ok(e) : refuse({ _tag: "program", what: "empty expression statement" })
  }
  if (s.type === "ExportNamedDeclaration") {
    const decl = nodeAt(s, "declaration")
    const decls = decl && decl.type === "VariableDeclaration" && decl.kind === "const" ? listAt(decl, "declarations") : undefined
    const d = decls && decls.length === 1 ? decls[0] : undefined
    const init = isNode(d) ? nodeAt(d, "init") : undefined
    return init ? ok(init) : refuse({ _tag: "program", what: "export that is not one const with an initializer" })
  }
  return refuse({ _tag: "program", what: s.type })
}

/* ============================================================ § 3  the fragment → Eff  (Read.lean) */

// `readEff(n, x)` reads `x` as a program at environment length `n`, in the order of the
// printer's table: a bare identifier is a binder, then `Effect.fiberId` or `undefined`, then
// a value row; a call is a reserved head, then a call row, then an atom application; a
// literal is a yielded error. Every reserved head has its own reader in `headReaders`; the
// heads with no reading in that position refuse by name. Binders are depths: the k-th nested
// lambda binds `a<k>`, and `varRead` recovers a variable by comparing names from the newest
// binder down, never by decoding digits.

/** The binder minted for environment position `index`: `a0`, `a1`, … (`Var.name`). */
const varName = (index: number): string => `a${index}`

/** The position `i < n` whose binder is `s`, searched from the newest binder down (`Var.read`). */
const varRead = (n: number, s: string): number | undefined => {
  for (let i = n - 1; i >= 0; i--) if (varName(i) === s) return i
  return undefined
}

const headOf = (s: string): Head | undefined => ((heads as ReadonlyArray<string>).includes(s) ? (s as Head) : undefined)

const unit: Term = { _tag: "lit", value: { _tag: "unit" } }

const readTerm = (n: number, x: Expr): Read<Term> => {
  switch (x._tag) {
    case "ident": {
      const i = varRead(n, x.name)
      if (i !== undefined) return ok({ _tag: "var", index: i })
      return x.name === "undefined" ? ok(unit) : refuse({ _tag: "unknownIdent", name: x.name })
    }
    case "int":
      return x.value >= 0 ? ok({ _tag: "lit", value: { _tag: "nat", value: x.value } }) : refuse({ _tag: "negative", value: x.value })
    case "bool":
      return ok({ _tag: "lit", value: { _tag: "bool", value: x.value } })
    case "str":
      return ok({ _tag: "lit", value: { _tag: "str", value: x.value } })
    case "call": {
      const fn = x.fn
      if (fn._tag !== "ident") return refuse({ _tag: "shape", what: "term" })
      return Result.map(readTerms(n, x.args), (args): Term => ({ _tag: "app", atom: fn.name, args }))
    }
    default:
      return refuse({ _tag: "shape", what: "term" })
  }
}

const readTerms = (n: number, xs: ReadonlyArray<Expr>): Read<ReadonlyArray<Term>> => {
  const out: Term[] = []
  for (const x of xs) {
    const t = readTerm(n, x)
    if (failed(t)) return again(t)
    out.push(t.success)
  }
  return ok(out)
}

const readCause = (n: number, x: Expr): Read<CauseTerm> => {
  if (x._tag !== "call" || x.fn._tag !== "ident") return refuse({ _tag: "shape", what: "cause" })
  const head = headOf(x.fn.name)
  const args = x.args
  if (head === "Cause.fail" && args.length === 1) return Result.map(readTerm(n, args[0]!), (error): CauseTerm => ({ _tag: "fail", error }))
  if (head === "Cause.die" && args.length === 1) return Result.map(readTerm(n, args[0]!), (defect): CauseTerm => ({ _tag: "die", defect }))
  if (head === "Cause.interrupt" && args.length === 0) return ok({ _tag: "interrupt", interruptor: null })
  if (head === "Cause.interrupt" && args.length === 1) {
    return Result.map(readTerm(n, args[0]!), (who): CauseTerm => ({ _tag: "interrupt", interruptor: who }))
  }
  if (head === "Cause.combine" && args.length === 2) {
    const left = readCause(n, args[0]!)
    if (failed(left)) return again(left)
    const right = readCause(n, args[1]!)
    if (failed(right)) return again(right)
    return ok({ _tag: "both", left: left.success, right: right.success })
  }
  return refuse({ _tag: "shape", what: "cause" })
}

/**
 * `{ startImmediately: b, uninterruptible: true | false | "inherit" }` back into fork
 * options. The object carries no `daemon` field: `Effect.forkChild` against
 * `Effect.forkDetach` decides it for a plain fork, and the scoped forks read it as `false`.
 */
const readForkOptions = (daemon: boolean, x: Expr): Read<ForkOptions> => {
  const shape = refuse({ _tag: "shape", what: "forkOptions" })
  if (x._tag !== "object" || x.fields.length !== 2) return shape
  const [[f1, start], [f2, u]] = x.fields as [readonly [string, Expr], readonly [string, Expr]]
  if (f1 !== "startImmediately" || start._tag !== "bool" || f2 !== "uninterruptible") return shape
  if (u._tag === "bool") return ok({ startImmediately: start.value, daemon, maskMode: u.value ? "uninterruptible" : "interruptible" })
  if (u._tag === "str" && u.value === "inherit") return ok({ startImmediately: start.value, daemon, maskMode: "inherit" })
  return shape
}

/**
 * The names an argument list spells, when every argument is a name: an identifier, or a
 * string literal as its quoted rendering. The Lean printer carries the quotes of
 * `Scope.make("parallel")` inside an identifier's name; oxc parses the same bytes as a string
 * literal, so a trailing name is matched by rendered text, exactly as the table spells it.
 */
const namesOf = (args: ReadonlyArray<Expr>): ReadonlyArray<string> | undefined => {
  const names: string[] = []
  for (const a of args) {
    if (a._tag === "ident") names.push(a.name)
    else if (a._tag === "str") names.push(JSON.stringify(a.value))
    else return undefined
  }
  return names
}

/** The reading of a row: a `callback` on an `async` row, a `perform` otherwise. */
const rowAnswer = (e: Entry, request: Term): Eff =>
  e.row.kind === "async" ? { _tag: "callback", register: e.op, request } : { _tag: "perform", op: e.op, request }

/** A bare identifier as a value row. */
const readRowValue = (s: string): Read<Eff> => {
  const e = spell(s, [])
  if (!e) return refuse({ _tag: "unknownIdent", name: s })
  return isValueRow(e) ? ok(rowAnswer(e, unit)) : refuse({ _tag: "arity", head: s })
}

/**
 * A call as a call row; `undefined` when no row of the table has this head and argument
 * shape, so the caller may read an atom application instead. A call row's argument list is
 * the trailing names alone on a `unit` request, and the request followed by the trailing
 * names otherwise; both readings are tried, and the table lets at most one succeed.
 */
const readRowCall = (n: number, s: string, args: ReadonlyArray<Expr>): Read<Eff> | undefined => {
  const all = namesOf(args)
  const asTrailing = all ? spell(s, all) : undefined
  if (asTrailing) return !isValueRow(asTrailing) && unitRequest(asTrailing) ? ok(rowAnswer(asTrailing, unit)) : refuse({ _tag: "arity", head: s })
  const [request, ...rest] = args
  if (request === undefined) return undefined
  const restNames = namesOf(rest)
  const withRequest = restNames ? spell(s, restNames) : undefined
  if (!withRequest) return undefined
  return !isValueRow(withRequest) && !unitRequest(withRequest)
    ? Result.map(readTerm(n, request), (t) => rowAnswer(withRequest, t))
    : refuse({ _tag: "arity", head: s })
}

const readEff = (n: number, x: Expr): Read<Eff> => {
  switch (x._tag) {
    case "ident": {
      const i = varRead(n, x.name)
      if (i !== undefined) return ok({ _tag: "yieldError", error: { _tag: "var", index: i } })
      const head = headOf(x.name)
      if (head === "Effect.fiberId") return ok({ _tag: "withFiber", action: { _tag: "getId" } })
      if (head === "undefined") return ok({ _tag: "yieldError", error: unit })
      if (head !== undefined) return refuse({ _tag: "unknownHead", name: x.name })
      return readRowValue(x.name)
    }
    case "int":
      return x.value >= 0
        ? ok({ _tag: "yieldError", error: { _tag: "lit", value: { _tag: "nat", value: x.value } } })
        : refuse({ _tag: "negative", value: x.value })
    case "bool":
      return ok({ _tag: "yieldError", error: { _tag: "lit", value: { _tag: "bool", value: x.value } } })
    case "str":
      return ok({ _tag: "yieldError", error: { _tag: "lit", value: { _tag: "str", value: x.value } } })
    case "call": {
      if (x.fn._tag !== "ident") return refuse({ _tag: "shape", what: "expression" })
      const s = x.fn.name
      const head = headOf(s)
      if (head !== undefined) return headReaders[head](n, x.args)
      const asRow = readRowCall(n, s, x.args)
      if (asRow !== undefined) return asRow
      return Result.map(readTerms(n, x.args), (args): Eff => ({ _tag: "yieldError", error: { _tag: "app", atom: s, args } }))
    }
    default:
      return refuse({ _tag: "shape", what: "expression" })
  }
}

type HeadReader = (n: number, args: ReadonlyArray<Expr>) => Read<Eff>

const arity = (head: Head): Read<never> => refuse({ _tag: "arity", head })
const binder = (expected: string): Read<never> => refuse({ _tag: "binder", expected })
const notHere = (head: Head): HeadReader => () => refuse({ _tag: "unknownHead", name: head })

/** `head(body)`: one program argument, wrapped by `wrap`. */
const unary = (head: Head, wrap: (body: Eff) => Eff): HeadReader => (n, args) =>
  args.length === 1 ? Result.map(readEff(n, args[0]!), wrap) : arity(head)

/** `head(body, (a<n>) => k)`: a program, then a one-binder continuation at `n + 1`. */
const withContinuation = (head: Head, make: (body: Eff, k: Eff) => Eff): HeadReader => (n, args) => {
  const [body, k] = args
  if (args.length !== 2 || body === undefined || k === undefined || k._tag !== "lambda" || k.params.length !== 1) return arity(head)
  if (k.params[0] !== varName(n)) return binder(varName(n))
  const b = readEff(n, body)
  if (failed(b)) return again(b)
  const r = readEff(n + 1, k.body)
  if (failed(r)) return again(r)
  return ok(make(b.success, r.success))
}

/** `head(term)`: one pure term. */
const term = (head: Head, make: (t: Term) => Eff): HeadReader => (n, args) =>
  args.length === 1 ? Result.map(readTerm(n, args[0]!), make) : arity(head)

/** `head(term, term)`: two pure terms. */
const terms2 = (head: Head, make: (a: Term, b: Term) => Eff): HeadReader => (n, args) => {
  if (args.length !== 2) return arity(head)
  const a = readTerm(n, args[0]!)
  if (failed(a)) return again(a)
  const b = readTerm(n, args[1]!)
  if (failed(b)) return again(b)
  return ok(make(a.success, b.success))
}

const withFiber = (action: ActionTerm): Eff => ({ _tag: "withFiber", action })

/** `head(program, options)`: a fork with its options object; `daemon` is the head's. */
const fork = (head: Head, daemon: boolean, make: (program: Eff, options: ForkOptions) => ActionTerm): HeadReader => (n, args) => {
  if (args.length !== 2) return arity(head)
  const p = readEff(n, args[0]!)
  if (failed(p)) return again(p)
  const o = readForkOptions(daemon, args[1]!)
  if (failed(o)) return again(o)
  return ok(withFiber(make(p.success, o.success)))
}

const readSucceed: HeadReader = term("Effect.succeed", (value) => ({ _tag: "succeed", value }))
const readFail: HeadReader = term("Effect.fail", (error) => ({ _tag: "fail", error }))
const readFailCause: HeadReader = (n, args) =>
  args.length === 1 ? Result.map(readCause(n, args[0]!), (cause): Eff => ({ _tag: "failCause", cause })) : arity("Effect.failCause")
const readSync: HeadReader = (n, args) => {
  const [thunk] = args
  if (args.length !== 1 || thunk === undefined || thunk._tag !== "arrow") return arity("Effect.sync")
  return Result.map(readTerm(n, thunk.body), (t): Eff => ({ _tag: "sync", thunk: t }))
}

/**
 * `Effect.suspend` carries three shapes: `() => t ? a : b` is a value-decided `branch`,
 * `() => body` is `suspend`, and the block `() => { let a<n> = i; return Effect.whileLoop({
 * while, body, step }) }` is `whileLoop` with the cursor at `n` and the body's answer at `n+1`.
 */
const readSuspend: HeadReader = (n, args) => {
  const [arg] = args
  if (args.length !== 1 || arg === undefined) return arity("Effect.suspend")
  if (arg._tag === "arrow") {
    if (arg.body._tag === "cond") {
      const test = readTerm(n, arg.body.test)
      if (failed(test)) return again(test)
      const thenB = readEff(n, arg.body.thenBranch)
      if (failed(thenB)) return again(thenB)
      const elseB = readEff(n, arg.body.elseBranch)
      if (failed(elseB)) return again(elseB)
      return ok({ _tag: "branch", test: test.success, thenB: thenB.success, elseB: elseB.success })
    }
    return Result.map(readEff(n, arg.body), (body): Eff => ({ _tag: "suspend", body }))
  }
  if (arg._tag === "arrowBlock" && arg.params.length === 0 && arg.body.length === 2) {
    const [init, ret] = arg.body as [TsStmt, TsStmt]
    if (init._tag !== "letInit" || ret._tag !== "ret") return arity("Effect.suspend")
    const call = ret.value
    if (call._tag !== "call" || call.fn._tag !== "ident" || call.args.length !== 1) return arity("Effect.suspend")
    const [options] = call.args as [Expr]
    if (options._tag !== "object" || options.fields.length !== 3) return arity("Effect.suspend")
    const [[fw, testArrow], [fb, bodyArrow], [fs, stepBlock]] = options.fields as [readonly [string, Expr], readonly [string, Expr], readonly [string, Expr]]
    if (testArrow._tag !== "arrow" || bodyArrow._tag !== "arrow" || stepBlock._tag !== "arrowBlock") return arity("Effect.suspend")
    if (stepBlock.params.length !== 1 || stepBlock.body.length !== 1) return arity("Effect.suspend")
    const [assign] = stepBlock.body as [TsStmt]
    if (assign._tag !== "assign") return arity("Effect.suspend")
    const named = call.fn.name === "Effect.whileLoop" && fw === "while" && fb === "body" && fs === "step" &&
      init.name === varName(n) && assign.name === varName(n) && stepBlock.params[0] === varName(n + 1)
    if (!named) return refuse({ _tag: "shape", what: "whileLoop" })
    const initial = readTerm(n, init.value)
    if (failed(initial)) return again(initial)
    const test = readTerm(n + 1, testArrow.body)
    if (failed(test)) return again(test)
    const step = readTerm(n + 2, assign.value)
    if (failed(step)) return again(step)
    const body = readEff(n + 1, bodyArrow.body)
    if (failed(body)) return again(body)
    return ok({ _tag: "whileLoop", initial: initial.success, test: test.success, step: step.success, body: body.success })
  }
  return arity("Effect.suspend")
}

const readFlatMap: HeadReader = withContinuation("Effect.flatMap", (first, rest) => ({ _tag: "bind", first, rest }))
const readGen: HeadReader = (n, args) => {
  const [body] = args
  if (args.length !== 1 || body === undefined || body._tag !== "generator") return arity("Effect.gen")
  return Result.map(readStmts(n, body.body), (stmts): Eff => ({ _tag: "gen", body: stmts }))
}
const readCatchCause: HeadReader = withContinuation("Effect.catchCause", (body, handler) => ({ _tag: "catchCause", body, handler }))

/** `Effect.matchCauseEffect(body, { onFailure: (a<n>) => c, onSuccess: (a<n>) => v })`. */
const readMatchCauseEffect: HeadReader = (n, args) => {
  const [body, arms] = args
  if (args.length !== 2 || body === undefined || arms === undefined || arms._tag !== "object" || arms.fields.length !== 2) {
    return arity("Effect.matchCauseEffect")
  }
  const [[ff, onCause], [fs, onValue]] = arms.fields as [readonly [string, Expr], readonly [string, Expr]]
  if (onCause._tag !== "lambda" || onCause.params.length !== 1 || onValue._tag !== "lambda" || onValue.params.length !== 1) {
    return arity("Effect.matchCauseEffect")
  }
  if (ff !== "onFailure" || fs !== "onSuccess" || onCause.params[0] !== varName(n) || onValue.params[0] !== varName(n)) {
    return refuse({ _tag: "shape", what: "matchCause" })
  }
  const b = readEff(n, body)
  if (failed(b)) return again(b)
  const v = readEff(n + 1, onValue.body)
  if (failed(v)) return again(v)
  const c = readEff(n + 1, onCause.body)
  if (failed(c)) return again(c)
  return ok({ _tag: "matchCause", body: b.success, onValue: v.success, onCause: c.success })
}

const readOnExit: HeadReader = withContinuation("Effect.onExit", (body, finalizer) => ({ _tag: "onExit", body, finalizer }))
const readExit: HeadReader = unary("Effect.exit", (body) => ({ _tag: "exit", body }))
const readUninterruptible: HeadReader = unary("Effect.uninterruptible", (body) => ({ _tag: "uninterruptible", body }))
const readInterruptible: HeadReader = unary("Effect.interruptible", (body) => ({ _tag: "interruptible", body }))
const readYieldNowWith: HeadReader = (_n, args) => {
  const [k] = args
  if (args.length !== 1 || k === undefined || k._tag !== "int") return arity("Effect.yieldNowWith")
  return k.value >= 0 ? ok({ _tag: "yieldNow", priority: k.value }) : refuse({ _tag: "negative", value: k.value })
}
const readJoin: HeadReader = term("Fiber.join", (fiber) => ({ _tag: "awaitFiber", fiber, mode: "joinEffect" }))
const readAwait: HeadReader = term("Fiber.await", (fiber) => ({ _tag: "awaitFiber", fiber, mode: "awaitValue" }))
const readForkChild: HeadReader = fork("Effect.forkChild", false, (program, options) => ({ _tag: "fork", program, options }))
const readForkDetach: HeadReader = fork("Effect.forkDetach", true, (program, options) => ({ _tag: "fork", program, options }))
const readForkIn: HeadReader = (n, args) => {
  if (args.length !== 3) return arity("Effect.forkIn")
  const p = readEff(n, args[0]!)
  if (failed(p)) return again(p)
  const s = readTerm(n, args[1]!)
  if (failed(s)) return again(s)
  const o = readForkOptions(false, args[2]!)
  if (failed(o)) return again(o)
  return ok(withFiber({ _tag: "forkIn", program: p.success, options: o.success, scope: s.success }))
}
const readForkScoped: HeadReader = fork("Effect.forkScoped", false, (program, options) => ({ _tag: "forkScoped", program, options }))
const readRunIn: HeadReader = terms2("Fiber.runIn", (target, scope) => withFiber({ _tag: "runIn", target, scope }))
const readInterrupt: HeadReader = term("Fiber.interrupt", (target) => withFiber({ _tag: "interrupt", target }))
const readInterruptAll: HeadReader = term("Fiber.interruptAll", (targets) => withFiber({ _tag: "interruptAll", targets, interruptor: null }))
const readInterruptAllAs: HeadReader = terms2("Fiber.interruptAllAs", (targets, who) => withFiber({ _tag: "interruptAll", targets, interruptor: who }))
const readAwaitAll: HeadReader = term("Fiber.awaitAll", (targets) => withFiber({ _tag: "awaitAll", targets }))
const readRaceAll: HeadReader = (n, args) => {
  const [entrants] = args
  if (args.length !== 1 || entrants === undefined || entrants._tag !== "arr") return arity("Effect.raceAll")
  return Result.map(readEffs(n, entrants.items), (es) => withFiber({ _tag: "raceAll", entrants: es }))
}
const readContext: HeadReader = (_n, args) => (args.length === 0 ? ok(withFiber({ _tag: "getContext" })) : arity("Effect.context"))
const readScopeClose: HeadReader = terms2("Scope.close", (scope, exit) => withFiber({ _tag: "closeScope", scope, exit }))
const readScoped: HeadReader = unary("Effect.scoped", (body) => ({ _tag: "scoped", body }))

/** `Effect.acquireRelease(acquire, (a<n>, a<n+1>) => release)`: the resource and the exit. */
const readAcquireRelease: HeadReader = (n, args) => {
  const [acquire, release] = args
  if (args.length !== 2 || acquire === undefined || release === undefined || release._tag !== "lambda" || release.params.length !== 2) {
    return arity("Effect.acquireRelease")
  }
  if (release.params[0] !== varName(n) || release.params[1] !== varName(n + 1)) return binder(varName(n))
  const a = readEff(n, acquire)
  if (failed(a)) return again(a)
  const r = readEff(n + 2, release.body)
  if (failed(r)) return again(r)
  return ok({ _tag: "acquireRelease", acquire: a.success, release: r.success })
}

/** One reader per reserved head. The keys are the generated `Head` type, so a head added to
 * the profile without a reader here is a compile error. */
const headReaders: Record<Head, HeadReader> = {
  "Effect.succeed": readSucceed,
  "Effect.fail": readFail,
  "Effect.failCause": readFailCause,
  "Effect.sync": readSync,
  "Effect.suspend": readSuspend,
  "Effect.flatMap": readFlatMap,
  "Effect.gen": readGen,
  "Effect.catchCause": readCatchCause,
  "Effect.matchCauseEffect": readMatchCauseEffect,
  "Effect.onExit": readOnExit,
  "Effect.exit": readExit,
  "Effect.uninterruptible": readUninterruptible,
  "Effect.interruptible": readInterruptible,
  "Effect.whileLoop": notHere("Effect.whileLoop"),
  "Effect.yieldNowWith": readYieldNowWith,
  "Fiber.join": readJoin,
  "Fiber.await": readAwait,
  "Effect.forkChild": readForkChild,
  "Effect.forkDetach": readForkDetach,
  "Effect.forkIn": readForkIn,
  "Effect.forkScoped": readForkScoped,
  "Fiber.runIn": readRunIn,
  "Fiber.interrupt": readInterrupt,
  "Fiber.interruptAll": readInterruptAll,
  "Fiber.interruptAllAs": readInterruptAllAs,
  "Fiber.awaitAll": readAwaitAll,
  "Effect.raceAll": readRaceAll,
  "Effect.context": readContext,
  "Effect.fiberId": notHere("Effect.fiberId"),
  "Scope.close": readScopeClose,
  "Effect.scoped": readScoped,
  "Effect.acquireRelease": readAcquireRelease,
  "Cause.fail": notHere("Cause.fail"),
  "Cause.die": notHere("Cause.die"),
  "Cause.interrupt": notHere("Cause.interrupt"),
  "Cause.combine": notHere("Cause.combine"),
  "undefined": notHere("undefined"),
}

/** A generator body, statement by statement, with the binder counts of the printer. */
const readStmts = (n: number, stmts: ReadonlyArray<TsStmt>): Read<ReadonlyArray<Stmt>> => {
  const out: Stmt[] = []
  let depth = n
  for (const s of stmts) {
    switch (s._tag) {
      case "constYield": {
        if (s.name !== varName(depth)) return binder(varName(depth))
        const e = readEff(depth, s.value)
        if (failed(e)) return again(e)
        out.push({ _tag: "bindYield", effect: e.success })
        depth += 1
        break
      }
      case "yieldDiscard": {
        const e = readEff(depth, s.value)
        if (failed(e)) return again(e)
        out.push({ _tag: "yieldDiscard", effect: e.success })
        break
      }
      case "ret": {
        const v = readTerm(depth, s.value)
        if (failed(v)) return again(v)
        out.push({ _tag: "ret", value: v.success })
        break
      }
      case "ifElse": {
        const t = readTerm(depth, s.condition)
        if (failed(t)) return again(t)
        const a = readStmts(depth, s.thenBranch)
        if (failed(a)) return again(a)
        const b = readStmts(depth, s.elseBranch)
        if (failed(b)) return again(b)
        out.push({ _tag: "ifElse", test: t.success, thenB: a.success, elseB: b.success })
        break
      }
      case "whileTrue": {
        const b = readStmts(depth, s.body)
        if (failed(b)) return again(b)
        out.push({ _tag: "whileTrue", body: b.success })
        break
      }
      case "breakTo":
        out.push({ _tag: "breakLoop" })
        break
      default:
        return refuse({ _tag: "unsupportedStmt" })
    }
  }
  return ok(out)
}

/** The race entrants, each at the same environment length. */
const readEffs = (n: number, items: ReadonlyArray<Expr>): Read<ReadonlyArray<Eff>> => {
  const out: Eff[] = []
  for (const x of items) {
    const e = readEff(n, x)
    if (failed(e)) return again(e)
    out.push(e.success)
  }
  return ok(out)
}
