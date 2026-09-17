// read.ts — TypeScript text into an Eff node. The one hand-written path of this package.
//
//   readTypeScript(source)
//     │ parseSync           text → oxc's ESTree                             (oxc-parser)
//     │ programModuleOf     the declarations and the one program a file holds § 2
//     │ exprOf              ESTree → the fragment the Lean printer emits      § 2
//     │ readEff(0, ·)       fragment → Eff: one matcher over the table Lean prints from     § 3
//     │ readModule          the hoisted layers put back at their paths        § 4
//     └ decodeEff           the node checked against the schema             (eff.gen.ts)
//
// Everything else in this package is generated from Lean: the nodes (eff.gen.ts), their
// JSON (json.gen.ts), the operation table (profile.gen.ts), the table of printed clauses
// (templates.gen.ts). This file holds what is logic and not data: what oxc calls things (§ 2),
// the generic reading step over the table, and the leaf and row readers (§ 3).

import { Result } from "effect"
import { parseSync } from "oxc-parser"
import type { ActionTerm, CauseTerm, Eff, ForkOptions, LayerTerm, Lit, Row, ServiceKey, Stmt, Term, Ty } from "./eff.gen.ts"
import { decodeEff } from "./eff.gen.ts"
import { heads, rows, serviceTypeFor, type Entry, type Head } from "./profile.gen.ts"
import { argNamesOf, argSortsOf, programHeads, templates, type ArgPat, type ArgSort, type Depth, type Fam, type StmtTpl, type StmtTpls, type TemplateRow, type Tpl } from "./templates.gen.ts"

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

/** One program file's text into an Eff node, or the refusal that names what was not readable.
 * `table` is the supplied row table (`Api.read (table := …)`): its rows are the external
 * operations, by position; the printed corpus reads under the empty table. */
export const readTypeScript = (source: string, filename = "program.ts", table: ReadonlyArray<Row> = []): Read<Eff> =>
  withTable(table, () => {
    const parsed = parseSync(filename, source, { sourceType: "module", lang: "ts" })
    if (parsed.errors.length > 0) return refuse({ _tag: "parse", messages: parsed.errors.map((e) => e.message) })
    const program = parsed.program as unknown
    if (!isNode(program)) return refuse({ _tag: "program", what: "no program" })
    const module = programModuleOf(program)
    if (failed(module)) return again(module)
    const { declarations, main } = module.success
    return declarations.length === 0 ? Result.map(readProgramExpr(main), decodeEff) : readModule(declarations, main)
  })

/** Fragment seam for the independent oxc normalization and printer-image test entrypoint. */
export const readExpression = (expression: unknown, table: ReadonlyArray<Row> = []): Read<Eff> =>
  withTable(table, () => Result.map(readProgramExpr(expression), decodeEff))

/** The same, before the schema decode: what a declaration block's main expression reads to. */
const readProgramExpr = (expression: unknown): Read<Eff> => {
  if (!isNode(expression)) return refuse({ _tag: "node", type: typeof expression, where: "expression" })
  const fragment = exprOf(expression)
  if (failed(fragment)) return again(fragment)
  return readEff(0, fragment.success)
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

/** The supplied table's rows as entries: the operation of the row at position `i` is
 * `NativeOp.external i` (`Read.lean` `nativeSpell`: an external index is the row's position,
 * never parsed out of an identifier). Bound for the duration of one entry-point call. */
let supplied: ReadonlyArray<Entry> = []
export const withTable = <A>(table: ReadonlyArray<Row>, body: () => A): A => {
  const saved = supplied
  supplied = table.map((row, index): Entry => ({ op: { _tag: "external", index }, row }))
  try {
    return body()
  } finally {
    supplied = saved
  }
}

/** The entry a (spelling, trailing names) pair names: `nativeSpell` of `Read.lean`, the
 * built-in rows first and then the supplied table. */
const spell = (spelling: string, trailing: ReadonlyArray<string>): Entry | undefined => {
  const named = (e: Entry): boolean =>
    e.row.spelling === spelling && e.row.trailing.length === trailing.length &&
    e.row.trailing.every((name, i) => name === trailing[i])
  return rows.find(named) ?? supplied.find(named)
}

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

export type Expr =
  | { readonly _tag: "ident"; readonly name: string }
  | { readonly _tag: "str"; readonly value: string }
  | { readonly _tag: "int"; readonly value: number }
  | { readonly _tag: "bool"; readonly value: boolean }
  | { readonly _tag: "call"; readonly fn: Expr; readonly args: ReadonlyArray<Expr> }
  /** `head<T1, …>` as the callee of a call: lean4-typescript's `Expr.generic`, the type
   * arguments as the spellings the printer writes (`E4-CHECK-CE-013`). */
  | { readonly _tag: "generic"; readonly fn: Expr; readonly typeArgs: ReadonlyArray<string> }
  | { readonly _tag: "method"; readonly base: Expr; readonly name: string; readonly args: ReadonlyArray<Expr> }
  /** `receiver.name` on its own: lean4-typescript's `Expr.member`, which the printer emits only
   * as the callee of a typed method call `receiver.name<T>(args)` (`Print.lean` `printMethod`). */
  | { readonly _tag: "member"; readonly base: Expr; readonly name: string }
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

export type TsStmt =
  /** `const name = yield* value` */
  | { readonly _tag: "constYield"; readonly name: string; readonly value: Expr }
  | { readonly _tag: "ret"; readonly value: Expr }
  | { readonly _tag: "exprStmt"; readonly value: Expr }
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

/** The qualified type names used by native service carriers. */
const qualifiedTypeName = (n: Node): string | undefined => {
  if (n.type === "Identifier" && typeof n.name === "string") return n.name
  if (n.type !== "TSQualifiedName") return undefined
  const left = nodeAt(n, "left")
  const right = nodeAt(n, "right")
  if (!left || right?.type !== "Identifier" || typeof right.name !== "string") return undefined
  const prefix = qualifiedTypeName(left)
  return prefix === undefined ? undefined : `${prefix}.${right.name}`
}

/** A type argument's spelling: the keywords and bare type names the printer writes
 * (`Expr.generic` in `src/Effect4/Codegen/Print.lean`, `Deferred.make<number, number>()`);
 * anything else is outside the printer's image. */
const typeName = (t: Node): string | undefined => {
  switch (t.type) {
    case "TSNumberKeyword": return "number"
    case "TSStringKeyword": return "string"
    case "TSBooleanKeyword": return "boolean"
    case "TSUnknownKeyword": return "unknown"
    case "TSNeverKeyword": return "never"
    case "TSVoidKeyword": return "void"
    case "TSTypeReference": {
      const ref = nodeAt(t, "typeName")
      if (!ref) return undefined
      const name = qualifiedTypeName(ref)
      if (name === undefined) return undefined
      const typeArgs = nodeAt(t, "typeArguments")
      if (!typeArgs) return name
      const rendered: string[] = []
      for (const arg of listAt(typeArgs, "params") ?? []) {
        const text = isNode(arg) ? typeName(arg) : undefined
        if (text === undefined) return undefined
        rendered.push(text)
      }
      return `${name}<${rendered.join(", ")}>`
    }
    default: return undefined
  }
}

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

/** A binder of the printed image, `a0`, `a1`, … (`Var.name`). No head or row spelling begins
 * with `a` (`rowNamesSafe`, Read.lean), so a member chain rooted at a binder is a receiver and
 * never a dotted head. */
const isBinderName = (s: string): boolean => /^a(0|[1-9][0-9]*)$/.test(s)

/** The root identifier of a member chain; `undefined` when the chain bottoms out elsewhere. */
const rootName = (n: Node): string | undefined => {
  if (n.type === "Identifier") return typeof n.name === "string" ? n.name : undefined
  if (n.type === "MemberExpression") {
    const object = nodeAt(n, "object")
    return object ? rootName(unwrap(object)) : undefined
  }
  return undefined
}

/** `receiver.name`: a plain member whose object is a receiver term (a chain rooted at a binder,
 * or an expression that is no identifier chain at all), as opposed to a dotted head such as
 * `Effect.succeed` or `Host.acquire`, which `dotted` reads as one identifier. */
const receiverMember = (n: Node): { readonly object: Node; readonly name: string } | undefined => {
  if (n.type !== "MemberExpression" || n.computed === true || n.optional === true) return undefined
  const object = nodeAt(n, "object")
  const property = nodeAt(n, "property")
  if (!object || !property || property.type !== "Identifier" || typeof property.name !== "string") return undefined
  const inner = unwrap(object)
  const root = rootName(inner)
  if (root !== undefined && !isBinderName(root)) return undefined
  return { object: inner, name: property.name }
}

export const exprOf = (raw: Node): Read<Expr> => {
  const n = unwrap(raw)
  switch (n.type) {
    case "Identifier":
      return typeof n.name === "string" ? ok({ _tag: "ident", name: n.name }) : unsupported(n, "identifier")
    case "MemberExpression": {
      const receiver = receiverMember(n)
      if (receiver) return Result.map(exprOf(receiver.object), (base): Expr => ({ _tag: "member", base, name: receiver.name }))
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
      if (n.optional === true) return unsupported(n, "call")
      const callee = nodeAt(n, "callee")
      if (!callee) return unsupported(n, "callee")
      // The layer printer's only method form is a single `.pipe(Layer.provide...)`.
      if (callee.type === "MemberExpression" && callee.computed !== true && callee.optional !== true) {
        const property = nodeAt(callee, "property")
        const object = nodeAt(callee, "object")
        if (property?.type === "Identifier" && property.name === "pipe" && object) {
          if (n.typeArguments) return unsupported(n, "method typeArguments")
          const base = exprOf(object)
          if (failed(base)) return again(base)
          const args = exprsOf(listAt(n, "arguments") ?? [], "argument")
          if (failed(args)) return again(args)
          return ok({ _tag: "method", base: base.success, name: "pipe", args: args.success })
        }
      }
      // `receiver.spelling(args)` is a method call on a receiver term (`printMethod`); with
      // type arguments the callee is `generic` over a `member`, as the printer spells it.
      const receiver = receiverMember(callee)
      const fn: Read<Expr> = receiver
        ? Result.map(exprOf(receiver.object), (base): Expr => ({ _tag: "member", base, name: receiver.name }))
        : exprOf(callee)
      if (failed(fn)) return again(fn)
      const args = exprsOf(listAt(n, "arguments") ?? [], "argument")
      if (failed(args)) return again(args)
      // `head<T1, …>(args)`: the type arguments become the callee's `generic` spellings.
      const targs = nodeAt(n, "typeArguments")
      if (!targs) {
        return fn.success._tag === "member"
          ? ok({ _tag: "method", base: fn.success.base, name: fn.success.name, args: args.success })
          : ok({ _tag: "call", fn: fn.success, args: args.success })
      }
      const names: string[] = []
      for (const p of listAt(targs, "params") ?? []) {
        const name = isNode(p) ? typeName(p) : undefined
        if (name === undefined) return unsupported(n, "typeArgument")
        names.push(name)
      }
      return ok({ _tag: "call", fn: { _tag: "generic", fn: fn.success, typeArgs: names }, args: args.success })
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

const exprsOf = (items: ReadonlyArray<unknown>, where: string,
  read: (node: Node, index: number) => Read<Expr> = exprOf): Read<ReadonlyArray<Expr>> => {
  const out: Expr[] = []
  for (const [i, item] of items.entries()) {
    if (!isNode(item)) return refuse({ _tag: "node", type: item === null ? "hole" : typeof item, where })
    if (item.type === "SpreadElement") return unsupported(item, where)
    const e = read(item, i)
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
      return Result.map(exprOf(inner), (value): TsStmt => ({ _tag: "exprStmt", value }))
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

/** A file's leading declarations and the one program it ends with. */
interface Module {
  /** The `const L_<path> = <layer>` declarations before the last statement, in file order. */
  readonly declarations: ReadonlyArray<Declaration>
  /** The last statement's expression: the program itself. */
  readonly main: Node
}

interface Declaration {
  readonly name: string
  readonly value: Node
}

/** `const name = value` or `export const name = value`, one declarator, any declared type. */
const constDeclOf = (s: Node): Declaration | undefined => {
  const decl = s.type === "ExportNamedDeclaration" ? nodeAt(s, "declaration") : s
  if (!decl || decl.type !== "VariableDeclaration" || decl.kind !== "const") return undefined
  const decls = listAt(decl, "declarations")
  const d = decls && decls.length === 1 ? decls[0] : undefined
  if (!isNode(d)) return undefined
  const id = nodeAt(d, "id")
  const init = nodeAt(d, "init")
  if (!id || id.type !== "Identifier" || typeof id.name !== "string" || !init) return undefined
  return { name: id.name, value: init }
}

/**
 * What a program file holds: any number of `const name = expression` declarations — the
 * layers `printModule` hoists — and then the program, as a bare expression statement (the
 * generated corpus) or as `export const name = expression` with any declared type (the truth
 * files). Imports are skipped; anything else before the last statement is not one program.
 */
const programModuleOf = (program: Node): Read<Module> => {
  const body = (listAt(program, "body") ?? []).filter((s): s is Node => isNode(s) && s.type !== "ImportDeclaration")
  const last = body[body.length - 1]
  if (last === undefined) return refuse({ _tag: "program", what: "0 statements after imports" })
  const declarations: Declaration[] = []
  for (const s of body.slice(0, -1)) {
    const d = constDeclOf(s)
    if (d === undefined) return refuse({ _tag: "program", what: `${s.type} where a const declaration was expected` })
    declarations.push(d)
  }
  if (last.type === "ExpressionStatement") {
    const e = nodeAt(last, "expression")
    return e ? ok({ declarations, main: e }) : refuse({ _tag: "program", what: "empty expression statement" })
  }
  const main = constDeclOf(last)
  return main ? ok({ declarations, main: main.value }) : refuse({ _tag: "program", what: last.type })
}

/* ============================================================ § 3  the fragment → Eff  (Read.lean, over templates.gen.ts) */

// `readEff(n, x)` reads `x` as a program at environment length `n`. It is Lean's `readT`
// (`src/Effect4/Codegen/Read.lean`): the first row of `templates.gen.ts` whose skeleton matches,
// then a generator, then a row call. There is no reader per head; a printed form is written in
// one place, Lean's `Codegen/Templates.lean`. A bare value (a literal, `undefined`, a binder) or
// an atom application in effect position is refused: the printer never emits one there.
// Binders are depths: the k-th nested lambda binds `a<k>`, and `varRead` recovers a variable by
// comparing names from the newest binder down, never by decoding digits.

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
 * `Effect.forkDetach` decides it for a plain fork, and the scoped forks (`Effect.forkIn`,
 * `Effect.forkScoped`) are daemon forks in rc.112 (`internal/effect.ts:5366` passes `true`
 * to `forkUnsafe`; `:5406` routes `forkScoped` through `forkIn`), as the Lean reader reads
 * them (`src/Effect4/Codegen/Read.lean`, `E4-CHECK-CE-015`).
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

/** The reading of a row: a `perform`, the one invocation form. The row's kind selects the route at the compile. */
const rowAnswer = (e: Entry, request: Term): Eff => ({ _tag: "perform", op: e.op, request })

/** A bare identifier as a value row. */
const readRowValue = (s: string): Read<Eff> => {
  const e = spell(s, [])
  if (!e) return refuse({ _tag: "unknownIdent", name: s })
  return isValueRow(e) ? ok(rowAnswer(e, unit)) : refuse({ _tag: "arity", head: s })
}

/**
 * The saved variable whose two components a tuple-call row receives, when its two
 * arguments are exactly `fst(a)` and `snd(a)` of one identifier `a` (Lean `savedVar?`).
 */
const savedVar = (x: Expr, y: Expr): string | undefined => {
  if (x._tag !== "call" || x.fn._tag !== "ident" || x.fn.name !== "fst" || x.args.length !== 1) return undefined
  if (y._tag !== "call" || y.fn._tag !== "ident" || y.fn.name !== "snd" || y.args.length !== 1) return undefined
  const [v] = x.args
  const [w] = y.args
  if (v?._tag !== "ident" || w?._tag !== "ident" || v.name !== w.name) return undefined
  return v.name
}

/**
 * The request of a tuple-call row from its two arguments: the components of one saved
 * variable read back as that variable, any other two terms as their `pair` application
 * (Lean `readTupleArgs`).
 */
const readTupleArgs = (n: number, x: Expr, y: Expr): Read<Term> => {
  const v = savedVar(x, y)
  if (v !== undefined) return readTerm(n, { _tag: "ident", name: v })
  const a = readTerm(n, x)
  if (failed(a)) return again(a)
  const b = readTerm(n, y)
  if (failed(b)) return again(b)
  return ok({ _tag: "app", atom: "pair", args: [a.success, b.success] })
}

/**
 * A call as a call row; `undefined` when no row of the table has this head and argument
 * shape, so the caller may read an atom application instead. A call row's argument list is
 * the trailing names alone on a `unit` request, and the request followed by the trailing
 * names otherwise; a tuple-call row's is its two request arguments followed by the trailing
 * names. The three readings are tried in that order, and the table lets at most one succeed
 * (Lean `readRowCall`).
 */
const readRowCall = (
  n: number, s: string, typeArgs: ReadonlyArray<string>, args: ReadonlyArray<Expr>,
  view: (e: Entry) => Entry = (e) => e,
): Read<Eff> | undefined => {
  // The call's type arguments must be exactly the ones the row declares: a row that needs
  // them refuses a bare call, and a row that declares none refuses a call that carries any
  // (`E4-CHECK-CE-013`).
  const typed = (e: Entry): boolean =>
    e.row.typeArgs.length === typeArgs.length && e.row.typeArgs.every((a, i) => a === typeArgs[i])
  // `view` is the identity for a call, and the method-argument view of the row for a method
  // call (`methodSignature` of Read.lean): the row identity is the spelled entry either way.
  const find = (names: ReadonlyArray<string>): Entry | undefined => {
    const e = spell(s, names)
    return e === undefined ? undefined : view(e)
  }
  const all = namesOf(args)
  const asTrailing = all ? find(all) : undefined
  if (asTrailing) return asTrailing.row.shape === "call" && unitRequest(asTrailing) && typed(asTrailing) ? ok(rowAnswer(asTrailing, unit)) : refuse({ _tag: "arity", head: s })
  const [request, ...rest] = args
  if (request === undefined) return undefined
  const restNames = namesOf(rest)
  const withRequest = restNames ? find(restNames) : undefined
  if (withRequest) {
    return withRequest.row.shape === "call" && !unitRequest(withRequest) && typed(withRequest)
      ? Result.map(readTerm(n, request), (t) => rowAnswer(withRequest, t))
      : refuse({ _tag: "arity", head: s })
  }
  const [second, ...names] = rest
  if (second === undefined) return undefined
  const tupleNames = namesOf(names)
  const asTuple = tupleNames ? find(tupleNames) : undefined
  if (!asTuple) return undefined
  return asTuple.row.shape === "tupleCall" && typed(asTuple)
    ? Result.map(readTupleArgs(n, request, second), (t) => rowAnswer(asTuple, t))
    : refuse({ _tag: "arity", head: s })
}

/** The ordinary call view of a method row's arguments (`Print.lean` `methodArgsRow`): the
 * request is the second component of the declared `prod` (`never` otherwise) and the shape
 * is `tupleCall` when that component is itself a `prod`, `call` otherwise. */
const methodArgsRow = (e: Entry): Entry => {
  const request: Ty = e.row.request._tag === "prod" ? e.row.request.right : { _tag: "never" }
  return { ...e, row: { ...e.row, request, shape: request._tag === "prod" ? "tupleCall" : "call" } }
}

/**
 * `receiver.spelling(args)` and `receiver.spelling<T>(args)`, the two shapes the printer emits
 * for a `method` row (Lean `readRowMethod`, `addReceiver`): the receiver reads as a term, the
 * arguments by the ordinary call readings under the method view, and the request is
 * `pair(receiver, args)`. A row of any other shape spelled with a receiver is refused.
 */
const readRowMethod = (n: number, receiver: Expr, s: string, typeArgs: ReadonlyArray<string>, args: ReadonlyArray<Expr>): Read<Eff> => {
  const recv = readTerm(n, receiver)
  if (failed(recv)) return again(recv)
  let spelled: Entry | undefined
  const body = readRowCall(n, s, typeArgs, args, (e) => {
    spelled = e
    return methodArgsRow(e)
  })
  if (body === undefined) return refuse({ _tag: "unknownHead", name: s })
  if (failed(body)) return again(body)
  const eff = body.success
  if (spelled === undefined || spelled.row.shape !== "method" || eff._tag !== "perform") {
    return refuse({ _tag: "shape", what: "method row" })
  }
  return ok(rowAnswer(spelled, { _tag: "app", atom: "pair", args: [recv.success, eff.request] }))
}

/** The exact numeric spelling and type argument of Lean's `printKey`. */
const readKey = (x: Expr): Read<ServiceKey> => {
  const bad = () => refuse({ _tag: "shape", what: "service key" })
  if (x._tag !== "call" || x.args.length !== 1 || x.args[0]?._tag !== "str") return bad()
  const fields = /^k(0|[1-9][0-9]*)_(0|[1-9][0-9]*)$/.exec(x.args[0].value)
  if (!fields) return bad()
  const name = Number(fields[1])
  const service = Number(fields[2])
  if (!Number.isSafeInteger(name) || !Number.isSafeInteger(service)) return bad()
  const ty = serviceTypeFor({ name: { value: name }, service: { value: service } })?.rendered
  if (ty === undefined) {
    if (x.fn._tag !== "ident" || x.fn.name !== "Context.Service") return bad()
  } else {
    if (x.fn._tag !== "generic" || x.fn.fn._tag !== "ident" || x.fn.fn.name !== "Context.Service" ||
      x.fn.typeArgs.length !== 1 || x.fn.typeArgs[0] !== ty) return bad()
  }
  return ok({ name: { value: name }, service: { value: service } })
}

const readLiteral = (x: Expr): Read<Lit> => {
  const term = readTerm(0, x)
  if (failed(term)) return again(term)
  return term.success._tag === "lit" ? ok(term.success.value) : refuse({ _tag: "shape", what: "literal" })
}

/* ---------- the one generic step over the table (Lean `readT`, src/Effect4/Codegen/Read.lean) ----------
 *
 * There is no clause per head. `readT(fam, n, x)` takes the rows of `templates.gen.ts` (Lean's
 * `Codegen/Templates.lean`, the table the printer prints from) in order: the first row of the
 * family whose skeleton matches `x`, its arguments read by sort from what the skeleton
 * captured, an argument the row's classifier determines supplied, and the node built from the
 * constructor's field names. A row is accepted only when the printer would choose it for the
 * arguments read, so what is read prints back to the tree read (`Effect.catchIf` with a literal
 * `true` test is refused: the printer writes that program as `Effect.catch`). A transparent
 * row (a bare hole: `withFiber` over its action) hands the same tree to its child's family and
 * matches when that does. A generator is a row, and so is each of its statements (`readStmts`).
 * What no row matches is, for a program, a row call.
 */

type Arg =
  | { readonly _tag: "expr"; readonly e: Expr }
  | { readonly _tag: "exprs"; readonly es: ReadonlyArray<Expr> }
  | { readonly _tag: "str"; readonly s: string }
  | { readonly _tag: "int"; readonly v: number }
  | { readonly _tag: "stmts"; readonly ss: ReadonlyArray<TsStmt> }

type Subst = Map<number, Arg>

const arity = (head: string): Read<never> => refuse({ _tag: "arity", head })
const binder = (expected: string): Read<never> => refuse({ _tag: "binder", expected })
const tableDefect = (): Read<never> => refuse({ _tag: "shape", what: "table" })

const sameParams = (n: number, binders: ReadonlyArray<number>, params: ReadonlyArray<string>): boolean =>
  params.length === binders.length && binders.every((k, j) => params[j] === varName(n + k))

/** Match a tree against a skeleton at depth `n`, collecting the holes (`Template.matchT`). */
const matchT = (n: number, t: Tpl, e: Expr, captured: Subst): boolean => {
  switch (t._tag) {
    case "hole": captured.set(t.i, { _tag: "expr", e }); return true
    case "strHole": if (e._tag !== "str") return false; captured.set(t.i, { _tag: "str", s: e.value }); return true
    case "intHole": if (e._tag !== "int") return false; captured.set(t.i, { _tag: "int", v: e.value }); return true
    case "arrHole": if (e._tag !== "arr") return false; captured.set(t.i, { _tag: "exprs", es: e.items }); return true
    case "binderRef": return e._tag === "ident" && e.name === varName(n + t.k)
    case "ident": return e._tag === "ident" && e.name === t.name
    case "str": return e._tag === "str" && e.value === t.value
    case "int": return e._tag === "int" && e.value === t.value
    case "bool": return e._tag === "bool" && e.value === t.value
    case "call": return e._tag === "call" && matchT(n, t.head, e.fn, captured) && matchTs(n, t.args, e.args, captured)
    case "callSpread":
      if (e._tag !== "call" || !matchT(n, t.head, e.fn, captured)) return false
      captured.set(t.i, { _tag: "exprs", es: e.args })
      return true
    case "arr": return e._tag === "arr" && matchTs(n, t.items, e.items, captured)
    case "object":
      return e._tag === "object" && e.fields.length === t.fields.length &&
        t.fields.every(([key, value], j) => e.fields[j]![0] === key && matchT(n, value, e.fields[j]![1], captured))
    case "arrow": return e._tag === "arrow" && matchT(n, t.body, e.body, captured)
    case "lambda": return e._tag === "lambda" && sameParams(n, t.binders, e.params) && matchT(n, t.body, e.body, captured)
    case "cond":
      return e._tag === "cond" && matchT(n, t.test, e.test, captured) &&
        matchT(n, t.yes, e.thenBranch, captured) && matchT(n, t.no, e.elseBranch, captured)
    case "method":
      return e._tag === "method" && e.name === t.name && matchT(n, t.target, e.base, captured) &&
        matchTs(n, t.args, e.args, captured)
    case "arrowBlock":
      return e._tag === "arrowBlock" && sameParams(n, t.binders, e.params) && matchStmts(n, t.body, e.body, captured)
    case "generator": return e._tag === "generator" && matchStmts(n, t.body, e.body, captured)
  }
}

/** A statement list: one captured list, or its statements in order (`matchStmts`). */
const matchStmts = (n: number, ts: StmtTpls, ss: ReadonlyArray<TsStmt>, captured: Subst): boolean => {
  if (!Array.isArray(ts)) {
    captured.set((ts as { readonly i: number }).i, { _tag: "stmts", ss })
    return true
  }
  const items = ts as ReadonlyArray<StmtTpl>
  return items.length === ss.length && items.every((t, j) => matchStmt(n, t, ss[j]!, captured))
}

const matchTs = (n: number, ts: ReadonlyArray<Tpl>, es: ReadonlyArray<Expr>, captured: Subst): boolean =>
  ts.length === es.length && ts.every((t, j) => matchT(n, t, es[j]!, captured))

/** The statements of the loop image and of a generator. An annotated `let` or `const` never
 * reaches this fragment (§ 2 refuses it), so a skeleton that captures an annotation matches
 * nothing here: the annotated loop prints and is not read, as in Lean (no reader of types). */
const matchStmt = (n: number, t: StmtTpl, s: TsStmt, captured: Subst): boolean => {
  switch (t._tag) {
    case "letInit":
      return t.ann === null && s._tag === "letInit" && s.name === varName(n + t.k) && matchT(n, t.value, s.value, captured)
    case "assign": return s._tag === "assign" && s.name === varName(n + t.k) && matchT(n, t.value, s.value, captured)
    case "ret": return s._tag === "ret" && matchT(n, t.value, s.value, captured)
    case "exprStmt": return s._tag === "exprStmt" && matchT(n, t.value, s.value, captured)
    case "constYield": return s._tag === "constYield" && s.name === varName(n + t.k) && matchT(n, t.value, s.value, captured)
    case "yieldDiscard": return s._tag === "yieldDiscard" && matchT(n, t.value, s.value, captured)
    case "ifElse":
      return s._tag === "ifElse" && matchT(n, t.test, s.condition, captured) &&
        matchStmts(n, t.thenB, s.thenBranch, captured) && matchStmts(n, t.elseB, s.elseBranch, captured)
    case "whileTrue": return s._tag === "whileTrue" && matchStmts(n, t.body, s.body, captured)
    case "breakTo": return s._tag === "breakTo"
  }
}

const sameJson = (a: unknown, b: unknown): boolean => {
  if (a === b) return true
  if (typeof a !== "object" || typeof b !== "object" || a === null || b === null) return false
  if (Array.isArray(a) !== Array.isArray(b)) return false
  const ka = Object.keys(a), kb = Object.keys(b)
  return ka.length === kb.length && ka.every((k) => sameJson((a as Record<string, unknown>)[k], (b as Record<string, unknown>)[k]))
}

/** Whether an argument satisfies a classifier pattern (`ArgPat.holds`). */
const holds = (p: ArgPat, v: unknown): boolean => {
  switch (p._tag) {
    case "term": return sameJson(p.value, v)
    case "bool": case "mode": return v === p.value
    case "decisionBool": return (v as { _tag?: string } | null)?._tag === "bool"
    case "decisionOption": return (v as { _tag?: string } | null)?._tag === "option"
    case "decisionTag": return (v as { _tag?: string } | null)?._tag === "tag"
    case "optTermNone": case "optTyNone": return v === null
    case "optTermSome": case "optTySome": return v !== null && v !== undefined
    case "daemon": return (v as { daemon?: boolean } | null)?.daemon === p.value
  }
}

/** The argument a pattern determines, when it determines one (`ArgPat.supplies`). */
const supplies = (p: ArgPat): { readonly value: unknown } | undefined => {
  switch (p._tag) {
    case "term": case "bool": case "mode": return { value: p.value }
    case "decisionBool": return { value: { _tag: "bool" } }
    case "decisionOption": return { value: { _tag: "option" } }
    case "optTermNone": case "optTyNone": return { value: null }
    default: return undefined
  }
}

const tableRows = templates.rows as ReadonlyArray<TemplateRow>

/** The row the printer chooses for a constructor's arguments (`Row.selects`, first in order). */
const chosenRow = (fam: Fam, ctor: string, args: ReadonlyArray<unknown>): number =>
  tableRows.findIndex((row) => row.fam === fam && row.ctor === ctor &&
    row.fixed.every(([i, p]) => i < args.length && holds(p, args[i])))

const depthAt = (n: number, d: Depth | undefined): number => (d === undefined ? n : d._tag === "rel" ? n + d.k : 0)

/** The daemon flag a row reads a fork's options under: the row's pattern for a plain fork, and
 * `true` otherwise (`forkIn` and `forkScoped` fork a daemon at the pin). */
const rowDaemon = (row: TemplateRow): boolean => {
  for (const [, p] of row.fixed) if (p._tag === "daemon") return p.value
  return true
}

/** A leaf argument from its capture, by sort, at the depth its row gives it (`readLeaf`). */
const readLeaf = (d: number, daemon: boolean, sort: ArgSort, a: Arg): Read<unknown> => {
  if (a._tag === "expr") {
    switch (sort) {
      case "term": case "optTerm": return readTerm(d, a.e)
      case "cause": return readCause(d, a.e)
      case "lit": return readLiteral(a.e)
      case "key": return readKey(a.e)
      case "forkOptions": return readForkOptions(daemon, a.e)
      case "path": {
        const target = a.e._tag === "ident" ? readRefName(a.e.name) : undefined
        return target !== undefined && a.e._tag === "ident" && refName(target) === a.e.name
          ? ok(target) : refuse({ _tag: "shape", what: "layer" })
      }
      default: break
    }
  }
  if (sort === "decision" && a._tag === "str") return ok({ _tag: "tag", tag: a.s })
  if (sort === "nat" && a._tag === "int") return a.v >= 0 ? ok(a.v) : refuse({ _tag: "negative", value: a.v })
  return refuse({ _tag: "shape", what: "argument" })
}

/** The refusal of a tree that no row of its family matches, named by the family (`unread`). */
const unread = (fam: Fam): Read<never> => refuse({ _tag: "shape", what: fam === "layer" || fam === "layers" ? "layer" : "expression" })

const famRank = (fam: Fam): number => (fam === "eff" ? 1 : 0)

const childFam = (sort: ArgSort): Fam | undefined => (sort.startsWith("child:") ? (sort.slice(6) as Fam) : undefined)

const build = (ctor: string, names: ReadonlyArray<string>, args: ReadonlyArray<unknown>): unknown => {
  const node: Record<string, unknown> = { _tag: ctor }
  names.forEach((name, i) => { node[name] = args[i] })
  return node
}

/** A spine of programs or of layers, item by item (`readSpine`). */
const readSpine = (fam: Fam, n: number, xs: ReadonlyArray<Expr>): Read<unknown> => {
  const item: Fam | undefined = fam === "effs" ? "eff" : fam === "layers" ? "layer" : undefined
  if (item === undefined) return tableDefect()
  const out: unknown[] = []
  for (const x of xs) {
    const r = readT(item, n, x) ?? unread(item)
    if (failed(r)) return again(r)
    out.push(r.success)
  }
  return ok(out)
}

/** One argument of a row: supplied by the classifier, a child handed to the recursion, or a leaf. */
const readArg = (n: number, row: TemplateRow, captured: Subst, i: number, sort: ArgSort): Read<unknown> => {
  const pattern = row.fixed.find(([j]) => j === i)?.[1]
  const supplied = pattern === undefined ? undefined : supplies(pattern)
  if (supplied !== undefined) return ok(supplied.value)
  const d = depthAt(n, row.depth[i])
  const a = captured.get(i)
  if (a === undefined) return tableDefect()
  const fam = childFam(sort)
  if (fam !== undefined && a._tag === "expr") return readT(fam, d, a.e) ?? unread(fam)
  if (fam !== undefined && a._tag === "exprs") return readSpine(fam, d, a.es)
  if (fam === "stmts" && a._tag === "stmts") return readStmts(d, a.ss)
  return readLeaf(d, rowDaemon(row), sort, a)
}

/** What is not a skeleton, read as the printer's hand fields print it (`readPerform`): a bare
 * identifier as a value row, a call as a call row, a method call as a method row. A reserved
 * head no row matched is refused by its argument list when it heads a program clause, and by
 * its name otherwise. */
const readPerform = (n: number, x: Expr): Read<Eff> => {
  switch (x._tag) {
    case "ident": {
      if (varRead(n, x.name) !== undefined) return refuse({ _tag: "shape", what: "bare binder" })
      const head = headOf(x.name)
      if (head === "undefined") return refuse({ _tag: "shape", what: "bare value" })
      if (head !== undefined) return refuse({ _tag: "unknownHead", name: x.name })
      return readRowValue(x.name)
    }
    case "int":
      return x.value >= 0 ? refuse({ _tag: "shape", what: "bare value" }) : refuse({ _tag: "negative", value: x.value })
    case "bool":
    case "str":
      return refuse({ _tag: "shape", what: "bare value" })
    case "call": {
      // A call carrying explicit type arguments is a row call and nothing else: no reserved
      // head and no atom application is printed with them, and an empty list is not a
      // spelling the printer emits (`E4-CHECK-CE-013`).
      if (x.fn._tag === "generic") {
        if (x.fn.typeArgs.length === 0) return refuse({ _tag: "shape", what: "expression" })
        if (x.fn.fn._tag === "member") return readRowMethod(n, x.fn.fn.base, x.fn.fn.name, x.fn.typeArgs, x.args)
        if (x.fn.fn._tag !== "ident") return refuse({ _tag: "shape", what: "expression" })
        const s = x.fn.fn.name
        return readRowCall(n, s, x.fn.typeArgs, x.args) ?? refuse({ _tag: "unknownHead", name: s })
      }
      if (x.fn._tag !== "ident") return refuse({ _tag: "shape", what: "expression" })
      const s = x.fn.name
      if (headOf(s) !== undefined) return programHeads.includes(s) ? arity(s) : refuse({ _tag: "unknownHead", name: s })
      return readRowCall(n, s, [], x.args) ?? refuse({ _tag: "unknownHead", name: s })
    }
    case "method":
      return readRowMethod(n, x.base, x.name, [], x.args)
    default:
      return refuse({ _tag: "shape", what: "expression" })
  }
}

/** `undefined` when no row of the family matches. */
const readT = (fam: Fam, n: number, x: Expr): Read<unknown> | undefined => {
  for (let k = 0; k < tableRows.length; k++) {
    const row = tableRows[k]!
    if (row.fam !== fam || row.out._tag !== "tpl") continue // a statement row is read by `readStmts`
    const sorts = argSortsOf(fam, row.ctor)
    const names = argNamesOf(fam, row.ctor)
    if (sorts === undefined || names === undefined) continue
    const t = row.out.tpl
    if (t._tag === "hole") {
      // a transparent row: the same tree at the child's family, or one leaf read of the whole tree
      if (sorts.length !== 1) continue
      const child = childFam(sorts[0]!)
      if (child !== undefined) {
        if (famRank(child) >= famRank(fam)) continue
        const inner = readT(child, depthAt(n, row.depth[0]), x)
        if (inner === undefined) continue
        return failed(inner) ? again(inner) : ok(build(row.ctor, names, [inner.success]))
      }
      const leaf = readLeaf(n, true, sorts[0]!, { _tag: "expr", e: x })
      if (failed(leaf)) continue
      return ok(build(row.ctor, names, [leaf.success]))
    }
    const captured: Subst = new Map()
    if (!matchT(n, t, x, captured)) continue
    return readRow(k, row, n, sorts, names, captured)
  }
  return fam === "eff" ? readPerform(n, x) : undefined
}

/** The arguments of a matched row, the exactness check, and the node (shared by both steps). */
const readRow = (k: number, row: TemplateRow, n: number, sorts: ReadonlyArray<ArgSort>, names: ReadonlyArray<string>, captured: Subst): Read<unknown> => {
  const args: unknown[] = []
  for (let i = 0; i < sorts.length; i++) {
    const a = readArg(n, row, captured, i, sorts[i]!)
    if (failed(a)) return again(a)
    args.push(a.success)
  }
  // exactness: the printer would choose this row for what was read
  if (chosenRow(row.fam, row.ctor, args) !== k) return refuse({ _tag: "shape", what: "not the printed row" })
  return ok(build(row.ctor, names, args))
}

/** The spine of statements: each statement through the first statement row whose skeleton
 * matches it, the rest under the binders that row's skeleton declares (`readStmts`). */
const readStmts = (n: number, stmts: ReadonlyArray<TsStmt>): Read<ReadonlyArray<Stmt>> => {
  const out: Stmt[] = []
  let depth = n
  next: for (const s of stmts) {
    for (let k = 0; k < tableRows.length; k++) {
      const row = tableRows[k]!
      if (row.fam !== "stmt" || row.out._tag !== "stmt") continue
      const sorts = argSortsOf("stmt", row.ctor)
      const names = argNamesOf("stmt", row.ctor)
      if (sorts === undefined || names === undefined) continue
      const captured: Subst = new Map()
      if (!matchStmt(depth, row.out.stmt, s, captured)) continue
      const node = readRow(k, row, depth, sorts, names, captured)
      if (failed(node)) return again(node)
      out.push(node.success as Stmt)
      depth += row.out.declares
      continue next
    }
    return refuse({ _tag: "unsupportedStmt" })
  }
  return ok(out)
}

/** A program from a tree, at environment length `n`. The node is checked against the schema by
 * `decodeEff` at the boundary (§ 0), so the generic build is typed there, once. */
export const readEff = (n: number, x: Expr): Read<Eff> =>
  (readT("eff", n, x) ?? unread("eff")) as Read<Eff>

/** A layer from a tree. A layer is closed: its bodies are read at environment length `0`. */
export const readLayer = (x: Expr): Read<LayerTerm> =>
  (readT("layer", 0, x) ?? unread("layer")) as Read<LayerTerm>



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

/* ============================================================ § 4  the declaration block  (Refs.lean) */

// A layer's identity is its path: the child indices from the root, in the one scheme
// `Node.child` of `src/Effect4/Program/Refs.lean` fixes. `printModule` hoists every
// referenced target into `const L_<path> = …`, so the defining site and every reference
// print as that one identifier; § 3 reads each of them as `LayerTerm.ref <path>`, and this
// section puts the declarations back at their paths (`readModule`, `Eff.restoreAll`), which
// leaves the defining site the layer itself and every later site a reference to it.

/** The declared name of a target: `L_` then its indices joined by `_` (`LayerTerm.refName`). */
const refName = (target: ReadonlyArray<number>): string => `L_${target.join("_")}`

/**
 * The path a declared name carries: `L_` then decimal groups separated by `_`, each group at
 * least one digit (`LayerTerm.readRefName`, read off the bytes there). An empty group —
 * `L_`, `L_1_`, `L_1__0` — is refused here; a group that decodes but does not spell itself
 * back — `L_01` — is refused by the caller's `refName` check, which is where Lean's reader
 * refuses it too.
 */
const readRefName = (s: string): ReadonlyArray<number> | undefined => {
  if (s.length < 3 || s.charCodeAt(0) !== 76 /* L */ || s.charCodeAt(1) !== 95 /* _ */) return undefined
  const groups: number[] = []
  let value = 0
  let seen = false
  for (let i = 2; i < s.length; i++) {
    const b = s.charCodeAt(i)
    if (b === 95) {
      if (!seen) return undefined
      groups.push(value)
      value = 0
      seen = false
    } else if (b >= 48 && b <= 57) {
      value = value * 10 + (b - 48)
      seen = true
    } else return undefined
  }
  if (!seen) return undefined
  groups.push(value)
  return groups
}

/** Program order on paths: a proper prefix is earlier, then the first differing index
 * (`Path.lt`). */
const pathLt = (a: ReadonlyArray<number>, b: ReadonlyArray<number>): boolean => {
  for (let i = 0; i < a.length && i < b.length; i++) {
    if (a[i]! < b[i]!) return true
    if (b[i]! < a[i]!) return false
  }
  return a.length < b.length
}

/** The seven node sorts a path addresses; terms are not nodes (`Node`). */
export type IrNode =
  | { readonly sort: "eff"; readonly eff: Eff }
  | { readonly sort: "stmts"; readonly stmts: ReadonlyArray<Stmt> }
  | { readonly sort: "stmt"; readonly stmt: Stmt }
  | { readonly sort: "action"; readonly action: ActionTerm }
  | { readonly sort: "effs"; readonly effs: ReadonlyArray<Eff> }
  | { readonly sort: "layer"; readonly layer: LayerTerm }
  | { readonly sort: "layers"; readonly layers: ReadonlyArray<LayerTerm> }

const kEff = (eff: Eff): IrNode => ({ sort: "eff", eff })
const kStmts = (stmts: ReadonlyArray<Stmt>): IrNode => ({ sort: "stmts", stmts })
const kStmt = (stmt: Stmt): IrNode => ({ sort: "stmt", stmt })
const kAction = (action: ActionTerm): IrNode => ({ sort: "action", action })
const kEffs = (effs: ReadonlyArray<Eff>): IrNode => ({ sort: "effs", effs })
const kLayer = (layer: LayerTerm): IrNode => ({ sort: "layer", layer })
const kLayers = (layers: ReadonlyArray<LayerTerm>): IrNode => ({ sort: "layers", layers })

/** One child: the node it holds, and the rebuild that puts a replacement of the same sort
 * back in its place (`Node.child` and `Node.setChild` in one entry). */
type Child = readonly [IrNode, (replacement: IrNode) => IrNode | undefined]

const atEff = (v: Eff, back: (v: Eff) => IrNode): Child =>
  [kEff(v), (c) => (c.sort === "eff" ? back(c.eff) : undefined)]
const atStmts = (v: ReadonlyArray<Stmt>, back: (v: ReadonlyArray<Stmt>) => IrNode): Child =>
  [kStmts(v), (c) => (c.sort === "stmts" ? back(c.stmts) : undefined)]
const atStmt = (v: Stmt, back: (v: Stmt) => IrNode): Child =>
  [kStmt(v), (c) => (c.sort === "stmt" ? back(c.stmt) : undefined)]
const atAction = (v: ActionTerm, back: (v: ActionTerm) => IrNode): Child =>
  [kAction(v), (c) => (c.sort === "action" ? back(c.action) : undefined)]
const atEffs = (v: ReadonlyArray<Eff>, back: (v: ReadonlyArray<Eff>) => IrNode): Child =>
  [kEffs(v), (c) => (c.sort === "effs" ? back(c.effs) : undefined)]
const atLayer = (v: LayerTerm, back: (v: LayerTerm) => IrNode): Child =>
  [kLayer(v), (c) => (c.sort === "layer" ? back(c.layer) : undefined)]
const atLayers = (v: ReadonlyArray<LayerTerm>, back: (v: ReadonlyArray<LayerTerm>) => IrNode): Child =>
  [kLayers(v), (c) => (c.sort === "layers" ? back(c.layers) : undefined)]

/**
 * A node's children, in the order the path scheme numbers them — a node's children are these
 * and nothing else (`Node.child`). A spine is a cons cell: its head is child 0 and its tail
 * child 1, so element `i` of the spine at child `c` of `p` is at `p ++ [c] ++ [1]*i ++ [0]`.
 */
export const childrenOf = (n: IrNode): ReadonlyArray<Child> => {
  switch (n.sort) {
    case "eff": {
      const e = n.eff
      switch (e._tag) {
        case "suspend": return [atEff(e.body, (body) => kEff({ ...e, body }))]
        case "bind": return [atEff(e.first, (first) => kEff({ ...e, first })), atEff(e.rest, (rest) => kEff({ ...e, rest }))]
        case "gen": return [atStmts(e.body, (body) => kEff({ ...e, body }))]
        case "catchCause":
        case "catchIf":
          return [atEff(e.body, (body) => kEff({ ...e, body })), atEff(e.handler, (handler) => kEff({ ...e, handler }))]
        case "matchCause":
          return [atEff(e.body, (body) => kEff({ ...e, body })), atEff(e.onValue, (onValue) => kEff({ ...e, onValue })),
            atEff(e.onCause, (onCause) => kEff({ ...e, onCause }))]
        case "onExit":
          return [atEff(e.body, (body) => kEff({ ...e, body })), atEff(e.finalizer, (finalizer) => kEff({ ...e, finalizer }))]
        case "exit": return [atEff(e.body, (body) => kEff({ ...e, body }))]
        case "uninterruptible": return [atEff(e.body, (body) => kEff({ ...e, body }))]
        case "interruptible": return [atEff(e.body, (body) => kEff({ ...e, body }))]
        case "select":
          return [atEff(e.arm0, (arm0) => kEff({ ...e, arm0 })), atEff(e.arm1, (arm1) => kEff({ ...e, arm1 }))]
        case "iterate": return [atEff(e.body, (body) => kEff({ ...e, body }))]
        case "withFiber": return [atAction(e.action, (action) => kEff({ ...e, action }))]
        case "scoped": return [atEff(e.body, (body) => kEff({ ...e, body }))]
        case "acquireRelease":
          return [atEff(e.acquire, (acquire) => kEff({ ...e, acquire })), atEff(e.release, (release) => kEff({ ...e, release }))]
        case "provideLayer":
          return [atLayer(e.layer, (layer) => kEff({ ...e, layer })), atEff(e.body, (body) => kEff({ ...e, body }))]
        case "provideService": return [atEff(e.body, (body) => kEff({ ...e, body }))]
        default: return []
      }
    }
    case "layer": {
      const l = n.layer
      switch (l._tag) {
        case "effect": return [atEff(l.body, (body) => kLayer({ ...l, body }))]
        case "effectDiscard": return [atEff(l.body, (body) => kLayer({ ...l, body }))]
        case "provide":
          return [atLayer(l.self, (self) => kLayer({ ...l, self })), atLayer(l.that, (that) => kLayer({ ...l, that }))]
        case "provideMerge":
          return [atLayer(l.self, (self) => kLayer({ ...l, self })), atLayer(l.that, (that) => kLayer({ ...l, that }))]
        case "merge":
          return [atLayer(l.left, (left) => kLayer({ ...l, left })), atLayer(l.right, (right) => kLayer({ ...l, right }))]
        case "fresh": return [atLayer(l.inner, (inner) => kLayer({ ...l, inner }))]
        case "orDie": return [atLayer(l.inner, (inner) => kLayer({ ...l, inner }))]
        case "mergeAll": return [atLayers(l.layers, (layers) => kLayer({ ...l, layers }))]
        default: return []
      }
    }
    case "stmt": {
      const s = n.stmt
      switch (s._tag) {
        case "bindYield": return [atEff(s.effect, (effect) => kStmt({ ...s, effect }))]
        case "yieldDiscard": return [atEff(s.effect, (effect) => kStmt({ ...s, effect }))]
        case "ifElse":
          return [atStmts(s.thenB, (thenB) => kStmt({ ...s, thenB })), atStmts(s.elseB, (elseB) => kStmt({ ...s, elseB }))]
        case "whileTrue": return [atStmts(s.body, (body) => kStmt({ ...s, body }))]
        default: return []
      }
    }
    case "action": {
      const a = n.action
      switch (a._tag) {
        case "fork": return [atEff(a.program, (program) => kAction({ ...a, program }))]
        case "forkIn": return [atEff(a.program, (program) => kAction({ ...a, program }))]
        case "forkScoped": return [atEff(a.program, (program) => kAction({ ...a, program }))]
        case "raceAll": return [atEffs(a.entrants, (entrants) => kAction({ ...a, entrants }))]
        default: return []
      }
    }
    case "stmts": {
      const [head, ...tail] = n.stmts
      if (head === undefined) return []
      return [atStmt(head, (h) => kStmts([h, ...tail])), atStmts(tail, (t) => kStmts([head, ...t]))]
    }
    case "effs": {
      const [head, ...tail] = n.effs
      if (head === undefined) return []
      return [atEff(head, (h) => kEffs([h, ...tail])), atEffs(tail, (t) => kEffs([head, ...t]))]
    }
    case "layers": {
      const [head, ...tail] = n.layers
      if (head === undefined) return []
      return [atLayer(head, (h) => kLayers([h, ...tail])), atLayers(tail, (t) => kLayers([head, ...t]))]
    }
  }
}

/** The node with the layer at a path replaced; `undefined` when the path names no layer
 * (`Node.replaceLayerAt`). */
const replaceLayerAt = (n: IrNode, path: ReadonlyArray<number>, layer: LayerTerm): IrNode | undefined => {
  const [index, ...rest] = path
  if (index === undefined) return n.sort === "layer" ? kLayer(layer) : undefined
  const child = childrenOf(n)[index]
  if (child === undefined) return undefined
  const replaced = replaceLayerAt(child[0], rest, layer)
  return replaced === undefined ? undefined : child[1](replaced)
}

/** The declarations put back at their paths, ancestors first (ascending program order), so a
 * nested target's site exists when its turn comes (`Eff.restoreAll`). */
export const restoreAll = (main: Eff, decls: ReadonlyArray<readonly [ReadonlyArray<number>, LayerTerm]>): Eff | undefined => {
  const ordered = [...decls].sort(([a], [b]) => (pathLt(a, b) ? -1 : pathLt(b, a) ? 1 : 0))
  let node: IrNode = kEff(main)
  for (const [target, layer] of ordered) {
    const replaced = replaceLayerAt(node, target, layer)
    if (replaced === undefined) return undefined
    node = replaced
  }
  return node.sort === "eff" ? node.eff : undefined
}

/**
 * A declaration block back to the program (`readModule` of `Read.lean`): the last statement
 * is the program, and every `const L_<path>` before it is a layer term put back at the path
 * its name carries. Every occurrence of the identifier — the defining site and each
 * reference — reads as `ref <path>` in § 3, so putting the declaration back at that path
 * leaves the first occurrence (the site at exactly that path, which is what `printModule`
 * hoists) the layer itself and every later occurrence a reference to it. A declaration whose
 * name is no canonical path spelling, or whose path names no layer, is `shape "module"`.
 */
const readModule = (declarations: ReadonlyArray<Declaration>, main: Node): Read<Eff> => {
  const notModule = refuse({ _tag: "shape", what: "module" })
  const program = readProgramExpr(main)
  if (failed(program)) return again(program)
  const decls: Array<readonly [ReadonlyArray<number>, LayerTerm]> = []
  for (const declaration of declarations) {
    const target = readRefName(declaration.name)
    if (target === undefined || refName(target) !== declaration.name) return notModule
    const fragment = exprOf(declaration.value)
    if (failed(fragment)) return again(fragment)
    const layer = readLayer(fragment.success)
    if (failed(layer)) return again(layer)
    decls.push([target, layer.success])
  }
  const whole = restoreAll(program.success, decls)
  return whole === undefined ? notModule : ok(decodeEff(whole))
}
