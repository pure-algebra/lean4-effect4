// read.ts — TypeScript text into an Eff node. The one hand-written path of this package.
//
//   readTypeScript(source), readTypeScriptFile(source)
//     │ parseSync           text → oxc's ESTree                             (oxc-parser)
//     │ programModuleOf     the declarations and the one program a file holds § 2
//     │ exprOf              ESTree → the fragment the Lean printer emits      § 2
//     │ readEff(0, ·)       fragment → Eff: one matcher over the table Lean prints from     § 3
//     │ readModule          the hoisted layers put back at their paths        § 4
//     │ readRowServices,    a file's rows' services, exactly; a definition   § 5
//     │   readBlock         block, its headers under the module's classes
//     └ decodeEff           the node checked against the schema             (eff.gen.ts)
//
// Everything else in this package is generated from Lean: the nodes (eff.gen.ts), their
// JSON (json.gen.ts), the operation table (profile.gen.ts), the table of printed clauses
// (templates.gen.ts). This file holds what is logic and not data: what oxc calls things (§ 2),
// the generic reading step over the table, the leaf and row readers (§ 3), and a module's
// declarations (§ 4, § 5).

import { Result } from "effect"
import { parseSync } from "oxc-parser"
import type { ActionTerm, CauseTerm, DefDecl, Eff, ForkOptions, LayerTerm, Lit, NativeOp, ParamDecl, Row, RowArg, ServiceKey, Stmt, Term, Ty } from "./eff.gen.ts"
import { decodeEff } from "./eff.gen.ts"
import { readTypeMetadata } from "./metadata.ts"
import { readTupleIndex } from "./tuple-index.ts"
import { targetType, legacyType, recordKeyForm, quoteType, payloadClass, targetIdentifier, requirementText, nativeScopeKey, keySpelling, keyOfSpelling, rowKeyNames, unionParts, normalize, sameKey, type KeyNames } from "./target-types.ts"
import { heads, rows, serviceTypes, serviceTypeFor, type Entry, type Head } from "./profile.gen.ts"
import { names as nameTables } from "./names.gen.ts"
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
 * operations, by position; the printed corpus reads under the empty table. The file is the
 * declaration block a host wraps (Lean `Api.readModule`): it declares no row's service. */
export const readTypeScript = (source: string, filename = "program.ts", table: ReadonlyArray<Row> = []): Read<Eff> =>
  readSource(source, filename, table, [])

/** A module file's text into an Eff node (Lean `Api.readFile`): its payload classes, then the
 * services of its table's rows, exactly as `rowServiceDecls` prints them (decisions row 378
 * (19)), then the declaration block. */
export const readTypeScriptFile = (source: string, filename = "program.ts", table: ReadonlyArray<Row> = []): Read<Eff> =>
  readSource(source, filename, table, table)

/** A source's text read under its table, its module declaring the services of `rows`. */
const readSource = (source: string, filename: string, table: ReadonlyArray<Row>, rows: ReadonlyArray<Row>): Read<Eff> =>
  withTable(table, () => {
    const parsed = parseSync(filename, source, { sourceType: "module", lang: "ts" })
    if (parsed.errors.length > 0) return refuse({ _tag: "parse", messages: parsed.errors.map((e) => e.message) })
    const program = parsed.program as unknown
    if (!isNode(program)) return refuse({ _tag: "program", what: "no program" })
    const module = programModuleOf(program)
    if (failed(module)) return again(module)
    const { classes, declarations, main } = module.success
    return withClasses(classes, () =>
      declarations.length === 0 && rows.length === 0 ? Result.map(readProgramExpr(main), decodeEff)
        : readModule(declarations, main, rows))
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

/**
 * Where a refusal happened (Lean's `ReadFailure`): the constructor and argument index at each
 * step from the root down to the node that refused, outermost first (a list's items are its
 * `cons` cells: argument 0 the item, 1 the rest); and, when a reserved head matched no row,
 * the steps down the nearest row's skeleton to where the tree parts from it, with what the
 * skeleton has there. It is kept BESIDE the refusal, keyed by the refusal object, so the
 * refusal stays flat and nothing that compares refusals moves.
 */
export interface Location {
  readonly path: ReadonlyArray<readonly [string, number]>
  readonly expected?: { readonly at: ReadonlyArray<string>; readonly what: string } | undefined
}

const locations = new WeakMap<Refusal, { path: Array<readonly [string, number]>; expected?: Location["expected"] }>()

/** Where a refusal this reader returned happened. */
export const locate = (r: Refusal): Location => locations.get(r) ?? { path: [] }

/** The same failure, seen from argument `i` of a `ctor` node above it (`ReadFailure.under`). */
const under = <A>(r: Read<A>, ctor: string, i: number): Read<A> => {
  if (Result.isFailure(r)) {
    const at = locations.get(r.failure) ?? { path: [] }
    at.path.unshift([ctor, i])
    locations.set(r.failure, at)
  }
  return r
}

/** For a person: `bind.1 > succeed.0: unknownIdent a5`, and what was expected where. */
export const showFailure = (r: Refusal): string => {
  const { path, expected } = locate(r)
  const at = path.map(([ctor, i]) => `${ctor}.${i}`).join(" > ")
  const wanted = expected === undefined ? "" : `; expected ${expected.what}${expected.at.length === 0 ? "" : ` at ${expected.at.join(" > ")}`}`
  return `${at === "" ? "" : `${at}: `}${showRefusal(r)}${wanted}`
}

const ok = <A>(value: A): Read<A> => Result.succeed(value)
const refuse = (refusal: Refusal): Result.Result<never, Refusal> => Result.fail(refusal)
const failed = <A>(r: Read<A>): r is Result.Failure<A, Refusal> => Result.isFailure(r)
const again = (f: Result.Failure<unknown, Refusal>): Result.Result<never, Refusal> => Result.fail(f.failure)

/* ============================================================ § 1  the profile */

// profile.gen.ts is generated and checks its own stamp at import. Each entry is already a
// `NativeOp` node and a `Row` node, decoded through the generated schemas; the reader
// derives what it needs from the row (`printRow` in PrintLeaf.lean: a value row is the bare
// spelling, a call row on a `unit` request prints the trailing arguments alone).

/** The supplied table's rows as entries: the operation of the row at position `i` is
 * `NativeOp.external i` (`Read.lean` `nativeSpell`: an external index is the row's position,
 * never parsed out of an identifier). Bound for the duration of one entry-point call. */
let supplied: ReadonlyArray<Entry> = []
let declaredKeyNames: KeyNames = []
export const withTable = <A>(table: ReadonlyArray<Row>, body: () => A): A => {
  const saved = supplied, savedNames = declaredKeyNames
  supplied = table.map((row, index): Entry => ({ op: { _tag: "external", index }, row }))
  declaredKeyNames = rowKeyNames(table)
  try {
    return body()
  } finally {
    supplied = saved
    declaredKeyNames = savedNames
  }
}

/** The payload classes the module declares (decisions row 120, part E2; `Codegen/Classes.lean`
 * `Classes`): each tag with its record fields, `_tag` first. A class construction
 * `new Tag({ … })` reads under them. Bound for the duration of one entry-point call; a bare
 * expression has none. */
type RecordFields = Extract<Ty, { _tag: "record" }>["fields"]
/** The payload classes a type is read under (Lean `Classes.Classes`): each tag with its record
 * fields, `_tag` first. */
type ClassTable = ReadonlyArray<readonly [string, RecordFields]>
let declaredClasses: ClassTable = []
export const withClasses = <A>(classes: ClassTable, body: () => A): A => {
  const saved = declaredClasses
  declaredClasses = classes
  try {
    return body()
  } finally {
    declaredClasses = saved
  }
}

/** Two trailing arguments are one: the same name, or the same string literal. */
export const sameRowArg = (a: RowArg, b: RowArg): boolean =>
  a._tag === "name" ? b._tag === "name" && a.spelling === b.spelling : b._tag === "str" && a.value === b.value

/** The entry a (spelling, trailing arguments) pair names: `nativeSpell` of `Read.lean`, the
 * built-in rows first and then the supplied table. Inside a definition block a name with no
 * trailing arguments spells a body's parameter, then a definition, first (Lean `namedSpell`). */
const spell = (spelling: string, trailing: ReadonlyArray<RowArg>): Entry | undefined => {
  if (trailing.length === 0) {
    const local = named.find((e) => e.row.spelling === spelling)
    if (local !== undefined) return local
  }
  const keyed = (e: Entry): boolean =>
    e.row.spelling === spelling && e.row.trailing.length === trailing.length &&
    e.row.trailing.every((a, i) => sameRowArg(a, trailing[i]!))
  return rows.find(keyed) ?? supplied.find(keyed)
}

const isValueRow = (e: Entry): boolean => e.row.shape === "value"
const unitRequest = (e: Entry): boolean => e.row.request._tag === "unit"

/* ============================================================ § 2  oxc's tree → the printer's fragment */

// `Expr` and `Stmt` retain the structural target forms used by the Lean printer.
// This adapter recognizes syntax; § 3 checks each form against the program printer image.
// Record wrappers retain raw declaration data; the program checker separately decides admission.
// This section is the one place that knows what oxc calls things.
// Two facts of oxc's output are folded
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
  /** `receiver.name`: the target member form, also used by typed method callees. */
  | { readonly _tag: "member"; readonly base: Expr; readonly name: string }
  | { readonly _tag: "index"; readonly base: Expr; readonly key: Expr }
  | { readonly _tag: "new"; readonly callee: Expr; readonly args: ReadonlyArray<Expr> }
  | { readonly _tag: "jsNull" }
  | { readonly _tag: "objectWith"; readonly keys: KeyForm; readonly entries: ReadonlyArray<ObjectEntry> }
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

/** Object key forms remain distinct until the canonical term reader checks them. */
export type KeyForm = "plain" | "quoted" | "computed"
export type ObjectEntry =
  | { readonly _tag: "property"; readonly name: string; readonly value: Expr }
  | { readonly _tag: "spread"; readonly value: Expr }

export type TsStmt =
  /** `const name = yield* value` */
  | { readonly _tag: "constYield"; readonly name: string; readonly value: Expr }
  | { readonly _tag: "ret"; readonly value: Expr }
  | { readonly _tag: "exprStmt"; readonly value: Expr }
  /** `yield* value` */
  | { readonly _tag: "yieldDiscard"; readonly value: Expr }
  /** `let name = value`, or `let name: T = value` with the stated type as the checked type reader
   * read it (`readTypeChecked`): a loop's stated cursor type (the state plan's T5, part B). */
  | { readonly _tag: "letInit"; readonly name: string; readonly value: Expr; readonly type?: Ty }
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

/** The pinned renderer's double-quoted string form. */
const quotedTypeString = (value: string): string =>
  `"${value.replace(/\\/g, "\\\\").replace(/"/g, '\\"').replace(/\n/g, "\\n").replace(/\r/g, "\\r").replace(/\t/g, "\\t")}"`

/** The structural type arguments emitted by the pinned target printer. */
const typeName = (t: Node): string | undefined => {
  switch (t.type) {
    case "TSAnyKeyword": return "any"
    case "TSObjectKeyword": return "object"
    case "TSSymbolKeyword": return "symbol"
    case "TSBigIntKeyword": return "bigint"
    case "TSNumberKeyword": return "number"
    case "TSStringKeyword": return "string"
    case "TSBooleanKeyword": return "boolean"
    case "TSUnknownKeyword": return "unknown"
    case "TSNeverKeyword": return "never"
    case "TSVoidKeyword": return "void"
    case "TSUndefinedKeyword": return "undefined"
    case "TSNullKeyword": return "null"
    case "TSLiteralType": {
      const literal = nodeAt(t, "literal")
      return literal?.type === "Literal" && typeof literal.value === "string"
        ? quotedTypeString(literal.value) : undefined
    }
    case "TSTypeReference": {
      const ref = nodeAt(t, "typeName")
      if (!ref) return undefined
      const name = qualifiedTypeName(ref)
      if (name === undefined) return undefined
      const typeArgs = nodeAt(t, "typeArguments")
      if (!typeArgs) return name
      const rendered = typeNames(listAt(typeArgs, "params"))
      return rendered === undefined ? undefined : `${name}<${rendered.join(", ")}>`
    }
    case "TSUnionType": {
      const members = typeNames(listAt(t, "types"))
      return members === undefined || members.length === 0 ? undefined : members.join(" | ")
    }
    case "TSTupleType": {
      const items = typeNames(listAt(t, "elementTypes"))
      return items === undefined ? undefined : `[${items.join(", ")}]`
    }
    case "TSTypeOperator": {
      const value = nodeAt(t, "typeAnnotation")
      if (t.operator !== "readonly" || value?.type !== "TSTupleType") return undefined
      const tuple = typeName(value)
      return tuple === undefined ? undefined : `readonly ${tuple}`
    }
    case "TSFunctionType": {
      // a method's field in a service's shape: `(a0: T) => Effect.Effect<A, E, never>`
      if (t.typeParameters) return undefined
      const params: string[] = []
      for (const p of listAt(t, "params") ?? []) {
        if (!isNode(p) || p.type !== "Identifier" || typeof p.name !== "string" || p.optional === true) return undefined
        const annotation = nodeAt(p, "typeAnnotation")
        const value = annotation && nodeAt(annotation, "typeAnnotation")
        const rendered = value && typeName(value)
        if (rendered === undefined) return undefined
        params.push(`${p.name}: ${rendered}`)
      }
      const ret = nodeAt(t, "returnType")
      const result = ret && nodeAt(ret, "typeAnnotation")
      const rendered = result && typeName(result)
      return rendered === undefined ? undefined : `(${params.join(", ")}) => ${rendered}`
    }
    case "TSTypeLiteral": {
      const fields: string[] = []
      const members = listAt(t, "members")
      if (members === undefined) return undefined
      for (const field of members) {
        if (!isNode(field) || field.type !== "TSPropertySignature" || field.computed === true) return undefined
        const key = nodeAt(field, "key")
        const name = key?.type === "Identifier" && typeof key.name === "string" ? key.name
          : key?.type === "Literal" && typeof key.value === "string" ? quotedTypeString(key.value) : undefined
        const annotation = nodeAt(field, "typeAnnotation")
        const value = annotation && nodeAt(annotation, "typeAnnotation")
        const rendered = value && typeName(value)
        if (name === undefined || rendered === undefined) return undefined
        fields.push(`${field.readonly === true ? "readonly " : ""}${name}${field.optional === true ? "?" : ""}: ${rendered}`)
      }
      return fields.length === 0 ? "{}" : `{ ${fields.join("; ")} }`
    }
    default: return undefined
  }
}

const typeNames = (nodes: ReadonlyArray<unknown> | undefined): ReadonlyArray<string> | undefined => {
  if (nodes === undefined) return undefined
  const values: string[] = []
  for (const node of nodes) {
    const value = isNode(node) ? typeName(node) : undefined
    if (value === undefined) return undefined
    values.push(value)
  }
  return values
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
      if (n.optional === true) return unsupported(n, "optional access")
      if (n.computed === true) {
        const object = nodeAt(n, "object")
        const property = nodeAt(n, "property")
        if (!object || !property) return unsupported(n, "element access")
        const base = exprOf(object)
        if (failed(base)) return again(base)
        const key = exprOf(property)
        if (failed(key)) return again(key)
        return ok({ _tag: "index", base: base.success, key: key.success })
      }
      const receiver = receiverMember(n)
      if (receiver) return Result.map(exprOf(receiver.object), (base): Expr => ({ _tag: "member", base, name: receiver.name }))
      const name = dotted(n)
      return name === undefined ? unsupported(n, "member") : ok({ _tag: "ident", name })
    }
    case "Literal": {
      const v = n.value
      if (v === null) return ok({ _tag: "jsNull" })
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
    case "NewExpression": {
      const callee = nodeAt(n, "callee")
      if (!callee || n.optional === true) return unsupported(n, "constructor")
      const target = exprOf(callee)
      if (failed(target)) return again(target)
      const args = exprsOf(listAt(n, "arguments") ?? [], "constructor argument")
      if (failed(args)) return again(args)
      const typeArgs = nodeAt(n, "typeArguments")
      if (!typeArgs) return ok({ _tag: "new", callee: target.success, args: args.success })
      const names = typeNames(listAt(typeArgs, "params"))
      return names === undefined ? unsupported(n, "constructor typeArgument")
        : ok({ _tag: "new", callee: { _tag: "generic", fn: target.success, typeArgs: names }, args: args.success })
    }
    case "ObjectExpression": {
      const entries: ObjectEntry[] = []
      let keys: KeyForm | undefined
      let spread = false
      for (const p of listAt(n, "properties") ?? []) {
        if (!isNode(p)) return unsupported(n, "property")
        if (p.type === "SpreadElement") {
          const argument = nodeAt(p, "argument")
          if (!argument) return unsupported(p, "spread value")
          const value = exprOf(argument)
          if (failed(value)) return again(value)
          entries.push({ _tag: "spread", value: value.success })
          spread = true
          continue
        }
        if (p.type !== "Property" || p.kind !== "init" || p.method === true || p.shorthand === true) {
          return unsupported(p, "property")
        }
        const key = nodeAt(p, "key")
        const form: KeyForm | undefined = p.computed === true
          ? key?.type === "Literal" && typeof key.value === "string" ? "computed" : undefined
          : key?.type === "Identifier" ? "plain"
          : key?.type === "Literal" && typeof key.value === "string" ? "quoted" : undefined
        if (form === undefined || (keys !== undefined && keys !== form)) return unsupported(key ?? p, "property key form")
        keys = form
        const name = form === "plain" ? key?.name : key?.value
        if (typeof name !== "string") return unsupported(key ?? p, "property key")
        const value = nodeAt(p, "value")
        if (!value) return unsupported(p, "property value")
        const v = exprOf(value)
        if (failed(v)) return again(v)
        entries.push({ _tag: "property", name, value: v.success })
      }
      if (!spread && (keys === undefined || keys === "plain")) {
        const fields: Array<readonly [string, Expr]> = []
        for (const entry of entries) if (entry._tag === "property") fields.push([entry.name, entry.value])
        return ok({ _tag: "object", fields })
      }
      return ok({ _tag: "objectWith", keys: keys ?? "plain", entries })
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
      if (!id || id.type !== "Identifier" || typeof id.name !== "string" || !init) return unsupported(n, "declarator")
      const annotation = nodeAt(id, "typeAnnotation")
      if (n.kind === "const") {
        // a yielded constant states no type: the printer never writes one there
        if (id.typeAnnotation) return unsupported(n, "declarator")
        const argument = yieldStar(unwrap(init))
        if (!argument) return unsupported(init, "const without yield*")
        const v = exprOf(argument)
        if (failed(v)) return again(v)
        return ok({ _tag: "constYield", name: id.name, value: v.success })
      }
      if (n.kind === "let") {
        const v = exprOf(init)
        if (failed(v)) return again(v)
        if (!id.typeAnnotation) return ok({ _tag: "letInit", name: id.name, value: v.success })
        // A stated type on a `let` is a loop's cursor type (`iterate`'s annotated image). It is
        // read by the checked type reader, and a type with no such reading is refused here,
        // where Lean answers `annotation "local const"`.
        const stated = annotation && nodeAt(annotation, "typeAnnotation")
        const type = stated ? readTypeChecked(stated) : undefined
        return type === undefined ? unsupported(n, "declarator") : ok({ _tag: "letInit", name: id.name, value: v.success, type })
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

/** A file's leading class declarations, its declarations and the one program it ends with. */
interface Module {
  /** The payload classes its leading `export class` declarations declare (decisions row 120). */
  readonly classes: ClassTable
  /** The `const L_<path> = <layer>` declarations before the last statement, in file order. */
  readonly declarations: ReadonlyArray<Declaration>
  /** The last statement's expression: the program itself. */
  readonly main: Node
}

/** A const declaration's oxc node with what the raw reader keeps of it: its name, its value, and
 * whether it is exported and annotated (the rows' services are read exactly, § 5). */
interface Declaration {
  readonly name: string
  readonly value: Node
  readonly exported: boolean
  readonly annotated: boolean
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
  return { name: id.name, value: init, exported: s.type === "ExportNamedDeclaration", annotated: nodeAt(id, "typeAnnotation") !== undefined }
}

/** A type's name from its printed spelling (`Codegen/Classes.lean` `readNamed`, over oxc's nodes),
 * under the module's payload classes: one choice per spelling, `number` as `nat`, `readonly [A, B]`
 * as a product, a union as the right-nested union of its members. A class name reads as the
 * record its declaration declares, and under no class as nothing. `Ref.Ref<A>` reads as `refOf`
 * when `refs` is true (a definition's header, `Signature.typeEnv`; decisions row 378 (8)) and as
 * nothing at an expression's type arguments or a loop's cursor (`refs = false`). */
const readNamedType = (name: string, args: ReadonlyArray<Ty>, classes: ClassTable, refs = false): Ty | undefined => {
  const [a, b] = args
  if (name === "Uint8Array" && args.length === 0) return { _tag: "bytes" }
  if (name === "Option.Option" && args.length === 1) return { _tag: "option", inner: a! }
  if (name === "ReadonlyArray" && args.length === 1) return { _tag: "list", inner: a! }
  if (name === "Result.Result" && args.length === 2) return { _tag: "except", error: b!, value: a! }
  if (name === "Ref.Ref" && args.length === 1 && refs) return { _tag: "refOf", value: a! }
  if (name === "Record" && args.length === 2 && a!._tag === "string") return { _tag: "map", key: a!, value: b! }
  if (name === "Readonly" && args.length === 1 && a!._tag === "map") return a
  const fields = args.length === 0 ? classes.find(([tag]) => tag === name)?.[1] : undefined
  return fields === undefined ? undefined : { _tag: "record", fields }
}
const ofMembers = (members: ReadonlyArray<Ty>): Ty => members.length === 0 ? { _tag: "never" } :
  members.slice(0, -1).reduceRight<Ty>((right, left) => ({ _tag: "union", left, right }), members.at(-1)!)
const readTypeNodes = (nodes: ReadonlyArray<unknown> | undefined, classes: ClassTable, names: KeyNames = [], refs = false): Ty[] | undefined => {
  if (nodes === undefined) return undefined
  const out: Ty[] = []
  for (const node of nodes) {
    const t = isNode(node) ? readTypeNode(node, classes, names, refs) : undefined
    if (t === undefined) return undefined
    out.push(t)
  }
  return out
}
const readFieldNodes = (members: ReadonlyArray<unknown> | undefined, classes: ClassTable, names: KeyNames = [], refs = false): Array<readonly [string, readonly [boolean, Ty]]> | undefined => {
  if (members === undefined) return undefined
  const out: Array<readonly [string, readonly [boolean, Ty]]> = []
  for (const field of members) {
    if (!isNode(field) || field.type !== "TSPropertySignature" || field.computed === true || field.readonly !== true) return undefined
    const key = nodeAt(field, "key")
    const name = key?.type === "Identifier" && typeof key.name === "string" ? key.name
      : key?.type === "Literal" && typeof key.value === "string" ? key.value : undefined
    const annotation = nodeAt(field, "typeAnnotation")
    const value = annotation && nodeAt(annotation, "typeAnnotation")
    const t = value && readTypeNode(value, classes, names, refs)
    if (name === undefined || t === undefined) return undefined
    out.push([name, [field.optional === true, t]])
  }
  return out
}
const readTypeNode = (t: Node, classes: ClassTable, names: KeyNames = [], refs = false): Ty | undefined => {
  switch (t.type) {
    case "TSNumberKeyword": return { _tag: "nat" }
    case "TSStringKeyword": return { _tag: "string" }
    case "TSBooleanKeyword": return { _tag: "bool" }
    case "TSVoidKeyword": return { _tag: "unit" }
    // `never` reads as the empty type (`readNamed`, the state plan's T5, part B): the error
    // column of `Deferred.make<A, never>()` is spelled so. `unknown` has no reading.
    case "TSNeverKeyword": return { _tag: "never" }
    case "TSNullKeyword": return { _tag: "null" }
    case "TSUndefinedKeyword": return { _tag: "undefined" }
    case "TSLiteralType": {
      const literal = nodeAt(t, "literal")
      return literal?.type === "Literal" && typeof literal.value === "string" ? { _tag: "lit", value: literal.value } : undefined
    }
    case "TSTypeReference": {
      const ref = nodeAt(t, "typeName")
      const name = ref && qualifiedTypeName(ref)
      const typeArgs = nodeAt(t, "typeArguments")
      const params = typeArgs ? listAt(typeArgs, "params") : []
      // `Context.Context<R>`: the context of its row, read by the requirement reader (Lean
      // `readTy`'s first arm, decisions row 349)
      if (name === "Context.Context") {
        const row = params !== undefined && params.length === 1 && isNode(params[0]) ? typeName(params[0]) : undefined
        const keys = row === undefined ? undefined : readKeysText(row, names)
        return keys === undefined ? undefined : { _tag: "contextOf", keys }
      }
      const args = readTypeNodes(params, classes, names, refs)
      return name === undefined || args === undefined ? undefined : readNamedType(name, args, classes, refs)
    }
    case "TSTypeOperator": {
      const value = nodeAt(t, "typeAnnotation")
      if (t.operator !== "readonly" || value?.type !== "TSTupleType") return undefined
      const items = readTypeNodes(listAt(value, "elementTypes"), classes, names, refs)
      if (items === undefined) return undefined
      return items.length === 2 ? { _tag: "prod", left: items[0]!, right: items[1]! } : { _tag: "tuple", items }
    }
    case "TSUnionType": {
      const members = readTypeNodes(listAt(t, "types"), classes, names, refs)
      return members === undefined ? undefined : ofMembers(members)
    }
    case "TSTypeLiteral": {
      const fields = readFieldNodes(listAt(t, "members"), classes, names, refs)
      return fields === undefined ? undefined : { _tag: "record", fields }
    }
    default: return undefined
  }
}

/**
 * The checked type reader (Lean `Classes.readTyChecked`, `Codegen/Classes.lean`) under the
 * module's payload classes and key names: a program type from its printed spelling, kept only when
 * the type printer prints that type as the spelling read (`targetType`, the twin of `Types.ofTy`).
 * What it accepts is exact. It does not make the printer injective: `number` reads as `nat`, so a
 * type at `int` does not read back, and a handle's name (`Deferred.Deferred<A, E>`, or
 * `Ref.Ref<A>` when `refs` is false) and `unknown` read as nothing, as does a class's name under
 * no class (Lean `Classes.ReadableTy` names what is outside). The expression reader reads its
 * types under no class and `refs = false`, and a definition's header under the module's classes,
 * key names and `refs = true` (decisions row 378 (8)).
 */
const readTypeChecked = (t: Node, classes: ClassTable = [], names: KeyNames = [], refs = false): Ty | undefined => {
  const ty = readTypeNode(t, classes, names, refs)
  return ty !== undefined && targetType(ty, legacyType, names) === typeName(t) ? ty : undefined
}

/**
 * The checked type reader on a type's text: exactly one type, parsed by oxc as the right side
 * of a type alias. The readers of this package read an operation's type arguments through this
 * one function: this file from the spellings its fragment holds (`installTypeArgs`), and the
 * compiler-backed foreign recognizer from the source text (`ingest/ck.ts`). The ESTree foreign
 * recognizer hands its fragment to this file's reader. So the three read a type alike.
 */
export const readTypeText = (text: string): Ty | undefined => {
  const parsed = parseSync("type.ts", `type T = ${text}`, { sourceType: "module", lang: "ts" })
  if (parsed.errors.length > 0) return undefined
  const program = parsed.program as unknown
  const body = isNode(program) ? listAt(program, "body") : undefined
  const alias = body !== undefined && body.length === 1 && isNode(body[0]) ? body[0] : undefined
  const annotation = alias !== undefined && alias.type === "TSTypeAliasDeclaration" && !alias.typeParameters
    ? nodeAt(alias, "typeAnnotation") : undefined
  return annotation === undefined ? undefined : readTypeChecked(annotation)
}

/** The class's type argument as `Codegen/Classes.lean` `classDecl` prints it: the fields after
 * `_tag`, in order, `readonly`, each type as the type projection spells it. */
const classTypeText = (rest: RecordFields): string | undefined => {
  const fields: string[] = []
  for (const [name, [optional, type]] of rest) {
    const target = targetType(type, legacyType)
    if (target === undefined) return undefined
    fields.push(`readonly ${targetIdentifier(name) ? name : quoteType(name)}${optional ? "?" : ""}: ${target}`)
  }
  return fields.length === 0 ? "{}" : `{ ${fields.join("; ")} }`
}

/**
 * `export class Tag extends Data.TaggedError("Tag")<{ readonly f: T; … }> {}` (decisions row 120,
 * part E2): the tag and the record fields, `_tag` first (`Codegen/Classes.lean` `readClassDecl`).
 * Accepted only when the declaration is exactly what the printer prints of what it reads to.
 * `undefined` when the statement is no class declaration.
 */
const classDeclOf = (s: Node): Read<readonly [string, RecordFields]> | undefined => {
  const decl = s.type === "ExportNamedDeclaration" ? nodeAt(s, "declaration") : undefined
  if (decl?.type !== "ClassDeclaration") return undefined
  const malformed = refuse({ _tag: "shape", what: "class" })
  const id = nodeAt(decl, "id")
  const superClass = nodeAt(decl, "superClass")
  const typeArgs = nodeAt(decl, "superTypeArguments")
  const body = nodeAt(decl, "body")
  if (id?.type !== "Identifier" || typeof id.name !== "string" || superClass?.type !== "CallExpression" ||
      typeArgs === undefined || (listAt(body ?? decl, "body") ?? [undefined]).length !== 0 ||
      (listAt(decl, "implements") ?? []).length !== 0 || (listAt(decl, "decorators") ?? []).length !== 0 ||
      decl.typeParameters || decl.abstract === true || decl.declare === true) return malformed
  const callee = nodeAt(superClass, "callee")
  const args = listAt(superClass, "arguments") ?? []
  const tagArg = args[0]
  const params = listAt(typeArgs, "params") ?? []
  const literal = params[0]
  if (!callee || dotted(callee) !== "Data.TaggedError" || args.length !== 1 || !isNode(tagArg) ||
      tagArg.type !== "Literal" || tagArg.value !== id.name || params.length !== 1 || !isNode(literal) ||
      literal.type !== "TSTypeLiteral") return malformed
  const rest = readFieldNodes(listAt(literal, "members"), [])
  if (rest === undefined || classTypeText(rest) !== typeName(literal)) return malformed
  return ok([id.name, [["_tag", [false, { _tag: "lit", value: id.name }]], ...rest]])
}

/**
 * What a program file holds: its payload class declarations first (decisions row 120), then any
 * number of `const name = expression` declarations — the layers `printModule` hoists — and then
 * the program, as a bare expression statement (the generated corpus) or as
 * `export const name = expression` with any declared type (the truth files). Imports are
 * skipped; anything else before the last statement is not one program.
 */
const programModuleOf = (program: Node): Read<Module> => {
  const body = (listAt(program, "body") ?? []).filter((s): s is Node => isNode(s) && s.type !== "ImportDeclaration")
  const last = body[body.length - 1]
  if (last === undefined) return refuse({ _tag: "program", what: "0 statements after imports" })
  const classes: Array<readonly [string, RecordFields]> = []
  const declarations: Declaration[] = []
  for (const s of body.slice(0, -1)) {
    const c = classDeclOf(s)
    if (c !== undefined) {
      if (declarations.length > 0) return refuse({ _tag: "program", what: "a class declaration after a const declaration" })
      if (failed(c)) return again(c)
      classes.push(c.success)
      continue
    }
    const d = constDeclOf(s)
    if (d === undefined) return refuse({ _tag: "program", what: `${s.type} where a const declaration was expected` })
    declarations.push(d)
  }
  if (last.type === "ExpressionStatement") {
    const e = nodeAt(last, "expression")
    return e ? ok({ classes, declarations, main: e }) : refuse({ _tag: "program", what: "empty expression statement" })
  }
  const main = constDeclOf(last)
  return main ? ok({ classes, declarations, main: main.value }) : refuse({ _tag: "program", what: last.type })
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

/** `Classes.classTag?`: the class a record construction prints as, when its declared fields are a
 * payload class (`payloadClass`), `_tag` is its first field, its first name and its first value
 * (the tag's literal), no later name repeats `_tag`, and every other name has its value. */
const sameTy = (a: Ty, b: Ty): boolean => JSON.stringify(a) === JSON.stringify(b)
export const classTag = (fields: RecordFields, names: ReadonlyArray<string>, values: ReadonlyArray<Term>): string | undefined => {
  const tag = payloadClass(fields)
  if (tag === undefined) return undefined
  const head = fields[0]
  const first = values[0]
  return head !== undefined && head[0] === "_tag" && head[1][0] === false && sameTy(head[1][1], { _tag: "lit", value: tag }) &&
    names[0] === "_tag" && first !== undefined && first._tag === "lit" && first.value._tag === "str" &&
    first.value.value === tag && !names.slice(1).includes("_tag") && names.length === values.length ? tag : undefined
}

/** The object of a construction or a record literal: its names and values in written order,
 * and its key form; undefined for a spread or another expression. */
const objectEntries = (object: Expr): { names: string[]; values: Expr[]; form: KeyForm } | undefined => {
  const entries: ReadonlyArray<ObjectEntry> | undefined = object._tag === "objectWith" ? object.entries :
    object._tag === "object" ? object.fields.map(([name, value]) => ({ _tag: "property", name, value })) : undefined
  if (entries === undefined) return undefined
  const names: string[] = [], values: Expr[] = []
  for (const entry of entries) {
    if (entry._tag !== "property") return undefined
    names.push(entry.name); values.push(entry.value)
  }
  return { names, values, form: object._tag === "objectWith" ? object.keys : "plain" }
}

/** `new Tag({ f: v, … })`, a payload class construction (`Codegen/Classes.lean` `readClass`): the
 * record term whose fields the module's classes declare for `Tag`, `_tag` restored first, accepted
 * only when the printer prints that term as this construction. */
const readClassTerm = (n: number, x: Expr): Read<Term> | undefined => {
  if (x._tag !== "new" || x.callee._tag !== "ident" || x.args.length !== 1) return undefined
  const object = objectEntries(x.args[0]!)
  if (object === undefined || object.form !== recordKeyForm(object.names)) return undefined
  const tag = x.callee.name
  const fields = declaredClasses.find(([name]) => name === tag)?.[1]
  if (fields === undefined) return refuse({ _tag: "unknownIdent", name: tag })
  const read = readTerms(n, object.values)
  if (failed(read)) return again(read)
  const names = ["_tag", ...object.names]
  const values: ReadonlyArray<Term> = [{ _tag: "lit", value: { _tag: "str", value: tag } }, ...read.success]
  if (classTag(fields, names, values) !== tag) return refuse({ _tag: "shape", what: "class" })
  return ok({ _tag: "record", fields, presentNames: names, values })
}

/** Canonical records and field operations; undefined means this is another term form. */
const readRecordTerm = (n: number, x: Expr): Read<Term> | undefined => {
  const malformed = (what: string) => refuse({ _tag: "shape", what: `record ${what}` })
  if (x._tag !== "call") return undefined
  const fn = x.fn
  if (fn._tag === "generic" && fn.fn._tag === "ident" && ["recordValue", "recordRaw"].includes(fn.fn.name)) {
    const raw = fn.fn.name === "recordRaw"
    if (fn.typeArgs.length !== 1 || x.args.length !== (raw ? 3 : 2)) return malformed("arity")
    const declared = readTypeMetadata(x.args[0]!)
    if (declared?._tag !== "record") return malformed("type metadata")
    const expected = targetType(declared, legacyType)
    let names: string[], values: ReadonlyArray<Expr>
    if (raw) {
      const supplied = x.args[1]!, children = x.args[2]!
      if (fn.typeArgs[0] !== "unknown" || supplied._tag !== "arr" || children._tag !== "arr") return malformed("raw frame")
      names = []
      for (const name of supplied.items) {
        if (name._tag !== "str") return malformed("supplied name")
        names.push(name.value)
      }
      values = children.items
      if (names.length === values.length && expected !== undefined) return malformed("unnecessary raw frame")
    } else {
      const object = x.args[1]!
      // Source text erases the distinction between plain object and objectWith/plain.
      const entries: ReadonlyArray<ObjectEntry> | undefined = object._tag === "objectWith" ? object.entries :
        object._tag === "object" ? object.fields.map(([name, value]) => ({ _tag: "property", name, value })) : undefined
      const form = object._tag === "objectWith" ? object.keys : "plain"
      if (entries === undefined || entries.some(entry => entry._tag !== "property")) return malformed("object entries")
      names = []; const children: Expr[] = []
      for (const entry of entries) {
        if (entry._tag !== "property") return malformed("spread in construction")
        names.push(entry.name); children.push(entry.value)
      }
      values = children
      if (form !== recordKeyForm(names) || expected === undefined || fn.typeArgs[0] !== expected) return malformed("annotation or key form")
    }
    const read = readTerms(n, values)
    if (failed(read)) return again(read)
    // the printer prints a construction in the class form as `new Tag({ … })` (decisions row 120)
    if (classTag(declared.fields, names, read.success) !== undefined) return malformed("in class form")
    return ok({ _tag: "record", fields: declared.fields, presentNames: names, values: read.success })
  }
  const update = fn._tag === "call" && fn.fn._tag === "call" ? fn.fn : undefined
  if (update?.fn._tag === "generic" && update.fn.fn._tag === "ident" && update.fn.fn.name === "recordSet") {
    if (fn._tag !== "call" || x.args.length !== 1 || fn.args.length !== 1 || update.args.length !== 1 ||
        update.fn.typeArgs.length !== 1 || update.args[0]?._tag !== "str" ||
        update.fn.typeArgs[0] !== quoteType(update.args[0].value)) return malformed("update key or arity")
    const name = update.args[0].value
    const target = readTerm(n, fn.args[0]!)
    if (failed(target)) return again(target)
    return Result.map(readTerm(n, x.args[0]!), (value): Term => ({ _tag: "recordSet", target: target.success, name, value }))
  }
  if (fn._tag !== "call" || fn.fn._tag !== "generic" || fn.fn.fn._tag !== "ident") return undefined
  const head = fn.fn.fn.name
  if (head !== "recordRequired" && head !== "recordOptional") return undefined
  if (fn.fn.typeArgs.length !== 1 || x.args.length !== 1 || fn.args.length !== 1 ||
      fn.args[0]?._tag !== "str" || fn.fn.typeArgs[0] !== quoteType(fn.args[0].value)) return malformed("field key or arity")
  const name = fn.args[0].value
  return Result.map(readTerm(n, x.args[0]!), (target): Term => ({ _tag: "field", mode: head === "recordRequired" ? "required" : "optional", target, name }))
}

/** Exact string index markers; the host representation refuses unsafe numeric indices. */
const readTupleTerm = (n: number, x: Expr): Read<Term> | undefined => {
  if (x._tag !== "call" || x.fn._tag !== "call" || x.fn.fn._tag !== "generic" ||
      x.fn.fn.fn._tag !== "ident" || x.fn.fn.fn.name !== "tupleAt") return undefined
  const marker = x.fn
  const malformed = (what: string) => refuse({ _tag: "shape", what: `tuple ${what}` })
  if (marker.fn._tag !== "generic" || marker.fn.typeArgs.length !== 1 || marker.args.length !== 1 ||
      x.args.length !== 1 || marker.args[0]?._tag !== "str" ||
      marker.fn.typeArgs[0] !== quoteType(marker.args[0].value)) return malformed("index marker or arity")
  const index = readTupleIndex(marker.args[0].value)
  if (index === undefined) return malformed("index outside canonical safe-natural profile")
  return Result.map(readTerm(n, x.args[0]!), (target): Term => ({ _tag: "tupleAt", target, index }))
}

/** A list fold, `fold(list, init, (aN, aM) => body)` (`Codegen/ListFold.lean`, decisions row
 * 228): the two parameters are the binders of levels `n` and `n + 1`, and the body is read two
 * levels up. A call of `fold` on any other argument list is no fold. It falls through to the
 * atom application, whose arguments are terms, and a function is no term. */
const readFoldTerm = (n: number, x: Expr): Read<Term> | undefined => {
  if (x._tag !== "call" || x.fn._tag !== "ident" || x.fn.name !== "fold" || x.args.length !== 3) return undefined
  const step = x.args[2]!
  if (step._tag !== "lambda" || !sameParams(n, [0, 1], step.params)) return undefined
  const list = readTerm(n, x.args[0]!)
  if (failed(list)) return again(list)
  const init = readTerm(n, x.args[1]!)
  if (failed(init)) return again(init)
  return Result.map(readTerm(n + 2, step.body), (body): Term => ({ _tag: "fold", accTy: null, list: list.success, init: init.success, body }))
}

export const readTerm = (n: number, x: Expr): Read<Term> => {
  const construction = readClassTerm(n, x)
  if (construction !== undefined) return construction
  const tuple = readTupleTerm(n, x)
  if (tuple !== undefined) return tuple
  const record = readRecordTerm(n, x)
  if (record !== undefined) return record
  const fold = readFoldTerm(n, x)
  if (fold !== undefined) return fold
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
      // A fold's stated accumulator type is printed and not read yet: the checked type reader
      // (`readTypeChecked`) does not serve this place (Lean's
      // `ReadRefusal.annotation "fold accumulator"`, `Codegen/Read.lean`).
      if (fn._tag === "generic" && fn.fn._tag === "ident" && fn.fn.name === "fold")
        return refuse({ _tag: "shape", what: "fold accumulator annotation" })
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

/** The trailing argument an argument reads as, if it reads as one: an identifier as a name, a
 * string literal as itself (Lean `rowArgs?`, one argument). */
export const rowArgOf = (a: Expr): RowArg | undefined =>
  a._tag === "ident" ? { _tag: "name", spelling: a.name } : a._tag === "str" ? { _tag: "str", value: a.value } : undefined

/** The trailing arguments an argument list reads as, when every argument reads as one
 * (Lean `rowArgs?`): `Scope.make("parallel")`'s literal is the row's string-literal argument. */
const argsOf = (args: ReadonlyArray<Expr>): ReadonlyArray<RowArg> | undefined => {
  const out: RowArg[] = []
  for (const a of args) {
    const r = rowArgOf(a)
    if (r === undefined) return undefined
    out.push(r)
  }
  return out
}

/** The reading of a row: a `perform`, the one invocation form, with the operation the row spells,
 * its face (a term row's term is the unit literal there); `readPerform` installs the function it
 * read. The row's kind selects the route at the compile. */
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
 * the trailing arguments alone on a `unit` request, and the request followed by the trailing
 * arguments otherwise; a tuple-call row's is its two request arguments followed by the trailing
 * arguments. The three readings are tried in that order, and the table lets at most one succeed
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
  const find = (names: ReadonlyArray<RowArg>): Entry | undefined => {
    const e = spell(s, names)
    return e === undefined ? undefined : view(e)
  }
  const all = argsOf(args)
  const asTrailing = all ? find(all) : undefined
  if (asTrailing) return asTrailing.row.shape === "call" && unitRequest(asTrailing) && typed(asTrailing) ? ok(rowAnswer(asTrailing, unit)) : refuse({ _tag: "arity", head: s })
  const [request, ...rest] = args
  if (request === undefined) return undefined
  const restNames = argsOf(rest)
  const withRequest = restNames ? find(restNames) : undefined
  if (withRequest) {
    return withRequest.row.shape === "call" && !unitRequest(withRequest) && typed(withRequest)
      ? Result.map(readTerm(n, request), (t) => rowAnswer(withRequest, t))
      : refuse({ _tag: "arity", head: s })
  }
  const [second, ...names] = rest
  if (second === undefined) return undefined
  const tupleNames = argsOf(names)
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

/** Only the exact printed key is admitted (Lean `readKey`): its spelling under the signature's
 * key names (`keySpelling`), its type argument and its carrier must agree, and the distinguished
 * scope is represented only by `Scope.Scope`. */
const readKey = (x: Expr): Read<ServiceKey> => {
  const bad = () => refuse({ _tag: "shape", what: "service key" })
  const scopeKey = serviceTypes.reserved.find(entry => entry.rendered === "Scope.Scope")?.key
  if (x._tag === "ident" && x.name === "Scope.Scope") return scopeKey ? ok(scopeKey) : bad()
  if (x._tag !== "call" || x.args.length !== 1 || x.args[0]?._tag !== "str") return bad()
  const text = x.args[0].value
  const key = keyOfSpelling(declaredKeyNames, text)
  if (!key) return bad()
  if (scopeKey !== undefined && sameKey(key, scopeKey)) return bad()
  const ty = serviceTypeFor(key)?.rendered
  const identity = quoteType(keySpelling(declaredKeyNames, key))
  if (ty === undefined) {
    if (x.fn._tag !== "ident" || x.fn.name !== "Context.Service") return bad()
  } else {
    if (x.fn._tag !== "generic" || x.fn.fn._tag !== "ident" || x.fn.fn.name !== "Context.Service" ||
      x.fn.typeArgs.length !== 2 || x.fn.typeArgs[0] !== identity ||
      x.fn.typeArgs[1] !== ty) return bad()
  }
  return ok(key)
}

/** The key order of `ServiceKey.Lt` (`src/Effect4/Machine/Key.lean`): by name, then by service. */
const keyBefore = (a: ServiceKey, b: ServiceKey): boolean =>
  a.name.value < b.name.value || (a.name.value === b.name.value && a.service.value < b.service.value)

/** The string a quoted type literal spells (`quoteType`'s inverse). */
const unquoteType = (quoted: string): string | undefined => {
  if (quoted.length < 2 || !quoted.startsWith('"') || !quoted.endsWith('"')) return undefined
  let out = ""
  for (let i = 1; i < quoted.length - 1; i++) {
    const c = quoted[i]!
    if (c === '"' || c === "\n" || c === "\r" || c === "\t") return undefined
    if (c !== "\\") { out += c; continue }
    const next = quoted[++i]
    if (next === "\\" || next === '"') out += next
    else if (next === "n") out += "\n"
    else if (next === "r") out += "\r"
    else if (next === "t") out += "\t"
    else return undefined
  }
  return out
}

/** A requirement row from its printed type argument (Lean `readKeys`): `never`, one key identifier,
 * or their union, each key read by its spelling under the module's key names (`keyOfSpelling`).
 * The canonical row of the keys read is kept only when it prints back as the text read, so what
 * the reader accepts is exact. */
const readKeys = (text: string, names: KeyNames = declaredKeyNames): Read<ReadonlyArray<ServiceKey>> => {
  const bad = () => refuse({ _tag: "shape", what: "requirement row" })
  const keys: Array<ServiceKey> = []
  for (const member of text === "never" ? [] : unionParts(text)) {
    if (member === "Scope.Scope") {
      if (nativeScopeKey === undefined) return bad()
      keys.push(nativeScopeKey)
      continue
    }
    const spelling = unquoteType(member)
    const key = spelling === undefined ? undefined : keyOfSpelling(names, spelling)
    if (key === undefined) return bad()
    keys.push(key)
  }
  const row = keys.slice().sort((a, b) => (keyBefore(a, b) ? -1 : keyBefore(b, a) ? 1 : 0))
    .filter((k, i, all) => i === 0 || keyBefore(all[i - 1]!, k))
  return requirementText(row, names) === text ? ok(row) : bad()
}

/** A context reader's type argument as a row, for the foreign recognizers: the printer's own
 * reader (`readKeys`), so only a printed row is admitted. */
export const readKeysText = (text: string, names: KeyNames = declaredKeyNames): ReadonlyArray<ServiceKey> | undefined => {
  const r = readKeys(text, names)
  return Result.isSuccess(r) ? r.success : undefined
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
 * The row call of `perform` is a row too, the last of the program rows (`readPerform`).
 */

type Arg =
  | { readonly _tag: "expr"; readonly e: Expr }
  | { readonly _tag: "exprs"; readonly es: ReadonlyArray<Expr> }
  | { readonly _tag: "str"; readonly s: string }
  | { readonly _tag: "int"; readonly v: number }
  | { readonly _tag: "stmts"; readonly ss: ReadonlyArray<TsStmt> }
  /** A stated type, as the checked type reader read it (Lean `Arg.type`). */
  | { readonly _tag: "type"; readonly ty: Ty }
  /** A head's type argument, as the expression reader spelled it (Lean `Arg.type` at a generic). */
  | { readonly _tag: "typeName"; readonly name: string }

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
    case "generic":
      if (e._tag !== "generic" || e.typeArgs.length !== 1 || !matchT(n, t.head, e.fn, captured)) return false
      captured.set(t.i, { _tag: "typeName", name: e.typeArgs[0]! })
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

/** The statements of the loop image and of a generator. An annotated `const` never reaches this
 * fragment (§ 2 refuses it). A `let` reaches it with or without a stated type: a skeleton with no
 * annotation matches a `let` that states none, and a skeleton with an annotation hole captures
 * the stated type, which the checked type reader has read (Lean `Template.matchStmt`,
 * `readLeaf` at a loop's cursor type; the state plan's T5, part B). */
const matchStmt = (n: number, t: StmtTpl, s: TsStmt, captured: Subst): boolean => {
  switch (t._tag) {
    case "letInit": {
      if (s._tag !== "letInit" || s.name !== varName(n + t.k)) return false
      if (t.ann === null ? s.type !== undefined : s.type === undefined) return false
      if (t.ann !== null && s.type !== undefined) captured.set(t.ann, { _tag: "type", ty: s.type })
      return matchT(n, t.value, s.value, captured)
    }
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

/* Where a tree parts from a skeleton (Lean `Template.explainT`): for a refusal's message only.
 * `matchT` is the definition of matching; this walks the same cases and names the first
 * difference: the steps down the skeleton, and what the skeleton has there. */

type Difference = { readonly at: ReadonlyArray<string>; readonly what: string } | undefined

const binderNames = (n: number, bs: ReadonlyArray<number>): string => bs.map((k) => varName(n + k)).join(", ")

const describe = (n: number, t: Tpl): string => {
  switch (t._tag) {
    case "hole": return "an expression"
    case "strHole": return "a string literal"
    case "intHole": return "an integer literal"
    case "arrHole": case "arr": return "an array"
    case "binderRef": return varName(n + t.k)
    case "ident": return t.name
    case "str": return `the string ${t.value}`
    case "int": case "bool": return String(t.value)
    case "call": case "callSpread": return "a call"
    case "generic": return "a head with a type argument"
    case "object": return "an object"
    case "arrow": return "a function of no parameter"
    case "lambda": return `a function of ${binderNames(n, t.binders)}`
    case "cond": return "a conditional"
    case "method": return `a call of .${t.name}`
    case "arrowBlock": return `a block function of (${binderNames(n, t.binders)})`
    case "generator": return "a generator function"
  }
}

const describeStmt = (n: number, t: StmtTpl): string => {
  switch (t._tag) {
    case "letInit": return `let ${varName(n + t.k)}`
    case "assign": return `an assignment to ${varName(n + t.k)}`
    case "ret": return "a return"
    case "exprStmt": return "an expression statement"
    case "constYield": return `const ${varName(n + t.k)} = yield*`
    case "yieldDiscard": return "yield*"
    case "ifElse": return "if/else"
    case "whileTrue": return "while (true)"
    case "breakTo": return "break"
  }
}

const below = (step: string, d: Difference): Difference => (d === undefined ? undefined : { at: [step, ...d.at], what: d.what })
const here = (what: string): Difference => ({ at: [], what })

const explainT = (n: number, t: Tpl, e: Expr): Difference => {
  switch (t._tag) {
    case "hole": return undefined
    case "strHole": return e._tag === "str" ? undefined : here(describe(n, t))
    case "intHole": return e._tag === "int" ? undefined : here(describe(n, t))
    case "arrHole": return e._tag === "arr" ? undefined : here(describe(n, t))
    case "binderRef": return e._tag === "ident" && e.name === varName(n + t.k) ? undefined : here(varName(n + t.k))
    case "ident": return e._tag === "ident" && e.name === t.name ? undefined : here(t.name)
    case "str": return e._tag === "str" && e.value === t.value ? undefined : here(describe(n, t))
    case "int": return e._tag === "int" && e.value === t.value ? undefined : here(String(t.value))
    case "bool": return e._tag === "bool" && e.value === t.value ? undefined : here(String(t.value))
    case "call":
      if (e._tag !== "call") return here(describe(n, t))
      return below("head", explainT(n, t.head, e.fn)) ?? explainTs(n, t.args, e.args)
    case "callSpread": return e._tag === "call" ? below("head", explainT(n, t.head, e.fn)) : here(describe(n, t))
    case "generic": return e._tag === "generic" ? below("head", explainT(n, t.head, e.fn)) : here(describe(n, t))
    case "arr": return e._tag === "arr" ? explainTs(n, t.items, e.items) : here(describe(n, t))
    case "object": {
      if (e._tag !== "object") return here(describe(n, t))
      for (let j = 0; j < t.fields.length; j++) {
        const [key, value] = t.fields[j]!
        const field = e.fields[j]
        if (field === undefined || field[0] !== key) return here(`the field ${key}`)
        const d = below(`field ${key}`, explainT(n, value, field[1]))
        if (d !== undefined) return d
      }
      return e.fields.length > t.fields.length ? here("no further field") : undefined
    }
    case "arrow": return e._tag === "arrow" ? below("body", explainT(n, t.body, e.body)) : here(describe(n, t))
    case "lambda":
      if (e._tag !== "lambda") return here(describe(n, t))
      return sameParams(n, t.binders, e.params) ? below("body", explainT(n, t.body, e.body)) : { at: ["parameters"], what: binderNames(n, t.binders) }
    case "cond":
      if (e._tag !== "cond") return here(describe(n, t))
      return below("test", explainT(n, t.test, e.test)) ?? below("then", explainT(n, t.yes, e.thenBranch)) ?? below("else", explainT(n, t.no, e.elseBranch))
    case "method":
      if (e._tag !== "method" || e.name !== t.name) return here(describe(n, t))
      return below("receiver", explainT(n, t.target, e.base)) ?? explainTs(n, t.args, e.args)
    case "arrowBlock":
      if (e._tag !== "arrowBlock") return here(describe(n, t))
      return sameParams(n, t.binders, e.params) ? explainStmts(n, t.body, e.body) : { at: ["parameters"], what: binderNames(n, t.binders) }
    case "generator": return e._tag === "generator" ? explainStmts(n, t.body, e.body) : here(describe(n, t))
  }
}

const explainTs = (n: number, ts: ReadonlyArray<Tpl>, es: ReadonlyArray<Expr>): Difference => {
  for (let j = 0; j < ts.length; j++) {
    if (es[j] === undefined) return here(`an argument ${j}`)
    const d = below(`argument ${j}`, explainT(n, ts[j]!, es[j]!))
    if (d !== undefined) return d
  }
  return es.length > ts.length ? here(`${ts.length} arguments`) : undefined
}

const explainStmt = (n: number, t: StmtTpl, s: TsStmt): Difference => {
  switch (t._tag) {
    case "letInit":
      if (s._tag !== "letInit" || s.name !== varName(n + t.k)) return here(describeStmt(n, t))
      return below("value", explainT(n, t.value, s.value))
        ?? (t.ann === null ? (s.type === undefined ? undefined : here("no annotation")) : (s.type === undefined ? here("an annotation") : undefined))
    case "assign": return s._tag === "assign" && s.name === varName(n + t.k) ? below("value", explainT(n, t.value, s.value)) : here(describeStmt(n, t))
    case "ret": return s._tag === "ret" ? below("value", explainT(n, t.value, s.value)) : here(describeStmt(n, t))
    case "exprStmt": return s._tag === "exprStmt" ? below("value", explainT(n, t.value, s.value)) : here(describeStmt(n, t))
    case "constYield": return s._tag === "constYield" && s.name === varName(n + t.k) ? below("value", explainT(n, t.value, s.value)) : here(describeStmt(n, t))
    case "yieldDiscard": return s._tag === "yieldDiscard" ? below("value", explainT(n, t.value, s.value)) : here(describeStmt(n, t))
    case "ifElse":
      if (s._tag !== "ifElse") return here(describeStmt(n, t))
      return below("test", explainT(n, t.test, s.condition)) ?? below("then", explainStmts(n, t.thenB, s.thenBranch)) ?? below("else", explainStmts(n, t.elseB, s.elseBranch))
    case "whileTrue": return s._tag === "whileTrue" ? below("body", explainStmts(n, t.body, s.body)) : here(describeStmt(n, t))
    case "breakTo": return s._tag === "breakTo" ? undefined : here(describeStmt(n, t))
  }
}

const explainStmts = (n: number, ts: StmtTpls, ss: ReadonlyArray<TsStmt>): Difference => {
  if (!Array.isArray(ts)) return undefined
  const items = ts as ReadonlyArray<StmtTpl>
  for (let j = 0; j < items.length; j++) {
    if (ss[j] === undefined) return here(describeStmt(n, items[j]!))
    const d = below(`statement ${j}`, explainStmt(n, items[j]!, ss[j]!))
    if (d !== undefined) return d
  }
  return ss.length > items.length ? here(`${items.length} statements`) : undefined
}

/** Where `x` parts from the nearest row: the first row with `x`'s head (`nearestRow`). */
const nearestRow = (n: number, x: Expr): Difference => {
  const head = x._tag === "ident" ? x.name : x._tag === "call" && x.fn._tag === "ident" ? x.fn.name
    : x._tag === "call" && x.fn._tag === "generic" && x.fn.fn._tag === "ident" ? x.fn.fn.name : undefined
  if (head === undefined) return undefined
  for (const row of tableRows) {
    if (row.out._tag !== "tpl") continue
    const t = row.out.tpl
    const rowHead = t._tag === "ident" ? t.name : (t._tag === "call" || t._tag === "callSpread") && t.head._tag === "ident" ? t.head.name
      : t._tag === "call" && t.head._tag === "generic" && t.head.head._tag === "ident" ? t.head.head.name : undefined
    if (rowHead !== head) continue
    const d = explainT(n, t, x)
    if (d !== undefined) return d
  }
  return undefined
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
    case "decisionRecordTag": return (v as { _tag?: string } | null)?._tag === "recordTag"
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
      case "decision": return a.e._tag === "str" ? ok({ _tag: "recordTag", tag: a.e.value }) : refuse({ _tag: "shape", what: "record tag" })
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
  // a loop's stated cursor type: the checked type reader read it where the statement was read
  if (sort === "optTy" && a._tag === "type") return ok(a.ty)
  if (sort === "keys" && a._tag === "typeName") return readKeys(a.name)
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
    // item j of a list is `cons.1` j times, then `cons.0`
    let r: Read<unknown> = under(readT(item, n, x) ?? unread(item), "cons", 0)
    for (let j = 0; j < out.length; j++) r = under(r, "cons", 1)
    if (failed(r)) return again(r)
    out.push(r.success)
  }
  return ok(out)
}

/** One argument of a row: supplied by the classifier, a child handed to the recursion, or a leaf. */
const readArg = (n: number, row: TemplateRow, captured: Subst, i: number, sort: ArgSort): Read<unknown> =>
  under(readArgHere(n, row, captured, i, sort), row.ctor, i)

const readArgHere = (n: number, row: TemplateRow, captured: Subst, i: number, sort: ArgSort): Read<unknown> => {
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

/**
 * The operation with its binder term replaced (Lean `NativeOp.withTerm`, the native signature's
 * `withTerm`); `undefined` for an operation that carries none. The eight read-modify-write rows
 * carry a binder term. The switch lists every constructor, so an appended one is a type error
 * here until it is classified.
 */
const withTerm = (op: NativeOp, f: Term): NativeOp | undefined => {
  switch (op._tag) {
    case "refUpdateWith":
    case "refGetAndUpdateWith":
    case "refUpdateAndGetWith":
    case "refUpdateSomeWith":
    case "refGetAndUpdateSomeWith":
    case "refUpdateSomeAndGetWith":
    case "refModifyWith":
    case "refModifySomeWith":
      return { _tag: op._tag, f }
    case "refMake":
    case "refGet":
    case "refSet":
    case "refGetAndSet":
    case "refSetAndGet":
    case "deferredIsDone":
    case "deferredPoll":
    case "deferredSucceed":
    case "deferredFail":
    case "deferredAwait":
    case "scopeMake":
    case "sleep":
    case "clockNow":
    case "external":
    case "deferredMakeOf":
    case "call":
    case "param":
      return undefined
    default: {
      const unclassified: never = op
      return unclassified
    }
  }
}

/**
 * The type arguments an operation carries on its call's head (Lean `NativeOp.typeArgs`, the
 * native signature's `typeArgsOf`): the two types of `Deferred.make<A, E>()`. No other operation
 * carries one. The switch lists every constructor, so an appended one is a type error here until
 * it is classified.
 */
export const typeArgsOf = (op: NativeOp): ReadonlyArray<Ty> => {
  switch (op._tag) {
    case "deferredMakeOf":
      return [op.value, op.error]
    case "refMake":
    case "refGet":
    case "refSet":
    case "refGetAndSet":
    case "refSetAndGet":
    case "refUpdateWith":
    case "refGetAndUpdateWith":
    case "refUpdateAndGetWith":
    case "refUpdateSomeWith":
    case "refGetAndUpdateSomeWith":
    case "refUpdateSomeAndGetWith":
    case "refModifyWith":
    case "refModifySomeWith":
    case "deferredIsDone":
    case "deferredPoll":
    case "deferredSucceed":
    case "deferredFail":
    case "deferredAwait":
    case "scopeMake":
    case "sleep":
    case "clockNow":
    case "external":
    case "call":
    case "param":
      return []
    default: {
      const unclassified: never = op
      return unclassified
    }
  }
}

/**
 * The operation at other type arguments (Lean `NativeOp.withTypeArgs`, the native signature's
 * `withTypeArgs`); an operation that carries none is unchanged. At a list of another length it
 * answers the operation the row's key spells, `Deferred.make` at `(nat, nat)`, as Lean does. A
 * reader installs only a list of the operation's own length (`installTypeArgs`).
 */
export const withTypeArgs = (op: NativeOp, tys: ReadonlyArray<Ty>): NativeOp => {
  if (op._tag !== "deferredMakeOf") return op
  const [value, error] = tys
  return tys.length === 2 && value !== undefined && error !== undefined
    ? { _tag: "deferredMakeOf", value, error }
    : { _tag: "deferredMakeOf", value: { _tag: "nat" }, error: { _tag: "nat" } }
}

/** The row call an expression holds before its last argument, and that argument's body, when
 * the last argument is a function of the current value at level `n`: `(aN) => body`, the binder
 * due at the node's level (Lean `splitFunction`, `Binders.read n [0]`). The printer writes an
 * operation's binder term there (`printPerform`). An annotated parameter or a declared result
 * never reaches this fragment (§ 2 refuses both). */
const splitFunction = (n: number, x: Expr): { readonly call: Expr; readonly body: Expr } | undefined => {
  if (x._tag !== "call" && x._tag !== "method") return undefined
  const last = x.args[x.args.length - 1]
  if (last === undefined || last._tag !== "lambda" || !sameParams(n, [0], last.params)) return undefined
  return { call: { ...x, args: x.args.slice(0, -1) }, body: last.body }
}

/** The spelling a row call names: a call's head, with or without type arguments, or a method's
 * name. A refusal of the row call names it (Lean `(sig.rowOf op).spelling`). */
const calledSpelling = (x: Expr): string => {
  if (x._tag === "method") return x.name
  if (x._tag !== "call") return ""
  const fn = x.fn._tag === "generic" ? x.fn.fn : x.fn
  return fn._tag === "ident" ? fn.name : fn._tag === "member" ? fn.name : ""
}

/** A row call without the type arguments on its head, and their spellings (Lean
 * `splitHeadTypes`): `s<T…>(args)` as `s(args)`, and a method call `r.s<T…>(args)` as
 * `r.s(args)`. `undefined` for a call whose head carries none, and for any other tree. */
const splitHeadTypes = (x: Expr): { readonly bare: Expr; readonly types: ReadonlyArray<string> } | undefined => {
  if (x._tag !== "call" || x.fn._tag !== "generic" || x.fn.typeArgs.length === 0) return undefined
  const head = x.fn.fn
  if (head._tag === "ident") return { bare: { _tag: "call", fn: head, args: x.args }, types: x.fn.typeArgs }
  if (head._tag === "member") return { bare: { _tag: "method", base: head.base, name: head.name, args: x.args }, types: x.fn.typeArgs }
  return undefined
}

/** A row call with the type arguments of its head read (Lean `readCall`; the state plan's T5,
 * part B). A call whose head carries type arguments is first read without them, at its face.
 * Where that names an operation, the type arguments are the operation's: they are as many as it
 * carries, each is read by the checked type reader (`readTypeText`), and the list is installed
 * (Lean `installTypeArgs`). Where it names none, the type arguments are the row's own declared
 * ones: the whole call is read at its face, as a call with no type argument is, and must name an
 * operation that carries none (Lean `typeFree`). So `Deferred.make()` is refused by its
 * spelling, never read at a default (`E4-CHECK-CE-013`). A type argument with no reading is
 * refused by name (Lean's `annotation "<spelling> type argument"`). */
const readCall = (n: number, x: Expr): Read<Eff> => {
  const split = splitHeadTypes(x)
  if (split !== undefined) {
    const bare = readPerformFace(n, split.bare)
    if (!failed(bare)) {
      const eff = bare.success
      if (eff._tag !== "perform") return refuse({ _tag: "shape", what: "operation data" })
      if (typeArgsOf(eff.op).length !== split.types.length) return arity(calledSpelling(x))
      const tys: Ty[] = []
      for (const text of split.types) {
        const ty = readTypeText(text)
        if (ty === undefined) return refuse({ _tag: "shape", what: `${calledSpelling(x)} type argument annotation` })
        tys.push(ty)
      }
      return ok({ _tag: "perform", op: withTypeArgs(eff.op, tys), request: eff.request })
    }
  }
  const face = readPerformFace(n, x)
  if (failed(face)) return face
  const eff = face.success
  if (eff._tag !== "perform") return refuse({ _tag: "shape", what: "operation data" })
  return typeArgsOf(eff.op).length === 0 ? face : arity(calledSpelling(x))
}

/** The row call at a node of level `n` (Lean `readPerform`). A call whose last argument is the
 * function of the current value is a term row's: the call before it is read with its head's type
 * arguments (`readCall`, over the face reader `readPerformFace`), the function's body as a term
 * one level up, where the current value is the binder at `n` (decisions row 43), and the term is
 * installed in the operation read (Lean `installTerm`). Any other tree is read the same way and
 * must name an operation that carries no term (Lean `termFree`): a term row called without its
 * function is refused by its spelling. The type arguments are installed before the term. */
const readPerform = (n: number, x: Expr): Read<Eff> => {
  const split = splitFunction(n, x)
  if (split !== undefined) {
    const typed = readCall(n, split.call)
    if (failed(typed)) return typed
    const f = readTerm(n + 1, split.body)
    if (failed(f)) return again(f)
    const eff = typed.success
    if (eff._tag !== "perform") return refuse({ _tag: "shape", what: "operation data" })
    const op = withTerm(eff.op, f.success)
    return op === undefined ? arity(calledSpelling(split.call)) : ok({ _tag: "perform", op, request: eff.request })
  }
  const typed = readCall(n, x)
  if (failed(typed)) return typed
  const eff = typed.success
  if (eff._tag !== "perform") return refuse({ _tag: "shape", what: "operation data" })
  return withTerm(eff.op, unit) !== undefined ? arity(calledSpelling(x)) : typed
}

/** What is not a skeleton, read as the printer's hand fields print it (`readPerformFace`): a
 * bare identifier as a value row, a call as a call row, a method call as a method row. A
 * reserved head no row matched is refused by its argument list when it heads a program clause,
 * and by its name otherwise. The operation it answers is the one the row spells, its face. */
const readPerformFace = (n: number, x: Expr): Read<Eff> => {
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
    if (row.fam !== fam) continue
    // the row call stands last among the program rows: a tree is one when it is nothing else
    if (row.out._tag === "rowCall") {
      if (fam !== "eff") return undefined
      const r = readPerform(n, x)
      if (failed(r)) {
        const expected = nearestRow(n, x)
        if (expected !== undefined) locations.set(r.failure, { path: [], expected })
      }
      return r
    }
    // an invocation with programs (decisions row 340, slice HO-3b): a call of a name that spells
    // the invocation of a definition that takes programs (§ 5, `readInvoke`)
    if (row.out._tag === "invoke") {
      const r = fam === "eff" ? readInvoke(k, n, x) : undefined
      if (r !== undefined) return r
      continue
    }
    if (row.out._tag !== "tpl") continue // a statement row is read by `readStmts`
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
        if (failed(inner)) return again(under(inner, row.ctor, 0) as Result.Failure<unknown, Refusal>)
        // exactness, as for every row: the printer would choose this row
        if (chosenRow(fam, row.ctor, [inner.success]) !== k) return refuse({ _tag: "shape", what: "not the printed row" })
        return ok(build(row.ctor, names, [inner.success]))
      }
      const leaf = readLeaf(n, true, sorts[0]!, { _tag: "expr", e: x })
      if (failed(leaf) || chosenRow(fam, row.ctor, [leaf.success]) !== k) continue
      return ok(build(row.ctor, names, [leaf.success]))
    }
    const captured: Subst = new Map()
    if (!matchT(n, t, x, captured)) continue
    return readRow(k, row, n, sorts, names, captured)
  }
  return undefined
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
      let node = under(readRow(k, row, depth, sorts, names, captured), "cons", 0)
      for (let j = 0; j < out.length; j++) node = under(node, "cons", 1)
      if (failed(node)) return again(node)
      out.push(node.success as Stmt)
      depth += row.out.declares
      continue next
    }
    let none: Read<never> = under(refuse({ _tag: "unsupportedStmt" }), "cons", 0)
    for (let j = 0; j < out.length; j++) none = under(none, "cons", 1)
    return none
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

/** The default of each switch of `childrenOf`. Its argument has no value when every constructor
 * of the sort has a case, so a constructor with no case is refused where this file is
 * type-checked (`bun run typecheck`). The constructor lists are the generated types'
 * (`eff.gen.ts`); `test/red/walkers.red.ts` is the red twin. */
const noChildCase = (node: never): never => { throw new Error(`childrenOf has no case for ${JSON.stringify(node)}`) }

/**
 * A node's children, in the order the path scheme numbers them — a node's children are these
 * and nothing else (`Node.child`). A spine is a cons cell: its head is child 0 and its tail
 * child 1, so element `i` of the spine at child `c` of `p` is at `p ++ [c] ++ [1]*i ++ [0]`.
 *
 * A hand copy of `Node.child`, which Lean generates (`src/Effect4/Program/NodeLenses.lean`).
 * Every constructor has a case, a leaf too. Until 2026-10-06 a constructor with no case was a
 * leaf without a word, and a `restore` had no child: a layer declared under a restore site
 * went back to no path, and the module was refused.
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
        case "restore": return [atEff(e.body, (body) => kEff({ ...e, body }))]
        // a provider region (decisions row 349): its body is child 0
        case "provideContext": return [atEff(e.body, (body) => kEff({ ...e, body }))]
        // a definition block (decisions row 328): its bodies' spine is child 0, its main program
        // child 1, the module's layers' spine child 2 (decisions row 341)
        case "defs":
          return [atEffs(e.bodies, (bodies) => kEff({ ...e, bodies })), atEff(e.main, (main) => kEff({ ...e, main })),
            atLayers(e.layers, (layers) => kEff({ ...e, layers }))]
        // an invocation with programs (decisions row 340): its programs' spine is child 0
        case "invoke": return [atEffs(e.args, (args) => kEff({ ...e, args }))]
        case "succeed": case "fail": case "failCause": case "sync": case "perform": case "yieldNow": case "awaitFiber": case "service":
          return []
        default: return noChildCase(e)
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
        case "succeed": case "ref": return []
        default: return noChildCase(l)
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
        case "ret": case "breakLoop": return []
        default: return noChildCase(s)
      }
    }
    case "action": {
      const a = n.action
      switch (a._tag) {
        case "fork": return [atEff(a.program, (program) => kAction({ ...a, program }))]
        case "forkIn": return [atEff(a.program, (program) => kAction({ ...a, program }))]
        case "forkScoped": return [atEff(a.program, (program) => kAction({ ...a, program }))]
        case "raceAll": case "raceAllFirst": return [atEffs(a.entrants, (entrants) => kAction({ ...a, entrants }))]
        case "runIn": case "interrupt": case "interruptScoped": case "interruptAll": case "awaitAll": case "awaitAllFailFast":
        case "snapshotChildren": case "awaitNewChildren": case "context": case "getId": case "closeScope":
        case "getInterruptible":
          return []
        default: return noChildCase(a)
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
 * A declaration block back to the program (`readModule` of `Read.lean`): past the payload classes,
 * the services of the rows the module declares (`rows`: the table's for a file, none for the block
 * a host wraps; § 5), then a definition block when the module has one (§ 5), else every
 * `const L_<path>` before the last statement as a layer term put back at the path its name
 * carries. Every occurrence of the identifier — the defining site and each reference — reads as
 * `ref <path>` in § 3, so putting the declaration back at that path leaves the first occurrence
 * (the site at exactly that path, which is what `printModule` hoists) the layer itself and every
 * later occurrence a reference to it. Services other than the rows' are `shape "row services"`;
 * a declaration whose name is no canonical path spelling, or whose path names no layer, is
 * `shape "module"`.
 */
const readModule = (declarations: ReadonlyArray<Declaration>, main: Node, rows: ReadonlyArray<Row>): Read<Eff> => {
  const after = readRowServices(declarations, rows)
  if (after === undefined) return refuse({ _tag: "shape", what: "row services" })
  // the leading definition constants (Lean `defsPrefix`): no layer path, no service's key or layer
  const defsEnd = after.findIndex((c) => readRefName(c.name) !== undefined || isServiceConst(c.value))
  const defDecls = defsEnd === -1 ? after : after.slice(0, defsEnd)
  if (defDecls.length > 0) return readBlock(defDecls, defsEnd === -1 ? [] : after.slice(defsEnd), main)
  const program = readProgramExpr(main)
  if (failed(program)) return again(program)
  const decls: Array<readonly [ReadonlyArray<number>, LayerTerm]> = []
  for (const declaration of after) {
    const d = readLayerDecl(declaration)
    if (failed(d)) return again(d)
    decls.push(d.success)
  }
  const whole = restoreAll(program.success, decls)
  return whole === undefined ? refuse({ _tag: "shape", what: "module" }) : ok(decodeEff(whole))
}

/* ============================================================ § 5  a module: the rows' services and a definition block */

// The rest of Lean's `readModule` (`src/Effect4/Codegen/Read.lean`): past the payload classes, a
// file declares the services of its rows (`readRowServices`, `Codegen/RowServices.lean`; decisions
// row 378 (19)), then a definition block may follow (decisions row 328): its definitions, the
// services its roles declare, the module's layers, the hoisted layers and the main program. The
// block's definitions and a body's parameters are names the rows' spelling map is extended by
// (`defsSpell`, `paramsSpell`). Every check here reads oxc's nodes: a header's annotations and a
// method's typed parameters are no fragment of § 2.


/** A block's definitions, by name, and inside a body its parameters, which a name with no
 * trailing arguments spells first (Lean `namedSpell`): a definition's name spells its
 * invocation (`NativeOp.call`), a parameter's its run (`NativeOp.param`). Bound for the duration
 * of one block's reading. */
let named: ReadonlyArray<Entry> = []
let namedDecls: ReadonlyArray<DefDecl> = []
const withNamed = <A>(entries: ReadonlyArray<Entry>, decls: ReadonlyArray<DefDecl>, body: () => A): A => {
  const saved = named, savedDecls = namedDecls
  named = entries
  namedDecls = decls
  try {
    return body()
  } finally {
    named = saved
    namedDecls = savedDecls
  }
}

/** The row a definition or a parameter declares: a program row of its columns, answered by its
 * body or by the program a call passes (Lean `DefDecl.row`, `ParamDecl.row`). */
const programRow = (name: string, request: Ty, answer: Ty, error: Ty, requires: ReadonlyArray<ServiceKey>): Row => ({
  name, spelling: name, shape: "call", trailing: [], kind: "program", request, answer, error,
  requires, cite: "", typeArgs: [], registration: "deferred",
})

const defEntries = (decls: ReadonlyArray<DefDecl>): ReadonlyArray<Entry> =>
  decls.map((d, index): Entry => ({ op: { _tag: "call", index }, row: programRow(d.name, d.request, d.answer, d.error, d.requires) }))

const paramEntries = (params: ReadonlyArray<ParamDecl>): ReadonlyArray<Entry> =>
  params.map((q, index): Entry => ({ op: { _tag: "param", index }, row: programRow(q.name, q.request, q.answer, q.error, []) }))

/** The definition a name invokes with programs (Lean `invokedDef`): the index of the definition
 * the name spells, when it takes programs. */
const invokedDef = (s: string): number | undefined => {
  const e = named.find((entry) => entry.row.spelling === s)
  if (e === undefined || e.op._tag !== "call") return undefined
  const d = namedDecls[e.op.index]
  return d !== undefined && d.params.length > 0 ? e.op.index : undefined
}

/** An invocation with programs (Lean `readRow`'s `invoke` arm, slice HO-3b): a call whose head
 * spells the invocation of a definition that takes programs, on its request and on one function
 * of the binder due at `n` for each program; the programs read at `n + 1`. `undefined` when the
 * tree is no such call. */
const readInvoke = (k: number, n: number, x: Expr): Read<unknown> | undefined => {
  if (x._tag !== "call" || x.fn._tag !== "ident") return undefined
  const [rq, ...fns] = x.args
  if (rq === undefined) return undefined
  const j = invokedDef(x.fn.name)
  if (j === undefined) return undefined
  const bodies: Expr[] = []
  for (const f of fns) {
    if (f._tag !== "lambda" || !sameParams(n, [0], f.params)) return undefined
    bodies.push(f.body)
  }
  const request = under(readTerm(n, rq), "invoke", 1)
  if (failed(request)) return again(request)
  const programs = under(readSpine("effs", n + 1, bodies), "invoke", 2)
  if (failed(programs)) return again(programs)
  const args = [j, request.success, programs.success]
  if (chosenRow("eff", "invoke", args) !== k) return refuse({ _tag: "shape", what: "not the printed row" })
  const names = argNamesOf("eff", "invoke")
  return names === undefined ? tableDefect() : ok(build("invoke", names, args))
}

/* ---------- the rows' services (Lean `Codegen/RowServices.lean`) ---------- */

/** The ambient values a binding name may not take (Lean `Names.reservedExtra`, generated). */
const reservedExtra: ReadonlyArray<string> = nameTables.reservedExtra

/** A binding name (Lean `Names.binderName`): a target identifier that is no ambient value. */
const bindingName = (name: string): boolean => targetIdentifier(name) && !reservedExtra.includes(name)

/** A spelling `Ns.method` as its namespace and its method (Lean `serviceParts`): a binding name,
 * one dot, and a property name, which may be a keyword. */
const serviceParts = (spelling: string): readonly [string, string] | undefined => {
  const dot = spelling.indexOf(".")
  if (dot < 0 || spelling.indexOf(".", dot + 1) >= 0) return undefined
  const ns = spelling.slice(0, dot), m = spelling.slice(dot + 1)
  return bindingName(ns) && /^[A-Za-z_$][A-Za-z0-9_$]*$/.test(m) ? [ns, m] : undefined
}

/** The service a row belongs to (Lean `Row.serviceCall?`): a call row with no trailing argument
 * and no declared type argument, whose requirement column names one key and whose spelling is
 * `Ns.method`. */
const serviceCall = (row: Row): readonly [string, string] | undefined =>
  row.requires.length === 1 && row.shape === "call" && row.trailing.length === 0 && row.typeArgs.length === 0
    ? serviceParts(row.spelling) : undefined

/** The members of an rc.112 service key, which an accessor would shadow (Lean
 * `serviceKeyMembers`, generated). */
const serviceKeyMembers: ReadonlyArray<string> = nameTables.serviceKeyMembers

interface RowService {
  readonly ns: string
  readonly key: ServiceKey
  readonly methods: ReadonlyArray<readonly [string, Row]>
}

/** The services of a table's service rows, one for each namespace, in the order of its first
 * row (Lean `rowServices`). */
const rowServices = (table: ReadonlyArray<Row>): ReadonlyArray<RowService> => {
  const rows = table.flatMap((row) => {
    const call = serviceCall(row)
    return call === undefined ? [] : [{ ns: call[0], key: row.requires[0]!, m: call[1], row }]
  })
  const spaces = [...new Set(rows.map((r) => r.ns))]
  return spaces.map((ns) => ({
    ns, key: rows.find((r) => r.ns === ns)!.key,
    methods: rows.filter((r) => r.ns === ns).map((r): readonly [string, Row] => [r.m, r.row]),
  }))
}

/** Whether one row breaks the table's services (Lean `rowBreaksServices`). */
const breaksServices = (services: ReadonlyArray<RowService>, row: Row): boolean => {
  const call = serviceCall(row)
  if (call !== undefined && row.requires.length === 1) {
    const [ns, m] = call
    const key = row.requires[0]!
    return serviceKeyMembers.includes(m) ||
      services.some((s) => s.ns === ns && (!sameKey(s.key, key) || s.methods.filter(([n]) => n === m).length !== 1)) ||
      services.some((s) => s.ns !== ns && (sameKey(s.key, key) || s.ns === `${ns}Key`))
  }
  if (call === undefined && row.requires.length === 0) {
    const parts = serviceParts(row.spelling)
    return parts !== undefined && services.some((s) => s.ns === parts[0])
  }
  return true
}

/** What a service's two declarations print (Lean `RowServiceData`): the namespace, the key's
 * identity, the text of the key's shape, and each method with its request's type text (`undefined`
 * on a `unit` request). `undefined` where Lean's `rowServiceData` refuses. */
interface ServiceData {
  readonly ns: string
  readonly identity: string
  readonly shape: string
  readonly methods: ReadonlyArray<readonly [string, string | undefined]>
}

const rowServiceData = (table: ReadonlyArray<Row>): ReadonlyArray<ServiceData> | undefined => {
  const services = rowServices(table)
  if (table.some((row) => breaksServices(services, row))) return undefined
  const out: ServiceData[] = []
  for (const s of services) {
    if (nativeScopeKey !== undefined && sameKey(s.key, nativeScopeKey)) return undefined
    const fields: string[] = []
    const methods: Array<readonly [string, string | undefined]> = []
    for (const [m, row] of s.methods) {
      const unit = normalize(row.request)._tag === "unit"
      const request = unit ? undefined : targetType(row.request, legacyType, declaredKeyNames)
      const answer = targetType(row.answer, legacyType, declaredKeyNames)
      const error = targetType(row.error, legacyType, declaredKeyNames)
      if ((!unit && request === undefined) || answer === undefined || error === undefined) return undefined
      fields.push(`readonly ${targetIdentifier(m) ? m : quoteType(m)}: (${request === undefined ? "" : `a0: ${request}`}) => ` +
        `Effect.Effect<${answer}, ${error}, never>`)
      methods.push([m, request])
    }
    out.push({ ns: s.ns, identity: keySpelling(declaredKeyNames, s.key), shape: fields.length === 0 ? "{}" : `{ ${fields.join("; ")} }`, methods })
  }
  return out
}

/** A property's key name, plain or a string literal. */
const propertyKey = (p: Node): string | undefined => {
  const key = nodeAt(p, "key")
  if (p.computed === true || !key) return undefined
  return key.type === "Identifier" && typeof key.name === "string" ? key.name
    : key.type === "Literal" && typeof key.value === "string" ? key.value : undefined
}

/** An identifier node with no annotation, by name. */
const plainIdent = (n: Node | undefined, name: string): boolean =>
  n !== undefined && n.type === "Identifier" && n.name === name && !n.typeAnnotation

/** A method's accessor exactly as Lean's `accessorExpr` writes it: `(a0: T) => NsKey.use((a1) =>
 * a1.m(a0))`, and `() => NsKey.use((a0) => a0.m())` on a `unit` request. */
const isAccessor = (keyName: string, m: string, request: string | undefined, f: Node): boolean => {
  if (f.type !== "ArrowFunctionExpression" || f.async === true || f.typeParameters || f.returnType || f.expression !== true) return false
  const params = listAt(f, "params") ?? []
  const inner = request === undefined ? "a0" : "a1"
  if (request === undefined ? params.length !== 0 : params.length !== 1) return false
  if (request !== undefined) {
    const p = params[0]
    const annotation = isNode(p) ? nodeAt(p, "typeAnnotation") : undefined
    const type = annotation && nodeAt(annotation, "typeAnnotation")
    if (!isNode(p) || p.type !== "Identifier" || p.name !== "a0" || !type || typeName(type) !== request) return false
  }
  const use = nodeAt(f, "body")
  if (use?.type !== "CallExpression" || use.optional === true || use.typeArguments) return false
  const useCallee = nodeAt(use, "callee")
  const [g] = listAt(use, "arguments") ?? []
  if (!useCallee || dotted(useCallee) !== `${keyName}.use` || (listAt(use, "arguments") ?? []).length !== 1 || !isNode(g)) return false
  if (g.type !== "ArrowFunctionExpression" || g.async === true || g.typeParameters || g.returnType || g.expression !== true) return false
  const gParams = listAt(g, "params") ?? []
  if (gParams.length !== 1 || !isNode(gParams[0]) || !plainIdent(gParams[0], inner)) return false
  const call = nodeAt(g, "body")
  if (call?.type !== "CallExpression" || call.optional === true || call.typeArguments) return false
  const member = nodeAt(call, "callee")
  if (member?.type !== "MemberExpression" || member.computed === true || member.optional === true) return false
  const object = nodeAt(member, "object"), property = nodeAt(member, "property")
  if (!plainIdent(object, inner) || property?.type !== "Identifier" || property.name !== m) return false
  const args = listAt(call, "arguments") ?? []
  return request === undefined ? args.length === 0 : args.length === 1 && isNode(args[0]) && plainIdent(args[0], "a0")
}

/** Whether two const declarations are exactly a service's (Lean `RowServiceData.isDecls`): the
 * key `NsKey = Context.Service<"identity", Shape>("identity")` and the namespace
 * `Ns = Object.assign(NsKey, { m: accessor, … })`, both exported and unannotated. */
const isServiceDecls = (d: ServiceData, key: Declaration, ns: Declaration): boolean => {
  const keyName = `${d.ns}Key`
  if (key.name !== keyName || !key.exported || key.annotated || ns.name !== d.ns || !ns.exported || ns.annotated) return false
  const k = key.value
  const kCallee = nodeAt(k, "callee")
  const kTypes = nodeAt(k, "typeArguments")
  const kParams = kTypes ? listAt(kTypes, "params") ?? [] : []
  const kArgs = listAt(k, "arguments") ?? []
  const identity = quotedTypeString(d.identity)
  if (k.type !== "CallExpression" || k.optional === true || !kCallee || dotted(kCallee) !== "Context.Service" ||
      kParams.length !== 2 || !isNode(kParams[0]) || typeName(kParams[0]) !== identity ||
      !isNode(kParams[1]) || typeName(kParams[1]) !== d.shape ||
      kArgs.length !== 1 || !isNode(kArgs[0]) || kArgs[0].type !== "Literal" || kArgs[0].value !== d.identity) return false
  const a = ns.value
  const aCallee = nodeAt(a, "callee")
  const aArgs = listAt(a, "arguments") ?? []
  if (a.type !== "CallExpression" || a.optional === true || a.typeArguments || !aCallee || dotted(aCallee) !== "Object.assign" ||
      aArgs.length !== 2 || !isNode(aArgs[0]) || !plainIdent(aArgs[0], keyName) || !isNode(aArgs[1]) ||
      aArgs[1].type !== "ObjectExpression") return false
  const properties = listAt(aArgs[1], "properties") ?? []
  if (properties.length !== d.methods.length) return false
  return d.methods.every(([m, request], i) => {
    const p = properties[i]
    if (!isNode(p) || p.type !== "Property" || p.kind !== "init" || p.method === true || p.shorthand === true) return false
    const value = nodeAt(p, "value")
    return propertyKey(p) === m && value !== undefined && isAccessor(keyName, m, request, value)
  })
}

/** **The rows' services read back** (Lean `readRowServices`): the leading declarations that are
 * exactly the declarations of the services of `rows`, two for each service in table order, and the
 * declarations after them. `undefined` when the services do not print or the declarations do not
 * begin with theirs. */
const readRowServices = (decls: ReadonlyArray<Declaration>, rows: ReadonlyArray<Row>): ReadonlyArray<Declaration> | undefined => {
  const data = rowServiceData(rows)
  if (data === undefined) return undefined
  if (decls.length < 2 * data.length) return undefined
  return data.every((d, i) => isServiceDecls(d, decls[2 * i]!, decls[2 * i + 1]!)) ? decls.slice(2 * data.length) : undefined
}

/* ---------- a definition block (Lean `readDefHead`, `readServices`, `readDefBody`) ---------- */

/** Whether a constant is a service's key or layer (Lean `isServiceConst`): a call of
 * `Context.Service` at type arguments, or of `Layer.effect`. */
const isServiceConst = (value: Node): boolean => {
  if (value.type !== "CallExpression") return false
  const callee = nodeAt(value, "callee")
  const head = callee && dotted(callee)
  return (head === "Context.Service" && nodeAt(value, "typeArguments") !== undefined) ||
    (head === "Layer.effect" && nodeAt(value, "typeArguments") === undefined)
}

/** `Effect.Effect<A, E, R>` as its three type nodes. */
const effectColumns = (t: Node | undefined): readonly [Node, Node, Node] | undefined => {
  if (t?.type !== "TSTypeReference") return undefined
  const ref = nodeAt(t, "typeName")
  const args = nodeAt(t, "typeArguments")
  const params = args ? listAt(args, "params") ?? [] : []
  const [a, e, r] = params
  return ref && qualifiedTypeName(ref) === "Effect.Effect" && params.length === 3 && isNode(a) && isNode(e) && isNode(r)
    ? [a, e, r] : undefined
}

/** A type annotation's type node. */
const annotationOf = (n: Node): Node | undefined => {
  const annotation = nodeAt(n, "typeAnnotation")
  return annotation && nodeAt(annotation, "typeAnnotation")
}

/** A parameter's declaration from its binder in a header (Lean `readParam`):
 * `name: (a0: Request) => Effect.Effect<A, E, never>`, each column under the module's classes and
 * key names. */
const readParam = (p: unknown): ParamDecl | undefined => {
  if (!isNode(p) || p.type !== "Identifier" || typeof p.name !== "string" || p.optional === true) return undefined
  const fn = annotationOf(p)
  if (fn?.type !== "TSFunctionType" || fn.typeParameters) return undefined
  const params = listAt(fn, "params") ?? []
  const binder = params[0]
  const request = isNode(binder) && binder.type === "Identifier" && binder.name === "a0" ? annotationOf(binder) : undefined
  const result = nodeAt(fn, "returnType")
  const columns = effectColumns(result && nodeAt(result, "typeAnnotation"))
  if (params.length !== 1 || request === undefined || columns === undefined || typeName(columns[2]) !== "never") return undefined
  const req = readTypeChecked(request, declaredClasses, declaredKeyNames, true)
  const answer = readTypeChecked(columns[0], declaredClasses, declaredKeyNames, true)
  const error = readTypeChecked(columns[1], declaredClasses, declaredKeyNames, true)
  return req === undefined || answer === undefined || error === undefined ? undefined
    : { name: p.name, request: req, answer, error }
}

/** A definition's declaration and its body's node from its constant (Lean `readDefHead`):
 * `(a0: Request, p: …): Effect.Effect<A, E, R> => body`, its columns under the module's classes,
 * key names and `refs = true`, and its requirement row by the requirement reader. The role is the
 * services' (`roleOf`). */
const readDefHead = (c: Declaration): Read<readonly [DefDecl, Node]> => {
  const bad = refuse({ _tag: "shape", what: "definition" })
  const f = c.value
  if (f.type !== "ArrowFunctionExpression" || f.async === true || f.typeParameters || f.expression !== true) return bad
  const [first, ...rest] = listAt(f, "params") ?? []
  const request = isNode(first) && first.type === "Identifier" && first.name === "a0" ? annotationOf(first) : undefined
  const result = nodeAt(f, "returnType")
  const columns = effectColumns(result && nodeAt(result, "typeAnnotation"))
  const body = nodeAt(f, "body")
  if (request === undefined || columns === undefined || body === undefined) return bad
  const req = readTypeChecked(request, declaredClasses, declaredKeyNames, true)
  const answer = readTypeChecked(columns[0], declaredClasses, declaredKeyNames, true)
  const error = readTypeChecked(columns[1], declaredClasses, declaredKeyNames, true)
  const rowText = typeName(columns[2])
  const requires = rowText === undefined ? undefined : readKeysText(rowText)
  const params = rest.map(readParam)
  if (req === undefined || answer === undefined || error === undefined || requires === undefined ||
      params.some((q) => q === undefined)) return bad
  return ok([{ name: c.name, request: req, answer, error, requires, role: { _tag: "plain" }, params: params as ParamDecl[] }, body])
}

type ServiceInfo = { readonly name: string; readonly init: string; readonly methods: ReadonlyArray<readonly [string, string, number]> }

/** The request a method's closure passes its definition (Lean `isMethodRequest`): the state `a0`,
 * then its arguments `a1` … `an` as `argTuple` writes them. */
const isMethodRequest = (arity: number, e: Node): boolean => {
  const isPairOf = (x: Node, first: string, rest: (y: Node) => boolean): boolean => {
    if (x.type !== "CallExpression") return false
    const callee = nodeAt(x, "callee")
    const args = listAt(x, "arguments") ?? []
    return callee !== undefined && plainIdent(callee, "pair") && args.length === 2 &&
      isNode(args[0]) && plainIdent(args[0], first) && isNode(args[1]) && rest(args[1])
  }
  const tuple = (from: number, x: Node): boolean =>
    from === arity ? plainIdent(x, `a${from}`) : isPairOf(x, `a${from}`, (y) => tuple(from + 1, y))
  return arity === 0 ? plainIdent(e, "a0") : isPairOf(e, "a0", (y) => tuple(1, y))
}

/** A service's layer (Lean `readServiceLayer`): `Layer.effect(S, Effect.map(init(), (a0) => {
 * return { m: (a1, …, p, …) => d(pair(a0, …), p, …), … } }))`. A closure takes its arguments, then
 * its definition's programs, which it passes on by name (Lean `readServiceMethod`, slice HO-5): its
 * arity is its parameters less those programs. A closure's parameters' annotations are not read:
 * they are erased in the run. */
const readServiceLayer = (c: Declaration): ServiceInfo | undefined => {
  const v = c.value
  const callee = nodeAt(v, "callee")
  const [s, mapped] = listAt(v, "arguments") ?? []
  if (v.type !== "CallExpression" || !callee || dotted(callee) !== "Layer.effect" || (listAt(v, "arguments") ?? []).length !== 2 ||
      !isNode(s) || s.type !== "Identifier" || typeof s.name !== "string" || !isNode(mapped) || mapped.type !== "CallExpression") return undefined
  const mapCallee = nodeAt(mapped, "callee")
  const [initCall, fn] = listAt(mapped, "arguments") ?? []
  if (!mapCallee || dotted(mapCallee) !== "Effect.map" || (listAt(mapped, "arguments") ?? []).length !== 2 ||
      !isNode(initCall) || initCall.type !== "CallExpression" || (listAt(initCall, "arguments") ?? []).length !== 0) return undefined
  const initCallee = nodeAt(initCall, "callee")
  if (initCallee?.type !== "Identifier" || typeof initCallee.name !== "string") return undefined
  if (!isNode(fn) || fn.type !== "ArrowFunctionExpression" || fn.async === true || fn.typeParameters || fn.expression === true ||
      fn.returnType) return undefined
  const fnParams = listAt(fn, "params") ?? []
  if (fnParams.length !== 1 || !isNode(fnParams[0]) || !plainIdent(fnParams[0], "a0")) return undefined
  const block = listAt(nodeAt(fn, "body") ?? fn, "body") ?? []
  const ret = block[0]
  const object = block.length === 1 && isNode(ret) && ret.type === "ReturnStatement" ? nodeAt(ret, "argument") : undefined
  if (object?.type !== "ObjectExpression") return undefined
  const methods: Array<readonly [string, string, number]> = []
  for (const p of listAt(object, "properties") ?? []) {
    if (!isNode(p) || p.type !== "Property" || p.kind !== "init" || p.method === true || p.shorthand === true) return undefined
    const m = propertyKey(p)
    const closure = nodeAt(p, "value")
    if (m === undefined || closure?.type !== "ArrowFunctionExpression" || closure.async === true || closure.typeParameters ||
        closure.expression !== true || closure.returnType) return undefined
    const params = listAt(closure, "params") ?? []
    const call = nodeAt(closure, "body")
    const head = call && nodeAt(call, "callee")
    const args = call ? listAt(call, "arguments") ?? [] : []
    const passed = args.slice(1)
    if (!passed.every((a) => isNode(a) && a.type === "Identifier" && typeof a.name === "string")) return undefined
    const names = passed.map((a) => (a as Node).name as string)
    const arity = params.length - names.length
    if (arity < 0 || !params.every((q, i) => isNode(q) && q.type === "Identifier" &&
        q.name === (i < arity ? `a${i + 1}` : names[i - arity]))) return undefined
    if (call?.type !== "CallExpression" || head?.type !== "Identifier" || typeof head.name !== "string" || args.length < 1 ||
        !isNode(args[0]) || !isMethodRequest(arity, args[0])) return undefined
    methods.push([m, head.name, arity])
  }
  return { name: s.name, init: initCallee.name, methods }
}

/** A block's service constants (Lean `readServices`): each service's key, `const S =
 * Context.Service<"S", Shape>("S")` (its shape is not read: it is erased in the run), then its
 * layer, named for the key. Every constant is one of these, or the reading refuses. */
const readServices = (consts: ReadonlyArray<Declaration>): ReadonlyArray<ServiceInfo> | undefined => {
  const out: ServiceInfo[] = []
  for (let i = 0; i < consts.length; i += 2) {
    const key = consts[i]!, layer = consts[i + 1]
    if (layer === undefined) return undefined
    const info = readServiceLayer(layer)
    if (info === undefined || layer.name !== `${info.name}Layer` || key.name !== info.name) return undefined
    const k = key.value
    const callee = nodeAt(k, "callee")
    const types = nodeAt(k, "typeArguments")
    const typeParams = types ? listAt(types, "params") ?? [] : []
    const [identity, shape] = typeParams
    const [arg] = listAt(k, "arguments") ?? []
    if (k.type !== "CallExpression" || !callee || dotted(callee) !== "Context.Service" || typeParams.length !== 2 ||
        !isNode(identity) || typeName(identity) !== quotedTypeString(info.name) || !isNode(shape) || shape.type !== "TSTypeLiteral" ||
        !isNode(arg) || arg.type !== "Literal" || arg.value !== info.name || (listAt(k, "arguments") ?? []).length !== 1) return undefined
    out.push(info)
  }
  return out
}

/** The role a block's services give a definition, by its name (Lean `roleOf`). */
const roleOf = (services: ReadonlyArray<ServiceInfo>, name: string): DefDecl["role"] => {
  const init = services.find((s) => s.init === name)
  if (init !== undefined) return { _tag: "serviceInit", service: init.name }
  for (const s of services) {
    const m = s.methods.find(([, d]) => d === name)
    if (m !== undefined) return { _tag: "serviceMethod", service: s.name, method: m[0], arity: m[2] }
  }
  return { _tag: "plain" }
}

/** A layer declaration back to its path and its layer (Lean `readLayerDecl`). */
const readLayerDecl = (c: Declaration): Read<readonly [ReadonlyArray<number>, LayerTerm]> => {
  const target = readRefName(c.name)
  if (target === undefined || refName(target) !== c.name) return refuse({ _tag: "shape", what: "module" })
  const fragment = exprOf(c.value)
  if (failed(fragment)) return again(fragment)
  const layer = readLayer(fragment.success)
  if (failed(layer)) return again(layer)
  return ok([target, layer.success])
}

/** A definition's body from its printed suspension, at environment length `1`, with its own
 * layers (Lean `readDefBody`): `Effect.suspend(() => body)`, or
 * `Effect.suspend(() => { let L_<path> = …; return body })`. */
const readDefBody = (x: Node): Read<readonly [Eff, ReadonlyArray<readonly [ReadonlyArray<number>, LayerTerm]>]> => {
  const bad = refuse({ _tag: "shape", what: "definition" })
  const callee = nodeAt(x, "callee")
  const [thunk] = listAt(x, "arguments") ?? []
  if (x.type !== "CallExpression" || !callee || dotted(callee) !== "Effect.suspend" || (listAt(x, "arguments") ?? []).length !== 1 ||
      !isNode(thunk) || thunk.type !== "ArrowFunctionExpression" || thunk.async === true || thunk.typeParameters ||
      (listAt(thunk, "params") ?? []).length !== 0 || thunk.returnType) return bad
  const body = nodeAt(thunk, "body")
  if (!body) return bad
  const readBody = (y: Node): Read<Eff> => {
    const fragment = exprOf(y)
    return failed(fragment) ? again(fragment) : readEff(1, fragment.success)
  }
  if (thunk.expression === true) return Result.map(readBody(body), (e) => [e, []] as const)
  const stmts = (listAt(body, "body") ?? []).filter(isNode)
  const last = stmts[stmts.length - 1]
  const result = last?.type === "ReturnStatement" ? nodeAt(last, "argument") : undefined
  if (result === undefined) return bad
  const locals: Array<readonly [ReadonlyArray<number>, LayerTerm]> = []
  for (const s of stmts.slice(0, -1)) {
    if (s.type !== "VariableDeclaration" || s.kind !== "let") return bad
    const [d] = listAt(s, "declarations") ?? []
    const id = isNode(d) ? nodeAt(d, "id") : undefined
    const init = isNode(d) ? nodeAt(d, "init") : undefined
    if ((listAt(s, "declarations") ?? []).length !== 1 || id?.type !== "Identifier" || typeof id.name !== "string" ||
        id.typeAnnotation || !init) return bad
    const local = readLayerDecl({ name: id.name, value: init, exported: false, annotated: false })
    if (failed(local)) return local.failure._tag === "shape" && local.failure.what === "module" ? bad : again(local)
    locals.push(local.success)
  }
  return Result.map(readBody(result), (e) => [e, locals] as const)
}

/** A path in a block's module layers: its head is the block's child `2` (Lean `inModulePath`). */
const inModulePath = (p: ReadonlyArray<number>): boolean => p[0] === 2

/** The module's `k`-th layer's path: the block's child `2`, then the spine's item `k` (Lean
 * `Path.layerPath`). */
const layerPath = (k: number): ReadonlyArray<number> => [2, ...Array<number>(k).fill(1), 0]

/** The block's module layers (Lean `moduleLayersOf`): the declarations whose paths stand in the
 * module, which must be `layerPath 0`, `1`, … in order. */
const moduleLayersOf = (ds: ReadonlyArray<readonly [ReadonlyArray<number>, LayerTerm]>): ReadonlyArray<LayerTerm> | undefined => {
  const ms = ds.filter(([p]) => inModulePath(p))
  return ms.every(([p], k) => refName(p) === refName(layerPath(k))) ? ms.map(([, l]) => l) : undefined
}

/** **A definition block** (Lean `readModule`'s block path): the headers, the services' roles, the
 * bodies at their parameters, the main program, the module's layers and the hoisted layers, put
 * back at their paths. */
const readBlock = (defDecls: ReadonlyArray<Declaration>, after: ReadonlyArray<Declaration>, main: Node): Read<Eff> => {
  const heads: Array<readonly [DefDecl, Node]> = []
  for (const c of defDecls) {
    const h = readDefHead(c)
    if (failed(h)) return again(h)
    heads.push(h.success)
  }
  const serviceEnd = after.findIndex((c) => readRefName(c.name) !== undefined || !isServiceConst(c.value))
  const serviceConsts = serviceEnd === -1 ? after : after.slice(0, serviceEnd)
  const layerConsts = serviceEnd === -1 ? [] : after.slice(serviceEnd)
  const services = readServices(serviceConsts)
  if (services === undefined) return refuse({ _tag: "shape", what: "service" })
  const decls: DefDecl[] = heads.map(([d]) => ({ ...d, role: roleOf(services, d.name) }))
  const defs = defEntries(decls)
  return withNamed(defs, decls, () => {
    const bodies: Eff[] = []
    const locals: Array<readonly [ReadonlyArray<number>, LayerTerm]> = []
    for (const [d, body] of heads) {
      const b = withNamed([...paramEntries(d.params), ...defs], decls, () => readDefBody(body))
      if (failed(b)) return again(b)
      bodies.push(b.success[0])
      locals.push(...b.success[1])
    }
    const program = readProgramExpr(main)
    if (failed(program)) return again(program)
    const ds: Array<readonly [ReadonlyArray<number>, LayerTerm]> = []
    for (const c of layerConsts) {
      const d = readLayerDecl(c)
      if (failed(d)) return again(d)
      ds.push(d.success)
    }
    const layers = moduleLayersOf(ds)
    if (layers === undefined) return refuse({ _tag: "shape", what: "module" })
    const whole = restoreAll({ _tag: "defs", decls, bodies, main: program.success, layers },
      [...locals, ...ds.filter(([p]) => !inModulePath(p))])
    return whole === undefined ? refuse({ _tag: "shape", what: "module" }) : ok(decodeEff(whole))
  })
}
