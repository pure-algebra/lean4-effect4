/**
 * Seat T (type-language probe, 2026-10-01): the form census.
 *
 * Counts TypeScript-level type forms, data-value forms, Effect types used as types, class kinds and
 * Effect module usage over a file set, by walking the syntax tree each file parses to under
 * oxc-parser 0.147.0, the ingest reader's second engine (`ts/eff/node_modules/oxc-parser`, read from
 * the main checkout by absolute path). Parse only: oxc is a parser, not a TypeScript compiler, so no
 * type is checked and no module is resolved; a count is a count of written syntax (comments and
 * string contents are not counted, unlike the data probe's regexes). The TypeScript 5.9.2 package is
 * never loaded (the owner's rule, restated 2026-10-01: tsgo 7 is the only TypeScript compiler; every
 * type check in this seat's folder is tsgo's).
 *
 * Usage:
 *   bun form_census.ts census <files.tsv>... > log      one report per set (TSV lines: set, project, path)
 *   bun form_census.ts check <file.ts> <expected.tsv>   exit 0 iff every expected count matches
 *
 * A category is counted per node; a file "has" a category when its count is nonzero; a project has
 * it when one of its files does. `effectFiles` counts the files that import from `effect` or
 * `@effect/*`. A file oxc reports errors for is counted as `parseErrors` and its tree still walked.
 */
import { parseSync } from "/Users/pooks/Dev/lean4-effect4/ts/eff/node_modules/oxc-parser/src-js/index.js"
import { readFileSync } from "node:fs"

/** Ordered categories: id and a one-line description. */
const CATEGORIES: ReadonlyArray<readonly [string, string]> = [
  // records written as TypeScript types
  ["T.interface", "interface declaration"],
  ["T.typeLiteral", "object type literal { ... }"],
  ["T.typeAlias.object", "type alias whose right side is an object type literal"],
  ["T.prop", "property signature (a field of an interface or type literal)"],
  ["T.prop.optional", "optional property signature a?: T"],
  ["T.prop.readonly", "readonly property signature"],
  ["T.prop.function", "function-typed field: property typed by a function type, or a method signature"],
  ["T.prop.quotedName", "property signature with a quoted or computed name"],
  ["T.indexSignature", "index signature [k: K]: V"],
  // sums
  ["T.union", "union type"],
  ["T.union.nullish", "union with an undefined or null member"],
  ["T.union.literals", "union whose members are all literal types"],
  ["T.union.tagged", "union of >= 2 object type literals each with a literal _tag field"],
  ["T.union.discriminated", "union of >= 2 object type literals sharing one literal-typed field (any name)"],
  ["T.typeLiteral.tagged", "object type literal with a literal-typed _tag field"],
  ["T.intersection", "intersection type A & B"],
  ["T.intersection.brand", "intersection with a Brand.Brand reference or a __brand/_brand field"],
  // sequences
  ["T.tuple", "tuple type [A, B]"],
  ["T.tuple.readonly", "readonly tuple type"],
  ["T.tuple.rest", "tuple type with a rest element"],
  ["T.tuple.optional", "tuple type with an optional element"],
  ["T.tuple.named", "tuple type with named members"],
  ["T.tuple.arity2", "tuple type with exactly 2 elements and no rest"],
  ["T.tuple.arity3plus", "tuple type with 3 or more elements and no rest"],
  ["T.tuple.arity01", "tuple type with 0 or 1 elements and no rest"],
  ["T.array", "array type T[]"],
  ["T.array.readonly", "readonly T[] or ReadonlyArray<T>"],
  ["T.array.ref", "Array<T> reference"],
  ["T.recordType.stringKey", "Record<K, V> with K = string (a keyed map)"],
  ["T.recordType.literalKeys", "Record<K, V> with K a literal or a union of literals (a fixed-key record)"],
  ["T.recordType.otherKey", "Record<K, V> with any other key type"],
  ["T.recordType.untypedValue", "Record<K, V> with V = unknown or any (an untyped bag)"],
  // scalars and keywords in type position
  ["T.kw.number", "number"],
  ["T.kw.string", "string"],
  ["T.kw.boolean", "boolean"],
  ["T.kw.bigint", "bigint"],
  ["T.kw.symbol", "symbol"],
  ["T.kw.uniqueSymbol", "unique symbol"],
  ["T.kw.undefined", "undefined (type)"],
  ["T.kw.null", "null (type)"],
  ["T.kw.void", "void (type)"],
  ["T.kw.never", "never"],
  ["T.kw.unknown", "unknown"],
  ["T.kw.any", "any"],
  ["T.kw.object", "object"],
  ["T.lit.string", "string literal type"],
  ["T.lit.number", "number literal type (signed included)"],
  ["T.lit.boolean", "true/false literal type"],
  ["T.lit.bigint", "bigint literal type"],
  ["T.templateLiteral", "template literal type `${...}`"],
  // type-level computation and signatures
  ["T.function", "function type (a => b) anywhere in a type"],
  ["T.generic.fn", "function-like declaration or signature with type parameters"],
  ["T.generic.type", "type alias, interface or class with type parameters"],
  ["T.typeParam.schema", "type parameter whose constraint mentions a Schema.* type"],
  ["T.param.schema", "value parameter typed Schema.<...>"],
  ["T.typeArgs.call", "explicit type arguments at a call or new"],
  ["T.typeof", "typeof query in a type"],
  ["T.typeof.schemaType", "typeof X.Type / X.Encoded (a type read off a schema)"],
  ["T.keyof", "keyof"],
  ["T.indexedAccess", "indexed access T[K]"],
  ["T.mapped", "mapped type"],
  ["T.conditional", "conditional type"],
  ["T.recursive", "interface or type alias that mentions its own name"],
  ["T.recursive.computed", "recursive, with a mapped or conditional type in its body (type-level computation)"],
  ["T.recursive.viaFunction", "recursive only through function types or method signatures (not data recursion)"],
  ["T.recursive.data", "recursive data: neither of the two above"],
  ["T.enum", "enum declaration"],
  ["T.moduleTypeRef", "type reference M.T to an Effect module type with no Ty constructor (NONCTOR_MODULES)"],
  ["T.moduleTypeRef.generic", "the same, with type arguments"],
  // classes
  ["C.class", "class declaration or expression"],
  ["C.dataTaggedError", "extends Data.TaggedError(...)"],
  ["C.dataError", "extends Data.Error"],
  ["C.schemaTaggedError", "extends Schema.TaggedError(Class)<...>"],
  ["C.schemaError", "extends Schema.Error(Class)<...>"],
  ["C.schemaClass", "extends Schema.Class / Schema.TaggedClass"],
  ["C.dataClass", "extends Data.Class / Data.TaggedClass"],
  ["C.service", "extends Context.Service/Tag/Reference, Effect.Service, ServiceMap.*"],
  ["C.jsError", "extends Error (or a JS error class)"],
  ["C.other", "any other class"],
  ["C.taggedError.nameIsTag", "tagged error class (Data or Schema) whose class name equals its tag"],
  ["C.taggedError.nameNotTag", "tagged error class whose class name differs from its tag"],
  ["C.taggedError.fields0", "tagged error class with no fields"],
  ["C.taggedError.messageOnly", "tagged error class whose only field is message"],
  ["C.taggedError.fieldsN", "tagged error class with fields other than message alone"],
  // value forms
  ["E.object", "object literal"],
  ["E.object.spread", "spread inside an object literal"],
  ["E.object.computedKey", "computed property name in an object literal"],
  ["E.array", "array literal"],
  ["E.number.fractional", "numeric literal with a fraction or exponent"],
  ["E.number.negative", "negated numeric literal -n"],
  ["E.bigint", "bigint literal 10n"],
  ["E.null", "null value"],
  ["E.undefined", "undefined value"],
  ["E.template", "template string with substitutions"],
  ["E.newDate", "new Date(...)"],
  ["E.dateNow", "Date.now()"],
  ["E.symbol", "Symbol(...) or Symbol.for(...)"],
  ["E.newMap", "new Map(...)"],
  ["E.newSet", "new Set(...)"],
  ["E.jsonParse", "JSON.parse"],
  ["E.jsonStringify", "JSON.stringify"],
  ["E.math", "Math.<member>"],
  ["E.durationString", "a duration string such as \"10 millis\""],
  ["E.instanceof", "instanceof"],
  ["E.typeofTest", "typeof x === / !== ..."],
  ["E.await", "await"],
  ["E.async", "async function"],
  ["E.newError", "new X(...) where X's name ends in Error"],
]
const IDS = new Set(CATEGORIES.map(([id]) => id))

/** Qualified Effect types counted as type references `M.T` (any T is also counted as `R.<M>`). */
const EFFECT_TYPE_MODULES = [
  "Effect", "Option", "Result", "Either", "Exit", "Cause", "Fiber", "Ref", "Deferred", "Scope", "Queue",
  "PubSub", "Stream", "Sink", "Channel", "Duration", "Chunk", "HashMap", "HashSet", "Layer", "Context",
  "Schedule", "Config", "Redacted", "DateTime", "Brand", "Schema", "Equal", "Data", "Mailbox",
  "Semaphore", "Latch", "Request", "Metric", "Logger", "Tracer", "Clock", "Random", "SubscriptionRef",
  "SynchronizedRef", "TxRef", "Cache", "Pool", "KeyValueStore", "FiberMap", "FiberSet", "FiberHandle",
  "RcMap", "RcRef", "ScopedCache", "BigDecimal", "Encoding", "Trie", "MutableHashMap", "MutableRef",
  "ServiceMap", "SchemaIssue", "Types", "Record", "Array", "Struct", "Predicate", "Match",
]
/** Effect modules whose types `Ty` spells today only as a rendered handle string or not at all (no constructor):
 * every `M.T` reference to one of them counts as `T.moduleTypeRef`. Option, Result, Exit, Cause, Fiber, Ref and
 * Deferred have constructors; Effect, Schema, Types, Data, Brand, Equal, Predicate, Match, Struct, Array, Record
 * are not data or service types and are left out. */
const NONCTOR_MODULES = [
  "Stream", "Layer", "Duration", "Redacted", "Scope", "Context", "Config", "DateTime", "Queue", "PubSub", "Schedule",
  "Sink", "Channel", "Semaphore", "Latch", "Cache", "ScopedCache", "Chunk", "HashMap", "HashSet", "Mailbox", "Pool",
  "Tracer", "Logger", "Metric", "Request", "SubscriptionRef", "SynchronizedRef", "TxRef", "FiberSet", "FiberMap",
  "FiberHandle", "RcMap", "RcRef", "KeyValueStore", "MutableHashMap", "MutableRef", "BigDecimal", "Clock", "Random",
  "ServiceMap", "Trie",
]
/** Bare (unqualified) type names counted as references. */
const BARE_TYPES = [
  "Date", "Map", "ReadonlyMap", "Set", "ReadonlySet", "Record", "Partial", "Readonly", "Required",
  "Pick", "Omit", "NonNullable", "ReturnType", "Parameters", "Promise", "Uint8Array", "ArrayBuffer",
  "ReadonlyArray", "Array", "Error", "URL", "Response", "Request", "Headers", "RegExp", "Iterable",
  "AsyncIterable", "Exclude", "Extract",
]
/** Modules whose value-level member accesses `M.x` are counted (expressions only). */
const VALUE_MODULES = new Set([
  ...EFFECT_TYPE_MODULES, "Console", "ConfigProvider", "HttpClient", "HttpClientRequest",
  "HttpClientResponse", "HttpServer", "HttpRouter", "HttpApi", "HttpApiBuilder", "HttpApiEndpoint",
  "HttpApiGroup", "Command", "Flag", "Argument", "Atom", "SqlClient", "Model", "Rpc", "RpcGroup",
  "Workflow", "Activity", "Persistence", "FileSystem", "Path", "Terminal", "ChildProcess",
  "Function", "Order", "Equivalence", "Hash", "Number", "String", "Boolean",
])

type Counts = Map<string, number>
type N = Record<string, any> & { type: string }
const bump = (c: Counts, k: string, n = 1) => c.set(k, (c.get(k) ?? 0) + n)
const isNode = (x: unknown): x is N => !!x && typeof x === "object" && typeof (x as N).type === "string"

const DURATION_RX =
  /^\s*\d+(\.\d+)?\s*(nanos?|micros?|millis?|seconds?|minutes?|hours?|days?|weeks?)\s*$/

function entityText(n: N | undefined): string {
  if (!n) return ""
  if (n.type === "Identifier") return n.name
  if (n.type === "TSQualifiedName") return entityText(n.left) + "." + entityText(n.right)
  if (n.type === "ThisExpression" || n.type === "TSThisType") return "this"
  return ""
}
const unwrap = (t: N | undefined): N | undefined => {
  while (t && t.type === "TSParenthesizedType") t = t.typeAnnotation
  return t
}
const annotation = (n: N | undefined): N | undefined => unwrap(n?.typeAnnotation?.typeAnnotation)
function keyName(k: N | undefined): string | undefined {
  if (!k) return undefined
  if (k.type === "Identifier") return k.name
  if (k.type === "Literal" && (typeof k.value === "string" || typeof k.value === "number")) return String(k.value)
  return undefined
}
const isBigIntLiteral = (n: N) =>
  n.type === "Literal" && (typeof n.value === "bigint" || "bigint" in n || /^[0-9][0-9_a-fA-FxXoObB]*n$/.test(String(n.raw ?? "")))
/** literal-typed property names of an object type literal */
function literalFields(t: N): Set<string> {
  const out = new Set<string>()
  for (const m of t.members ?? [])
    if (m.type === "TSPropertySignature" && annotation(m)?.type === "TSLiteralType") {
      const name = keyName(m.key)
      if (name !== undefined) out.add(name)
    }
  return out
}
/** Self-references to `name` under `root`, each marked by whether a function type or method encloses it. */
function selfRefs(root: N | undefined, name: string): boolean[] {
  const out: boolean[] = []
  const go = (x: unknown, underFn: boolean) => {
    if (Array.isArray(x)) { for (const y of x) go(y, underFn); return }
    if (!isNode(x)) return
    if (x.type === "TSTypeReference" && entityText(x.typeName).split(".").pop() === name) out.push(underFn)
    const fn = underFn || x.type === "TSFunctionType" || x.type === "TSMethodSignature" || x.type === "TSConstructorType" ||
      x.type === "TSCallSignatureDeclaration" || x.type === "TSConstructSignatureDeclaration"
    for (const k in x) if (k !== "start" && k !== "end") go(x[k], fn)
  }
  go(root, false)
  return out
}
function recursion(c: Counts, root: N | undefined, name: string | undefined) {
  if (!name) return
  const refs = selfRefs(root, name)
  if (refs.length === 0) return
  bump(c, "T.recursive")
  if (some(root, (n) => n.type === "TSMappedType" || n.type === "TSConditionalType")) bump(c, "T.recursive.computed")
  else if (refs.every((u) => u)) bump(c, "T.recursive.viaFunction")
  else bump(c, "T.recursive.data")
}

function some(root: N | undefined, pred: (n: N) => boolean): boolean {
  let found = false
  const go = (x: unknown) => {
    if (found) return
    if (Array.isArray(x)) { for (const y of x) go(y); return }
    if (!isNode(x)) return
    if (pred(x)) { found = true; return }
    for (const k in x) if (k !== "start" && k !== "end") go(x[k])
  }
  go(root)
  return found
}
const schemaRef = (n: N) => n.type === "TSTypeReference" && entityText(n.typeName).startsWith("Schema.")
/** Innermost head of a heritage expression: `Data.TaggedError` for `Data.TaggedError("X")`, and for
 * `Schema.TaggedError<X>()("X", {...})`. */
function heritageHead(e: N | undefined): string {
  while (e && (e.type === "CallExpression" || e.type === "TSInstantiationExpression")) e = e.callee ?? e.expression
  if (!e) return ""
  if (e.type === "Identifier") return e.name
  if (e.type === "MemberExpression" && !e.computed && e.object?.type === "Identifier" && e.property?.type === "Identifier")
    return e.object.name + "." + e.property.name
  return ""
}
function classify(head: string): string {
  if (head === "Data.TaggedError") return "C.dataTaggedError"
  if (head === "Data.Error") return "C.dataError"
  if (head === "Schema.TaggedError" || head === "Schema.TaggedErrorClass") return "C.schemaTaggedError"
  if (head === "Schema.Error" || head === "Schema.ErrorClass") return "C.schemaError"
  if (head === "Schema.Class" || head === "Schema.TaggedClass") return "C.schemaClass"
  if (head === "Data.Class" || head === "Data.TaggedClass") return "C.dataClass"
  if (/^(Context\.(Service|Tag|Reference|Key)|Effect\.Service|ServiceMap\.(Service|Key|Reference))$/.test(head)) return "C.service"
  if (/^(Error|TypeError|RangeError|SyntaxError)$/.test(head)) return "C.jsError"
  return "C.other"
}
/** The outermost call of a heritage expression (`Data.TaggedError("X")`; for
 * `Schema.TaggedError<S>()("X", {...})` the call carrying the tag). */
const outerCall = (e: N | undefined): N | undefined => (e?.type === "CallExpression" ? e : undefined)
const firstString = (call: N | undefined): string | undefined => {
  const a = call?.arguments?.[0]
  return a?.type === "Literal" && typeof a.value === "string" ? a.value : undefined
}
/** Kind of a payload field's type (Data form: a TS type; Schema form: a Schema.<X> expression). */
function fieldKindTs(t: N | undefined): string {
  t = unwrap(t)
  if (!t) return "none"
  switch (t.type) {
    case "TSStringKeyword": return "string"
    case "TSNumberKeyword": return "number"
    case "TSBooleanKeyword": return "boolean"
    case "TSUnknownKeyword": return "unknown"
    case "TSAnyKeyword": return "any"
    case "TSLiteralType": return "literal"
    case "TSUnionType": return "union"
    case "TSArrayType": return "array"
    case "TSTypeLiteral": return "record"
    case "TSFunctionType": return "function"
    case "TSTypeReference": {
      const name = entityText(t.typeName)
      if (/^(ReadonlyArray|Array)$/.test(name)) return "array"
      if (/^(Error|.*Error)$/.test(name)) return "error-reference"
      if (/^Option\.Option$/.test(name)) return "option"
      return "other-reference"
    }
    default: return "other"
  }
}
function fieldKindSchema(v: N | undefined): string {
  if (!v) return "none"
  if (v.type === "MemberExpression" && v.object?.type === "Identifier" && v.object.name === "Schema" && v.property?.type === "Identifier") {
    const m: string = v.property.name
    if (m === "String" || m === "NonEmptyString") return "string"
    if (m === "Number" || m === "Int" || m === "Finite") return "number"
    if (m === "Boolean") return "boolean"
    if (m === "Unknown" || m === "Any") return "unknown"
    if (m === "Defect") return "defect"
    return "other-schema"
  }
  if (v.type === "CallExpression") {
    const h = heritageHead(v)
    if (/^Schema\.(optional|optionalKey|NullOr|UndefinedOr|NullishOr)$/.test(h)) return "optional-or-nullable"
    if (/^Schema\.(Literal|Literals)$/.test(h)) return "literal"
    if (/^Schema\.(Array|NonEmptyArray)$/.test(h)) return "array"
    if (/^Schema\.(Struct|Record)$/.test(h)) return "record"
    return "other-schema"
  }
  return "other"
}

const FUNCTION_LIKE = new Set([
  "FunctionDeclaration", "FunctionExpression", "ArrowFunctionExpression", "TSDeclareFunction",
  "TSMethodSignature", "TSFunctionType", "TSCallSignatureDeclaration", "TSConstructSignatureDeclaration",
  "TSConstructorType",
])

export function countText(path: string, text: string): {
  counts: Counts; effectImport: boolean; imports: Set<string>; errors: number
} {
  const lang = path.endsWith(".tsx") ? "tsx" : "ts"
  const parsed = parseSync(path, text, { lang, sourceType: "module" })
  const c: Counts = new Map()
  const imports = new Set<string>()
  let effectImport = false

  const visit = (n: N, parent: N | undefined): void => {
    const pt = parent?.type
    switch (n.type) {
      case "ImportDeclaration": {
        const spec = String(n.source?.value ?? "")
        if (/^(effect($|\/)|@effect\/)/.test(spec)) {
          effectImport = true
          for (const s of n.specifiers ?? []) {
            if (s.type === "ImportSpecifier") imports.add(keyName(s.imported) ?? s.local?.name)
            else if (s.local?.name) imports.add(s.local.name)
          }
        }
        break
      }
      case "TSInterfaceDeclaration":
        bump(c, "T.interface")
        if (n.typeParameters) bump(c, "T.generic.type")
        recursion(c, n.body, n.id?.name)
        break
      case "TSTypeAliasDeclaration":
        if (unwrap(n.typeAnnotation)?.type === "TSTypeLiteral") bump(c, "T.typeAlias.object")
        if (n.typeParameters) bump(c, "T.generic.type")
        recursion(c, n.typeAnnotation, n.id?.name)
        break
      case "TSTypeLiteral":
        bump(c, "T.typeLiteral")
        if (literalFields(n).has("_tag")) bump(c, "T.typeLiteral.tagged")
        break
      case "TSPropertySignature":
        bump(c, "T.prop")
        if (n.optional) bump(c, "T.prop.optional")
        if (n.readonly) bump(c, "T.prop.readonly")
        if (annotation(n)?.type === "TSFunctionType") bump(c, "T.prop.function")
        if (n.computed || n.key?.type === "Literal") bump(c, "T.prop.quotedName")
        break
      case "TSMethodSignature":
        bump(c, "T.prop.function")
        break
      case "TSIndexSignature":
        bump(c, "T.indexSignature")
        break
      case "TSUnionType": {
        const ms: N[] = (n.types ?? []).map(unwrap)
        bump(c, "T.union")
        if (ms.some((m) => m.type === "TSUndefinedKeyword" || m.type === "TSNullKeyword")) bump(c, "T.union.nullish")
        if (ms.length > 0 && ms.every((m) => m.type === "TSLiteralType")) bump(c, "T.union.literals")
        if (ms.length >= 2 && ms.every((m) => m.type === "TSTypeLiteral")) {
          const sets = ms.map(literalFields)
          if (sets.every((s) => s.has("_tag"))) bump(c, "T.union.tagged")
          if ([...sets[0]!].some((k) => sets.every((s) => s.has(k)))) bump(c, "T.union.discriminated")
        }
        break
      }
      case "TSIntersectionType":
        bump(c, "T.intersection")
        if ((n.types ?? []).map(unwrap).some((m: N) =>
          (m.type === "TSTypeReference" && /^(Brand\.Brand|Brand\.Branded)$/.test(entityText(m.typeName))) ||
          (m.type === "TSTypeLiteral" && (m.members ?? []).some((p: N) => /^_{1,2}brand$/.test(keyName(p.key) ?? "")))))
          bump(c, "T.intersection.brand")
        break
      case "TSTupleType": {
        const els: N[] = n.elementTypes ?? []
        bump(c, "T.tuple")
        if (pt === "TSTypeOperator" && parent!.operator === "readonly") bump(c, "T.tuple.readonly")
        if (els.some((e) => e.type === "TSRestType")) bump(c, "T.tuple.rest")
        if (els.some((e) => e.type === "TSOptionalType" || (e.type === "TSNamedTupleMember" && e.optional))) bump(c, "T.tuple.optional")
        if (els.some((e) => e.type === "TSNamedTupleMember" || (e.type === "TSRestType" && e.typeAnnotation?.type === "TSNamedTupleMember")))
          bump(c, "T.tuple.named")
        if (!els.some((e) => e.type === "TSRestType")) bump(c, els.length === 2 ? "T.tuple.arity2" : els.length >= 3 ? "T.tuple.arity3plus" : "T.tuple.arity01")
        break
      }
      case "TSArrayType":
        bump(c, "T.array")
        if (pt === "TSTypeOperator" && parent!.operator === "readonly") bump(c, "T.array.readonly")
        break
      case "TSTypeOperator":
        if (n.operator === "unique") bump(c, "T.kw.uniqueSymbol")
        if (n.operator === "keyof") bump(c, "T.keyof")
        break
      case "TSNumberKeyword": bump(c, "T.kw.number"); break
      case "TSStringKeyword": bump(c, "T.kw.string"); break
      case "TSBooleanKeyword": bump(c, "T.kw.boolean"); break
      case "TSBigIntKeyword": bump(c, "T.kw.bigint"); break
      case "TSSymbolKeyword": bump(c, "T.kw.symbol"); break
      case "TSUndefinedKeyword": bump(c, "T.kw.undefined"); break
      case "TSNullKeyword": bump(c, "T.kw.null"); break
      case "TSVoidKeyword": bump(c, "T.kw.void"); break
      case "TSNeverKeyword": bump(c, "T.kw.never"); break
      case "TSUnknownKeyword": bump(c, "T.kw.unknown"); break
      case "TSAnyKeyword": bump(c, "T.kw.any"); break
      case "TSObjectKeyword": bump(c, "T.kw.object"); break
      case "TSLiteralType": {
        const l: N = n.literal
        if (l.type === "UnaryExpression") bump(c, "T.lit.number")
        else if (l.type === "TemplateLiteral") bump(c, "T.lit.string")
        else if (isBigIntLiteral(l)) bump(c, "T.lit.bigint")
        else if (typeof l.value === "string") bump(c, "T.lit.string")
        else if (typeof l.value === "number") bump(c, "T.lit.number")
        else if (typeof l.value === "boolean") bump(c, "T.lit.boolean")
        break
      }
      case "TSTemplateLiteralType": bump(c, "T.templateLiteral"); break
      case "TSFunctionType": bump(c, "T.function"); break
      case "TSTypeQuery": {
        bump(c, "T.typeof")
        if (/\.(Type|Encoded)$/.test(entityText(n.exprName))) bump(c, "T.typeof.schemaType")
        break
      }
      case "TSIndexedAccessType": bump(c, "T.indexedAccess"); break
      case "TSMappedType": bump(c, "T.mapped"); break
      case "TSConditionalType": bump(c, "T.conditional"); break
      case "TSEnumDeclaration": bump(c, "T.enum"); break
      case "TSTypeParameter":
        if (some(n.constraint, schemaRef)) bump(c, "T.typeParam.schema")
        break
      case "TSTypeReference": {
        const name = entityText(n.typeName)
        const parts = name.split(".")
        if (parts.length >= 2 && NONCTOR_MODULES.includes(parts[0]!)) {
          bump(c, "T.moduleTypeRef")
          if ((n.typeArguments?.params ?? []).length > 0) bump(c, "T.moduleTypeRef.generic")
        }
        if (parts.length >= 2 && EFFECT_TYPE_MODULES.includes(parts[0]!)) {
          bump(c, "R." + parts[0])
          bump(c, "R." + parts.slice(0, 2).join("."))
        } else if (parts.length === 1 && BARE_TYPES.includes(name)) {
          bump(c, "B." + name)
          if (name === "ReadonlyArray") bump(c, "T.array.readonly")
          if (name === "Record") {
            const [k, v] = ((n.typeArguments?.params ?? []) as N[]).map(unwrap)
            const literalKey = (t: N | undefined): boolean => !!t && (t.type === "TSLiteralType" ||
              (t.type === "TSUnionType" && (t.types ?? []).map(unwrap).every((m: N) => m.type === "TSLiteralType")))
            bump(c, k?.type === "TSStringKeyword" ? "T.recordType.stringKey" : literalKey(k) ? "T.recordType.literalKeys" : "T.recordType.otherKey")
            if (v?.type === "TSUnknownKeyword" || v?.type === "TSAnyKeyword") bump(c, "T.recordType.untypedValue")
          }
          if (name === "Array") bump(c, "T.array.ref")
        }
        break
      }
      case "ClassDeclaration":
      case "ClassExpression":
        bump(c, "C.class")
        if (n.typeParameters) bump(c, "T.generic.type")
        {
          const kind = n.superClass ? classify(heritageHead(n.superClass)) : "C.other"
          bump(c, kind)
          if (kind === "C.dataTaggedError" || kind === "C.schemaTaggedError") {
            const call = outerCall(n.superClass)
            const tag = firstString(call)
            if (tag !== undefined && n.id?.name !== undefined) bump(c, tag === n.id.name ? "C.taggedError.nameIsTag" : "C.taggedError.nameNotTag")
            let names: string[] = []
            if (kind === "C.dataTaggedError") {
              const lit = unwrap(n.superTypeArguments?.params?.[0])
              const members: N[] = lit?.type === "TSTypeLiteral" ? lit.members ?? [] : []
              names = members.map((m) => keyName(m.key) ?? "?")
              for (const m of members) bump(c, "P.data." + (m.type === "TSPropertySignature" ? fieldKindTs(m.typeAnnotation?.typeAnnotation) : "method"))
            } else {
              const obj = call?.arguments?.[1]
              const props: N[] = obj?.type === "ObjectExpression" ? obj.properties ?? [] : []
              names = props.map((p) => keyName(p.key) ?? "?")
              for (const p of props) bump(c, "P.schema." + (p.type === "Property" ? fieldKindSchema(p.value) : "spread"))
            }
            if (names.length === 0) bump(c, "C.taggedError.fields0")
            else if (names.length === 1 && names[0] === "message") bump(c, "C.taggedError.messageOnly")
            else bump(c, "C.taggedError.fieldsN")
          }
        }
        break
      case "CallExpression":
      case "NewExpression": {
        if (n.typeArguments) bump(c, "T.typeArgs.call")
        const callee: N = n.callee
        const name = callee?.type === "Identifier" ? callee.name
          : callee?.type === "MemberExpression" && callee.object?.type === "Identifier" && callee.property?.type === "Identifier"
            ? callee.object.name + "." + callee.property.name : ""
        if (n.type === "NewExpression") {
          if (name === "Date") bump(c, "E.newDate")
          if (name === "Map") bump(c, "E.newMap")
          if (name === "Set") bump(c, "E.newSet")
          if (/Error$/.test(name)) bump(c, "E.newError")
        } else {
          if (name === "Date.now") bump(c, "E.dateNow")
          if (name === "Symbol" || name === "Symbol.for") bump(c, "E.symbol")
        }
        break
      }
      case "ObjectExpression":
        bump(c, "E.object")
        for (const p of n.properties ?? []) {
          if (p.type === "SpreadElement") bump(c, "E.object.spread")
          if (p.type === "Property" && p.computed) bump(c, "E.object.computedKey")
        }
        break
      case "ArrayExpression": bump(c, "E.array"); break
      case "Literal":
        if (pt === "TSLiteralType") break
        if (isBigIntLiteral(n)) bump(c, "E.bigint")
        else if (typeof n.value === "number") {
          const raw = String(n.raw ?? "")
          if (!/^0[xXbBoO]/.test(raw) && /[.eE]/.test(raw) && !(pt === "UnaryExpression" && parent!.operator === "-"))
            bump(c, "E.number.fractional")
        } else if (n.value === null && n.raw === "null") bump(c, "E.null")
        else if (typeof n.value === "string" && DURATION_RX.test(n.value)) bump(c, "E.durationString")
        break
      case "UnaryExpression":
        if (n.operator === "-" && n.argument?.type === "Literal" && typeof n.argument.value === "number" && pt !== "TSLiteralType") {
          bump(c, "E.number.negative")
          const raw = String(n.argument.raw ?? "")
          if (!/^0[xXbBoO]/.test(raw) && /[.eE]/.test(raw)) bump(c, "E.number.fractional")
        }
        break
      case "Identifier":
        if (n.name === "undefined" && pt !== "TSQualifiedName" && pt !== "TSTypeReference" &&
          !(pt === "MemberExpression" && parent!.property === n) && !(pt === "Property" && parent!.key === n))
          bump(c, "E.undefined")
        break
      case "TemplateLiteral":
        if (pt !== "TSLiteralType" && (n.expressions ?? []).length > 0) bump(c, "E.template")
        break
      case "BinaryExpression":
        if (n.operator === "instanceof") bump(c, "E.instanceof")
        if ((n.operator === "===" || n.operator === "!==") &&
          ((n.left?.type === "UnaryExpression" && n.left.operator === "typeof") ||
            (n.right?.type === "UnaryExpression" && n.right.operator === "typeof"))) bump(c, "E.typeofTest")
        break
      case "AwaitExpression": bump(c, "E.await"); break
      case "MemberExpression":
        if (!n.computed && n.object?.type === "Identifier" && n.property?.type === "Identifier") {
          const m: string = n.object.name, member: string = n.property.name
          if (m === "JSON" && member === "parse") bump(c, "E.jsonParse")
          if (m === "JSON" && member === "stringify") bump(c, "E.jsonStringify")
          if (m === "Math") bump(c, "E.math")
          if (VALUE_MODULES.has(m)) { bump(c, "M." + m); bump(c, "M." + m + "." + member) }
        }
        break
    }
    if (FUNCTION_LIKE.has(n.type)) {
      if (n.typeParameters) bump(c, "T.generic.fn")
      if (n.async) bump(c, "E.async")
      for (const p of n.params ?? []) {
        const t = annotation(p.type === "TSParameterProperty" ? p.parameter : p.type === "AssignmentPattern" ? p.left : p)
        if (t && schemaRef(t)) bump(c, "T.param.schema")
      }
    }
    for (const k in n) {
      if (k === "start" || k === "end" || k === "type") continue
      const v = n[k]
      if (Array.isArray(v)) { for (const x of v) if (isNode(x)) visit(x, n) }
      else if (isNode(v)) visit(v, n)
    }
  }
  visit(parsed.program as N, undefined)
  return { counts: c, effectImport, imports, errors: parsed.errors.length }
}

type Row = { set: string; project: string; path: string }

function readList(file: string): Row[] {
  return readFileSync(file, "utf8").split("\n").filter((l) => l.length > 0).map((l) => {
    const [set, project, path] = l.split("\t")
    return { set: set!, project: project!, path: path! }
  })
}

const SELECTED = ["T.interface", "T.typeLiteral", "T.prop.optional", "T.prop.function", "T.indexSignature",
  "T.union.nullish", "T.union.tagged", "T.intersection", "T.tuple.rest", "T.templateLiteral", "T.kw.bigint",
  "B.Date", "T.generic.fn", "T.recursive", "T.enum", "C.dataTaggedError", "C.schemaTaggedError", "C.schemaClass",
  "C.service", "E.number.fractional", "E.number.negative", "R.Option", "R.Stream", "R.Queue", "R.Layer",
  "R.Schedule", "R.Config", "C.taggedError.nameNotTag", "C.taggedError.fieldsN", "C.taggedError.fields0",
  "C.taggedError.messageOnly", "P.data.unknown", "B.Record", "B.ReadonlyMap", "T.typeAlias.object", "T.union.literals",
  "T.kw.null", "T.kw.undefined", "R.Duration", "R.Redacted", "B.Uint8Array", "E.number.negative", "E.newDate", "T.tuple"]

function report(set: string, rows: Row[]) {
  const occ: Counts = new Map(), files: Counts = new Map(), effFiles: Counts = new Map()
  const projects = new Map<string, Set<string>>()
  const perProject = new Map<string, Counts>()
  const importFiles: Counts = new Map(), importProjects = new Map<string, Set<string>>()
  let effectFileCount = 0, unreadable = 0, parseErrorFiles = 0
  const perFile: Array<[string, Counts]> = []
  for (const r of rows) {
    let text: string
    try { text = readFileSync(r.path, "utf8") } catch { unreadable++; continue }
    const { counts, effectImport, imports, errors } = countText(r.path, text)
    if (errors > 0) parseErrorFiles++
    if (effectImport) effectFileCount++
    if (set === "probe" || set === "dogfood") perFile.push([r.path, counts])
    const pp = perProject.get(r.project) ?? new Map(); perProject.set(r.project, pp)
    for (const [k, v] of counts) {
      bump(occ, k, v); bump(files, k)
      if (effectImport) bump(effFiles, k)
      const s = projects.get(k) ?? new Set(); s.add(r.project); projects.set(k, s)
      bump(pp, k, v)
    }
    for (const name of imports) {
      bump(importFiles, name)
      const s = importProjects.get(name) ?? new Set(); s.add(r.project); importProjects.set(name, s)
    }
  }
  const projectCount = new Set(rows.map((r) => r.project)).size
  console.log(`## ${set}: ${rows.length} files (${unreadable} unreadable, ${parseErrorFiles} with oxc parse errors), ` +
    `${projectCount} projects, ${effectFileCount} files import effect or @effect/*`)
  if (perFile.length > 0) {
    console.log(`### ${set}: per file, nonzero categories (T., C., E. only)`)
    for (const [p, cs] of perFile) {
      const nz = [...cs].filter(([k]) => IDS.has(k)).map(([k, v]) => `${k}=${v}`).join(" ")
      console.log(`- ${p.replace(/^.*\/docs\/research\//, "")}: ${nz}`)
    }
  }
  console.log(`### ${set}: categories`)
  console.log(["category", "occurrences", "files", "projects", "effectFiles", "description"].join("\t"))
  for (const [id, desc] of CATEGORIES)
    console.log([id, occ.get(id) ?? 0, files.get(id) ?? 0, projects.get(id)?.size ?? 0, effFiles.get(id) ?? 0, desc].join("\t"))
  const table = (title: string, keys: string[]) => {
    console.log(title)
    console.log(["key", "occurrences", "files", "projects", "effectFiles"].join("\t"))
    for (const k of keys.sort((a, b) => (occ.get(b)! - occ.get(a)!) || a.localeCompare(b)))
      console.log([k, occ.get(k), files.get(k), projects.get(k)?.size ?? 0, effFiles.get(k) ?? 0].join("\t"))
  }
  table(`### ${set}: Effect types as types (R.<Module> any member; R.<Module>.<Type>)`, [...occ.keys()].filter((k) => k.startsWith("R.")))
  table(`### ${set}: tagged error payload field kinds (P.data.<kind>: Data.TaggedError TS field types; P.schema.<kind>: Schema.TaggedError field schemas)`,
    [...occ.keys()].filter((k) => k.startsWith("P.")))
  table(`### ${set}: bare type references`, [...occ.keys()].filter((k) => k.startsWith("B.")))
  table(`### ${set}: module member accesses in expressions (M.<Module> total)`, [...occ.keys()].filter((k) => /^M\.[^.]+$/.test(k)))
  table(`### ${set}: module members (M.<Module>.<member>), occurrences >= 3`,
    [...occ.keys()].filter((k) => /^M\.[^.]+\.[^.]+$/.test(k) && (occ.get(k) ?? 0) >= 3))
  console.log(`### ${set}: names imported from effect or @effect/* (files, projects)`)
  console.log(["name", "files", "projects"].join("\t"))
  for (const k of [...importFiles.keys()].sort((a, b) => (importFiles.get(b)! - importFiles.get(a)!) || a.localeCompare(b)))
    console.log([k, importFiles.get(k), importProjects.get(k)?.size ?? 0].join("\t"))
  if (rows.length > 20) {
    console.log(`### ${set}: per project (occurrences), selected categories`)
    console.log(["project", ...SELECTED].join("\t"))
    for (const [p, cs] of [...perProject].sort((a, b) => a[0].localeCompare(b[0])))
      console.log([p, ...SELECTED.map((k) => cs.get(k) ?? 0)].join("\t"))
  }
  console.log()
}

function check(file: string, expected: string): number {
  const { counts, errors } = countText(file, readFileSync(file, "utf8"))
  let bad = errors === 0 ? 0 : 1
  if (errors) console.log(`FAIL oxc reported ${errors} parse errors`)
  for (const line of readFileSync(expected, "utf8").split("\n")) {
    if (line.length === 0 || line.startsWith("#")) continue
    const [id, want] = line.split("\t")
    const got = counts.get(id!) ?? 0
    const ok = got === Number(want)
    if (!ok) bad++
    console.log(`${ok ? "ok  " : "FAIL"} ${id} expected ${want} got ${got}`)
  }
  console.log(bad === 0 ? "ALL OK" : `${bad} MISMATCH(ES)`)
  return bad === 0 ? 0 : 1
}

const [mode, ...args] = process.argv.slice(2)
if (mode === "census") {
  console.log(`# form census over oxc-parser 0.147.0 trees (syntax only; bun ${Bun.version}), ${new Date().toISOString()}`)
  for (const list of args) {
    const rows = readList(list)
    report(rows[0]?.set ?? list, rows)
  }
} else if (mode === "check") {
  process.exit(check(args[0]!, args[1]!))
} else {
  console.error("usage: bun form_census.ts census <files.tsv>... | check <file.ts> <expected.tsv>")
  process.exit(2)
}
