/**
 * Seat EFFECT, data probe (2026-10-01): rc.112 Schema behaviours the note relies on, run under
 * bun 1.4.2 against the pinned effect@4.0.0-rc.112 (ts/eff/node_modules, by absolute path).
 * Each line prints `T<n> <label>: <observed>` and `expect=<expected>`; the run fails (exit 1)
 * if any observation differs from its expectation.
 */
import {
  Data, Effect, Exit, Schema, SchemaIssue
} from "/Users/pooks/Dev/lean4-effect4/ts/eff/node_modules/effect/dist/index.js"

let failures = 0
const show = (v: unknown): string => {
  try {
    return JSON.stringify(v, (_k, x) => (typeof x === "number" && !Number.isFinite(x) ? `#${x}` : x === undefined ? "#undefined" : x))
  } catch (e) {
    return `<unprintable ${String(e)}>`
  }
}
const check = (id: string, label: string, observed: unknown, expected: unknown) => {
  const o = show(observed), e = show(expected)
  const ok = o === e
  if (!ok) failures++
  console.log(`${id} ${label}: ${o}  expect=${e}  ${ok ? "ok" : "MISMATCH"}`)
}
const attempt = <A>(f: () => A): { ok: A } | { error: string } => {
  try { return { ok: f() } } catch (e) {
    const err = e as any
    return { error: `${err?._tag ?? err?.name ?? "Error"}: ${err?.message ?? String(err)}` }
  }
}

const User = Schema.Struct({ id: Schema.Number, name: Schema.String })

// T1 excess keys are dropped by default (onExcessProperty "ignore", SchemaAST.ts:459-551)
check("T1", "excess key dropped", Schema.decodeUnknownSync(User)({ id: 1, name: "a", extra: true }), { id: 1, name: "a" })
// T2 the output's key order is the declaration's, not the input's
check("T2", "output key order", Object.keys(Schema.decodeUnknownSync(User)({ name: "a", id: 1 })), ["id", "name"])
// T3 a missing required key fails with SchemaError; the message is the default formatter's
check("T3", "missing key", attempt(() => Schema.decodeUnknownSync(User)({ id: 1 })), { error: "SchemaError: Missing key\n  at [\"name\"]" })
// T4 a wrong type
check("T4", "wrong type", attempt(() => Schema.decodeUnknownSync(User)({ id: "1", name: "a" })), { error: "SchemaError: Expected number\n  at [\"id\"]" })
// T4b the input enters the message only under `reportInput: true` (SchemaAST.ts:520-547)
check("T4b", "wrong type, reportInput", attempt(() => Schema.decodeUnknownSync(User)({ id: "1", name: "a" }, { reportInput: true })), { error: "SchemaError: Expected number, got \"1\"\n  at [\"id\"]" })
// T5 Schema.Number admits what `Ty.nat` refuses
check("T5", "Number admits 1.5, -1, NaN, Infinity",
  [1.5, -1, NaN, Infinity].map((n) => attempt(() => Schema.decodeUnknownSync(Schema.Number)(n))),
  [{ ok: 1.5 }, { ok: -1 }, { ok: NaN }, { ok: Infinity }])
// T6 the JSON codec writes non-finite numbers as strings (SchemaAST.ts:1427-1475)
check("T6", "toCodecJson(Number) of NaN, Infinity, 2",
  [NaN, Infinity, 2].map((n) => Schema.encodeSync(Schema.toCodecJson(Schema.Number))(n)), ["NaN", "Infinity", 2])
// T7 JSON text with a duplicate key: JSON.parse keeps the last, and fromJsonString sees only that
check("T7", "duplicate key, last wins", Schema.decodeUnknownSync(Schema.fromJsonString(User))('{"id":1,"id":2,"name":"a"}'), { id: 2, name: "a" })
// T8 an anyOf union answers its first succeeding member, which strips the other member's keys
const AB = Schema.Union([Schema.Struct({ a: Schema.Number }), Schema.Struct({ a: Schema.Number, b: Schema.String })])
check("T8", "anyOf first match strips b", Schema.decodeUnknownSync(AB)({ a: 1, b: "x" }), { a: 1 })
// T9 a tagged union selects by the `_tag` sentinel instead
const Entry = Schema.Union([
  Schema.TaggedStruct("Deposit", { amount: Schema.Number }),
  Schema.TaggedStruct("Withdraw", { amount: Schema.Number })
])
check("T9", "tagged union by sentinel", Schema.decodeUnknownSync(Entry)({ _tag: "Withdraw", amount: 3 }), { _tag: "Withdraw", amount: 3 })
// T10 a pure schema's decode effect is already an Exit: no fiber is needed to run it
const eff = Schema.decodeUnknownEffect(User)({ id: 1, name: "a" })
check("T10", "decodeUnknownEffect of a pure schema is an Exit", Exit.isExit(eff), true)
// T11 Schema.TaggedError: decoding builds the class instance, encoding gives the plain struct
class NotFound extends Schema.TaggedError<NotFound>()("NotFound", { id: Schema.Number }) {}
const nf = Schema.decodeUnknownSync(NotFound)({ _tag: "NotFound", id: 7 })
check("T11a", "decoded TaggedError is an instance", [nf instanceof NotFound, nf instanceof Error, nf._tag, nf.id], [true, true, "NotFound", 7])
check("T11b", "encoded TaggedError is the struct", Schema.encodeSync(NotFound)(new NotFound({ id: 7 })), { _tag: "NotFound", id: 7 })
check("T11c", "a plain object is not a NotFound at encode", attempt(() => Schema.encodeSync(NotFound)({ _tag: "NotFound", id: 7 } as any)).hasOwnProperty("error"), true)
// T12 optionalKey refuses an explicit undefined; optional admits it; both admit absence
const K = Schema.Struct({ a: Schema.optionalKey(Schema.String) })
const O = Schema.Struct({ a: Schema.optional(Schema.String) })
check("T12", "optionalKey vs optional",
  [attempt(() => Schema.decodeUnknownSync(K)({})), attempt(() => Schema.decodeUnknownSync(K)({ a: undefined })).hasOwnProperty("error"),
   attempt(() => Schema.decodeUnknownSync(O)({ a: undefined }))],
  [{ ok: {} }, true, { ok: { a: undefined } }])
// T13 a record with string keys
check("T13", "Record(String, Number)", Schema.decodeUnknownSync(Schema.Record(Schema.String, Schema.Number))({ x: 1, y: 2 }), { x: 1, y: 2 })
// T14 recursion through suspend
interface Tree { readonly value: number; readonly children: ReadonlyArray<Tree> }
const Tree: Schema.Codec<Tree> = Schema.Struct({ value: Schema.Number, children: Schema.Array(Schema.suspend((): Schema.Codec<Tree> => Tree)) })
check("T14", "suspend", Schema.decodeUnknownSync(Tree)({ value: 1, children: [{ value: 2, children: [] }] }), { value: 1, children: [{ value: 2, children: [] }] })
// T15 a decoding default supplies a missing key
const D = Schema.Struct({ n: Schema.Number.pipe(Schema.withDecodingDefaultKey(Effect.succeed(5))) })
check("T15", "withDecodingDefaultKey", Schema.decodeUnknownSync(D)({}), { n: 5 })
// T16 the issue tree, and its flat Standard Schema projection (message and path per leaf)
const Outer = Schema.Struct({ user: User, tags: Schema.Array(Schema.String) })
const failed = Schema.decodeUnknownExit(Outer)({ user: { id: "x" }, tags: [1] }, { errors: "all" })
const issue = Exit.isFailure(failed) ? (failed.cause.reasons[0] as any).error.issue : undefined
const tags = (i: any): unknown => i === undefined ? null : i._tag === "Pointer" ? { Pointer: i.path, issue: tags(i.issue) }
  : i._tag === "Composite" || i._tag === "AnyOf" ? { [i._tag]: i.issues.map(tags) } : i._tag
check("T16a", "issue tree under errors: all", tags(issue),
  { Composite: [{ Pointer: ["user"], issue: { Composite: [{ Pointer: ["id"], issue: "InvalidType" }, { Pointer: ["name"], issue: "MissingKey" }] } },
                { Pointer: ["tags"], issue: { Composite: [{ Pointer: [0], issue: "InvalidType" }] } }] })
const flat = SchemaIssue.makeFormatterStandardSchemaV1()(issue)
check("T16b", "Standard Schema projection", flat.issues.map((x: any) => [x.message, x.path]),
  [["Expected number", ["user", "id"]], ["Missing key", ["user", "name"]], ["Expected string", ["tags", 0]]])
// T17 Data.TaggedError: no schema; JSON.stringify keeps the fields and the tag
class HttpError extends Data.TaggedError("HttpError")<{ readonly status: number }> {}
const he = new HttpError({ status: 503 })
check("T17", "Data.TaggedError instance", [he._tag, he.status, he instanceof Error, JSON.parse(JSON.stringify(he))], ["HttpError", 503, true, { status: 503, _tag: "HttpError" }])
// T18 SchemaError's own shape
const se = attempt(() => Schema.decodeUnknownSync(Schema.Number)("x"))
const seObj = (() => { try { Schema.decodeUnknownSync(Schema.Number)("x") } catch (e) { return e as any } })()
check("T18", "SchemaError tag, message, issue tag", [seObj._tag, seObj.message, seObj.issue._tag, Schema.isSchemaError(seObj)], ["SchemaError", "Expected number", "InvalidType", true])
void se

// T19 the TypeScript rule at an undeclared optional key, at run time (assign-records.ts, `hole`)
const hasX = { x: 1, y: 2 }
const onlyY: { readonly y: number } = hasX
const hole: { readonly x?: string; readonly y: number } = onlyY
check("T19", "typeof hole.x", typeof hole.x, "number")

// T20 the tree's codec refuses an excess key where rc.112 drops it
// (Test/Codegen/SchemaGenerationContract.lean:248 has `Ty.decode (.option .nat) {_tag: None, extra} = none`)
const OptJson = Schema.toCodecJson(Schema.Option(Schema.Number))
check("T20", "rc.112 decodes {_tag: None, extra} at toCodecJson(Option(Number))",
  attempt(() => Schema.decodeUnknownSync(OptJson)({ _tag: "None", extra: true })), { ok: { _id: "Option", _tag: "None" } })
// T21 a duplicate `_tag` in JSON text: JSON.parse keeps the last, rc.112 decodes that
// (the tree refuses the duplicated object, SchemaGenerationContract.lean:247)
check("T21", "rc.112 decodes '{\"_tag\":\"Some\",\"_tag\":\"None\"}' at fromJsonString(toCodecJson(Option(Number)))",
  attempt(() => Schema.decodeUnknownSync(Schema.fromJsonString(OptJson))('{"_tag":"Some","_tag":"None"}')), { ok: { _id: "Option", _tag: "None" } })

console.log(failures === 0 ? "ALL OK" : `${failures} MISMATCH(ES)`)
process.exit(failures === 0 ? 0 : 1)
