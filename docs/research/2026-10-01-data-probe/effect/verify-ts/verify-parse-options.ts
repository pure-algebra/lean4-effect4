/**
 * Verifier of seat EFFECT (2026-10-01): rc.112 decode behaviour carried as DATA beside the shape —
 * per-call ParseOptions and schema annotations — which S-a1 ("exact modulo stripAnn"), S3 (one
 * excess-key policy) and EFF-13 (the default formatter's message) must account for. Run under bun
 * against the pinned effect@4.0.0-rc.112. Exit 1 on any mismatch.
 */
import { Schema, SchemaRepresentation } from "/Users/pooks/Dev/lean4-effect4/ts/eff/node_modules/effect/dist/index.js"

let failures = 0
const check = (id: string, label: string, observed: unknown, expected: unknown) => {
  const o = JSON.stringify(observed), e = JSON.stringify(expected)
  const ok = o === e
  if (!ok) failures++
  console.log(`${id} ${label}: ${o}  expect=${e}  ${ok ? "ok" : "MISMATCH"}`)
}
const run = (f: () => unknown): unknown => { try { return { ok: f() } } catch (e: any) { return { error: `${e?._tag ?? e?.name}: ${e?.message}` } } }

const User = Schema.Struct({ id: Schema.Number, name: Schema.String })
const OptJson = Schema.toCodecJson(Schema.Option(Schema.Number))

// P1 per-call onExcessProperty "error": rc.112 refuses the excess key the tree's decoder refuses
check("P1", "toCodecJson(Option(Number)) with {_tag: None, extra}, onExcessProperty: error",
  run(() => Schema.decodeUnknownSync(OptJson)({ _tag: "None", extra: true }, { onExcessProperty: "error" })).hasOwnProperty("error"), true)
// P2 per-call onExcessProperty "preserve": the excess key stays in the decoded value
// (run 1 expected the declared keys first; rc.112 writes the preserved key first)
check("P2", "Struct with onExcessProperty: preserve keeps the extra key",
  run(() => Schema.decodeUnknownSync(User)({ id: 1, name: "a", extra: true }, { onExcessProperty: "preserve" })), { ok: { extra: true, id: 1, name: "a" } })
// P3 per-call propertyOrder "original": output key order follows the input
check("P3", "propertyOrder: original keeps input order",
  run(() => Object.keys(Schema.decodeUnknownSync(User)({ name: "a", id: 1 }, { propertyOrder: "original" }))), { ok: ["name", "id"] })
// P4 the same policy as a schema annotation (SchemaParser.ts:1096-1102 merges ast.annotations.parseOptions)
const Strict = User.annotate({ parseOptions: { onExcessProperty: "error" } })
check("P4", "parseOptions annotation refuses an extra key with no per-call option",
  run(() => Schema.decodeUnknownSync(Strict)({ id: 1, name: "a", extra: true })).hasOwnProperty("error"), true)
// P5 the annotation is persisted by toRepresentation (internal/schema/toRepresentation.ts annotationsField)
const doc = SchemaRepresentation.toRepresentation(Strict.ast)
check("P5", "toRepresentation keeps the parseOptions annotation",
  (doc.representation as any).annotations?.parseOptions ?? null, { onExcessProperty: "error" })
// P6 an identifier annotation changes the default formatter's message
const UserId = Schema.Number.annotate({ identifier: "UserId" })
check("P6", "identifier annotation in the SchemaError message",
  run(() => Schema.decodeUnknownSync(UserId)("x")), { error: "SchemaError: Expected UserId" }) // run 1 expected the input in the text; it appears only under reportInput (T4b)
// P7 errors: "all" changes the message text of the same failure
const two = { id: "x" }
const first = run(() => Schema.decodeUnknownSync(User)(two))
const all = run(() => Schema.decodeUnknownSync(User)(two, { errors: "all" }))
check("P7", "errors: all changes the message", JSON.stringify(first) === JSON.stringify(all), false)

console.log(failures === 0 ? "ALL OK" : `${failures} MISMATCH(ES)`)
process.exit(failures === 0 ? 0 : 1)
