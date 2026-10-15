/** The JSON Schemas of the to-do's entries, written at generation by rc.112's own compiler (CR-4).
 *
 * `EmitTodo.lean` writes the module's surface (`.work/todo.surface.gen.ts`): the Schemas of each
 * data service's methods. This writes `OUT/todo.schemas.json` from them: for each method, the JSON
 * Schema document (draft 2020-12) of its input, its answer and its error, each of the canonical
 * JSON form (`Schema.toJsonSchemaDocument`, `vendor/effect-4.0.0-rc.112/src/Schema.ts`).
 *
 * Each input's document is checked as it is written. rc.112 imports it back
 * (`SchemaRepresentation.fromJsonSchemaDocument`), and the imported Schema accepts the canonical
 * JSON of each member input below and refuses each non-member, as the surface's Schema does. The
 * inputs are a finite evaluation, not a law.
 *
 *     bun --no-install apps/todo/json-schemas.ts OUT */
import { mkdir, writeFile } from "node:fs/promises"
import { resolve } from "node:path"
import { Exit, Schema, SchemaRepresentation } from "effect"
import * as Surface from "./.work/todo.surface.gen.ts"

const [out] = process.argv.slice(2)
if (!out) throw Error("usage: json-schemas.ts OUT")

type Entry = { readonly input: Schema.Top; readonly answer: Schema.Top; readonly error: Schema.Top }
const services = Object.entries(Surface).filter(([name]) => name.endsWith("Schemas")) as
  Array<[string, Readonly<Record<string, Entry>>]>
if (services.length === 0) throw Error("the surface holds no service's Schemas")

const documents: Record<string, Record<string, Record<string, unknown>>> = {}
for (const [name, methods] of services) {
  documents[name] = {}
  for (const [method, entry] of Object.entries(methods))
    documents[name]![method] = {
      input: Schema.toJsonSchemaDocument(entry.input),
      answer: Schema.toJsonSchemaDocument(entry.answer),
      error: Schema.toJsonSchemaDocument(entry.error)
    }
}

/** The inputs each method's input document is checked at: members of the input's type, and
 * values outside it, each as its canonical JSON. */
const cases: Record<string, { readonly members: ReadonlyArray<unknown>; readonly others: ReadonlyArray<unknown> }> = {
  add: { members: [["milk"], [""]], others: [[1], [], ["milk", "tea"]] },
  list: { members: [[]], others: [["milk"]] },
  complete: { members: [[0], [1], [Number.MAX_SAFE_INTEGER]], others: [[-1], [1.5], ["1"]] },
  remove: { members: [[1]], others: [[-1], [1.5]] }
}
const accepts = (schema: Schema.Top, value: unknown): boolean =>
  Exit.isSuccess(Schema.decodeUnknownExit(Schema.toCodecJson(schema) as unknown as Schema.Codec<unknown, unknown>,
    { onExcessProperty: "error" })(value))
let checked = 0
for (const [method, { members, others }] of Object.entries(cases)) {
  const entry = Surface.TodoAppSchemas[method as keyof typeof Surface.TodoAppSchemas]
  const imported = SchemaRepresentation.fromJsonSchemaDocument(
    documents["TodoAppSchemas"]![method]!["input"] as Parameters<typeof SchemaRepresentation.fromJsonSchemaDocument>[0])
  for (const value of members) {
    if (!accepts(entry.input, value)) throw Error(`${method}: the surface's input Schema refuses the member ${JSON.stringify(value)}`)
    if (!accepts(imported, value)) throw Error(`${method}: the input's JSON Schema refuses the member ${JSON.stringify(value)}`)
    checked++
  }
  for (const value of others) {
    if (accepts(entry.input, value)) throw Error(`${method}: the surface's input Schema accepts ${JSON.stringify(value)}`)
    if (accepts(imported, value)) throw Error(`${method}: the input's JSON Schema accepts ${JSON.stringify(value)}`)
    checked++
  }
}
await mkdir(out, { recursive: true })
await writeFile(resolve(out, "todo.schemas.json"), JSON.stringify(documents, null, 2) + "\n")
const methods = services.reduce((n, [, m]) => n + Object.keys(m).length, 0)
console.log(`PASS the to-do's JSON Schemas: ${methods} methods of ${services.length} services, three documents each, ` +
  `written by rc.112; ${checked} inputs on which each input document and its Schema agree`)
