import { describe, expect, test } from "bun:test"
import { spawnSync } from "node:child_process"
import { resolve } from "node:path"
import { Result } from "effect"
import type { Term } from "../eff.gen.ts"
import { readTypeScript } from "../read.ts"
import fixtures from "./type-projection.gen.json"

// The error payload face's red twin (decisions row 120, part E2): tsgo 7, the one compiler, run on
// `test/red/tsconfig.json`, must refuse every line of `test/red/payload-classes.red.ts` with the
// code pinned here. The green file, `test/payload-classes.typecheck.ts`, is part of the package's
// own type check. Finite compiler evidence against effect@4.0.0-rc.112, not an execution theorem.
const root = resolve(import.meta.dir, "..")
const tsgo = resolve(root, "node_modules/@typescript/native-preview/bin/tsgo")

describe("payload classes under tsgo 7", () => {
  test("the red twin fails with exactly its pinned codes", () => {
    const run = spawnSync("node", [tsgo, "--noEmit", "--pretty", "false", "-p", resolve(root, "test/red/tsconfig.json")],
      { cwd: root, encoding: "utf8" })
    expect(run.status).toBe(1)
    const errors = [...run.stdout.matchAll(/^test\/red\/payload-classes\.red\.ts\((\d+),\d+\): error (TS\d+):/gm)]
      .map((match) => `${match[1]} ${match[2]}`)
    expect(errors).toEqual([
      "9 TS2740",  // a structural record is no class instance
      "10 TS2375", // nor a structural failure under an error column that names the class
      "11 TS2375", // nor under a union of classes
      "12 TS2353", // the constructor takes no `_tag`
      "13 TS2322", // the constructor keeps its fields' types
      "15 TS2375", // DI-55's finding F3: the former raw suspension infers one arm's error
    ])
  })
})

// The reader's class branch (`read.ts` `classDeclOf`, `readClassTerm`; Lean's
// `Codegen/Classes.lean` `readClassDecl`, `readClass`): a printed module reads back with each
// construction's declared fields restored from its class, `_tag` first.
const header = 'import { Data, Effect } from "effect"\n'
const notFoundClass = 'export class NotFound extends Data.TaggedError("NotFound")<{ readonly id: number }> {}\n'
const notFound: Term = {
  _tag: "record",
  fields: [["_tag", [false, { _tag: "lit", value: "NotFound" }]], ["id", [false, { _tag: "nat" }]]],
  presentNames: ["_tag", "id"],
  values: [{ _tag: "lit", value: { _tag: "str", value: "NotFound" } }, { _tag: "lit", value: { _tag: "nat", value: 9 } }],
}
const reads = (source: string) => {
  const read = readTypeScript(source)
  return Result.isSuccess(read) ? read.success : undefined
}
const refused = (source: string) => {
  const read = readTypeScript(source)
  return Result.isFailure(read) ? JSON.stringify(read.failure) : undefined
}
const metadata = fixtures.cases.find((item) => item.raw._tag === "record" && "fields" in item.raw &&
  item.raw.fields?.[0]?.[0] === "_tag" && item.annotation === "NotFound")!.metadata

describe("payload classes through the TypeScript reader", () => {
  test("a printed module reads back to its program", () => {
    expect(reads(header + notFoundClass +
      "export const main: Effect.Effect<never, NotFound, never> = Effect.fail(new NotFound({ id: 9 }))\n"))
      .toEqual({ _tag: "fail", error: notFound })
    expect(reads(header + notFoundClass +
      "export const main: Effect.Effect<NotFound, never, never> = Effect.succeed(new NotFound({ id: 9 }))\n"))
      .toEqual({ _tag: "succeed", value: notFound })
  })

  test("a declared field of type `never` reads, as the Lean class reader reads it", () => {
    // The field-type reader reads `never` since the state plan's T5, part B (Lean `readNamed`:
    // the error column of `Deferred.make<A, never>()` is spelled so), and a class's field types
    // go through it. `Test/Codegen/TypeReader.lean` pins the same declaration. `unknown` has no
    // reading, in either reader.
    expect(reads(header + 'export class X extends Data.TaggedError("X")<{ readonly a: never }> {}\n' +
      "export const main = Effect.succeed(0)\n")).toEqual({ _tag: "succeed", value: { _tag: "lit", value: { _tag: "nat", value: 0 } } })
    expect(refused(header + 'export class X extends Data.TaggedError("X")<{ readonly a: unknown }> {}\n' +
      "export const main = Effect.succeed(0)\n")).toBe('{"_tag":"shape","what":"class"}')
  })

  test("red controls: no class, another tag, a member, a structural record in the class form", () => {
    expect(refused("Effect.fail(new NotFound({ id: 9 }))")).toBe('{"_tag":"unknownIdent","name":"NotFound"}')
    expect(refused(header + 'export class NotFound extends Data.TaggedError("Other")<{ readonly id: number }> {}\n' +
      "export const main = Effect.fail(new NotFound({ id: 9 }))\n")).toBe('{"_tag":"shape","what":"class"}')
    expect(refused(header + 'export class NotFound extends Data.TaggedError("NotFound")<{ readonly id: number }> { x = 1 }\n' +
      "export const main = Effect.fail(new NotFound({ id: 9 }))\n")).toBe('{"_tag":"shape","what":"class"}')
    expect(refused(header + 'export class NotFound extends Data.TaggedError("NotFound")<{ id: number }> {}\n' +
      "export const main = Effect.fail(new NotFound({ id: 9 }))\n")).toBe('{"_tag":"shape","what":"class"}')
    expect(refused(header + notFoundClass +
      `export const main = Effect.fail(recordValue<NotFound>(${metadata}, { _tag: "NotFound", id: 9 }))\n`))
      .toBe('{"_tag":"shape","what":"record in class form"}')
  })
})
