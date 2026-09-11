import assert from "node:assert/strict"
import { pathToFileURL } from "node:url"
import { Cause, Exit, Option, Result, Schema } from "effect"
import effectPackage from "effect/package.json"

assert.equal(effectPackage.version, "4.0.0-rc.112")
const input = process.argv[2]
if (!input) throw new Error("expected a fresh Lean output module")
const { default: encoded } = await import(pathToFileURL(input).href)
if (typeof encoded !== "object" || encoded === null || Array.isArray(encoded)) {
  throw new Error("Lean codec output is not an object")
}

const cause = Cause.fromReasons([
  Cause.makeFailReason("bad"),
  Cause.makeDieReason({ user: 7 }),
  Cause.makeInterruptReason(undefined),
  Cause.makeInterruptReason(9)
])
let checked = 0
const names: string[] = []
function check<S extends Schema.ConstraintCodec<unknown, unknown>>(name: string, schema: S, value: S["Type"]) {
  const codec = Schema.toCodecJson(schema)
  const host = Schema.encodeSync(codec)(value)
  assert.deepEqual(encoded[name], host, `${name}: Lean/rc.112 encoding differs`)
  const recovered = Schema.decodeUnknownSync(codec)(encoded[name])
  assert.deepEqual(Schema.encodeSync(codec)(recovered), host, `${name}: host round trip differs`)
  names.push(name)
  checked++
}

check("unit", Schema.Void, undefined)
check("bool", Schema.Boolean, true)
check("nat", Schema.Int.check(Schema.isGreaterThanOrEqualTo(0)), 42)
check("string", Schema.String, "λ🙂")
check("literal", Schema.Literal("User"), "User")
check("pair", Schema.Tuple([Schema.Number, Schema.String]), [3, "x"])
check("list", Schema.Array(Schema.Boolean), [true, false])
check("none", Schema.Option(Schema.Number), Option.none())
check("some", Schema.Option(Schema.Number), Option.some(7))
check("resultFailure", Schema.Result(Schema.Boolean, Schema.String), Result.fail("bad"))
check("resultSuccess", Schema.Result(Schema.Boolean, Schema.String), Result.succeed(true))
check("exitSuccess", Schema.Exit(Schema.Boolean, Schema.String, Schema.Defect()), Exit.succeed(true))
check("exitFailure", Schema.Exit(Schema.Boolean, Schema.String, Schema.Defect()), Exit.failCause(cause))
check("cause", Schema.Cause(Schema.String, Schema.Defect()), cause)
check("emptyCause", Schema.Cause(Schema.Never, Schema.Defect()), Cause.empty)
check("union", Schema.Union([Schema.String, Schema.Number]), 4)
check("nested", Schema.Array(Schema.Option(Schema.Result(Schema.Boolean, Schema.String))),
  [Option.some(Result.succeed(true)), Option.none()])
assert.deepEqual(Object.keys(encoded).sort(), names.sort(), "uncompared or missing Lean fixture")

// Negative controls catch the two incorrect shapes in the original specification.
assert.throws(() => Schema.decodeUnknownSync(Schema.toCodecJson(
  Schema.Result(Schema.Boolean, Schema.String)))({ _tag: "Success", value: true }))
assert.throws(() => Schema.decodeUnknownSync(Schema.toCodecJson(
  Schema.Cause(Schema.String, Schema.Defect())))({ reasons: [] }))
console.log(`PASS schema-codec: ${checked} fresh Lean/rc.112 comparisons, ${checked} host round trips, 2 negative controls`)
