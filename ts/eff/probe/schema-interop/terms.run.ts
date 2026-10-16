/** The term probe: our first-order expressions as Schema checks and codecs, through rc.112's
 * persisted documents.
 *
 * Run in `ts/eff`: `bun probe/schema-interop/terms.run.ts`.
 *
 * A check is a filter whose representation id is `effect4/term` and whose payload is Lean's own
 * `Term` (`Machine/Term.lean`), in the wire form `eff.gen.ts` decodes, with the refusal's path and
 * reason. A codec is a declaration whose id is `effect4/codec`: its two type parameters are the
 * wire side and the type side, and its payload is the pair of terms, read and write.
 *
 * The evaluator below reads a term and calls each atom's generated prelude body
 * (`harness/truth/prelude-atoms.gen.ts`, from `NativeAtom.row`); it holds no copy of an atom.
 * It covers `var`, `lit`, `app`, a required `field` and `tupleAt`, and refuses the rest. Its
 * agreement with Lean's evaluation is a proposed law, not an observation of this probe. */
import { Effect, Option, Schema, SchemaIssue, SchemaRepresentation, SchemaTransformation } from "effect"
import { isDeepStrictEqual } from "node:util"
import { writeFileSync } from "node:fs"
import { join } from "node:path"
import { Term } from "../../eff.gen.ts"
import { builtins, decode, encode, normS, show } from "./census.run.ts"

type Json = Schema.Json
type Atom = (...args: ReadonlyArray<unknown>) => unknown
const atomsPath = join(import.meta.dir, "../../../../harness/truth/prelude-atoms.gen.ts")
const Atoms = (await import(atomsPath)) as Record<string, Atom>

/** Evaluate a term over an environment of values, `var i` at position `i` (Lean's levels). */
export const evalTerm = (term: Term, env: ReadonlyArray<unknown>): unknown => {
  switch (term._tag) {
    case "var": {
      if (term.index >= env.length) throw new Error(`variable ${term.index} out of scope`)
      return env[term.index]
    }
    case "lit": {
      const v = term.value
      return v._tag === "unit" ? undefined : v.value
    }
    case "app": {
      const atom = Atoms[term.atom]
      if (atom === undefined) throw new Error(`no atom ${term.atom}`)
      return atom(...term.args.map(arg => evalTerm(arg, env)))
    }
    case "field": {
      if (term.mode !== "required") throw new Error("an optional field read is outside this evaluator")
      return (evalTerm(term.target, env) as Record<string, unknown>)[term.name]
    }
    case "tupleAt": return (evalTerm(term.target, env) as ReadonlyArray<unknown>)[term.index]
    default: throw new Error(`the term ${term._tag} is outside this evaluator`)
  }
}

// ---- terms, as the Lean surface writes them ----------------------------------------------------
const v = (index: number): Term => ({ _tag: "var", index })
const nat = (value: number): Term => ({ _tag: "lit", value: { _tag: "nat", value } })
const str = (value: string): Term => ({ _tag: "lit", value: { _tag: "str", value } })
const app = (atom: string, ...args: ReadonlyArray<Term>): Term => ({ _tag: "app", atom, args })
const field = (target: Term, name: string): Term => ({ _tag: "field", mode: "required", target, name })
const self = v(0)
const f = (name: string) => field(self, name)
const not = (t: Term) => app("not", t)
const le = (a: Term, b: Term) => not(app("lt", b, a))

/** A term as TypeScript over the prelude's atoms: `var 0` is the checked value `a0`, a parameter
 * is its payload value written inline, and an atom is a call of its prelude export. This stands in
 * for Lean's term printer (`Codegen/PrintLeaf.lean`) on the evaluator's fragment. */
export const printTerm = (term: Term, params: ReadonlyArray<unknown>, atoms: Set<string>): string => {
  switch (term._tag) {
    case "var": return term.index === 0 ? "a0" : JSON.stringify(params[term.index - 1])
    case "lit": return term.value._tag === "unit" ? "undefined" : JSON.stringify(term.value.value)
    case "app": atoms.add(term.atom); return `${term.atom}(${term.args.map(a => printTerm(a, params, atoms)).join(", ")})`
    case "field": return `${printTerm(term.target, params, atoms)}.${term.name}`
    case "tupleAt": return `${printTerm(term.target, params, atoms)}[${term.index}]`
    default: throw new Error(`the term ${term._tag} is outside this printer`)
  }
}
/** The prelude the printed code imports its atoms from, relative to `cases/`. */
const preludeFromCases = "../../../../../harness/truth/prelude-atoms.gen.ts"

// ---- the check reviver ---------------------------------------------------------------------------
const TermCheck = Schema.Struct({
  term: Term,
  params: Schema.Array(Schema.Json),
  path: Schema.Array(Schema.String),
  reason: Schema.String
})
type TermCheck = typeof TermCheck.Type
const termCheckJson = Schema.toCodecJson(TermCheck)

/** A term check as a Schema filter: the term at `[value, ...params]` must answer `true`. The filter
 * carries its own representation, so rc.112 writes it back. */
export const termFilter = (payload: TermCheck) =>
  Schema.makeFilter((input: unknown) =>
    evalTerm(payload.term, [input, ...payload.params]) === true ? undefined : { path: payload.path, issue: payload.reason },
    {
      representation: { id: "effect4/term", payload: Schema.encodeSync(termCheckJson)(payload) as Json }, expected: payload.reason,
      toCode: () => {
        const atoms = new Set<string>()
        const body = printTerm(payload.term, payload.params, atoms)
        return {
          // rc.112 gives a check's `toCode` no type of the checked node (`toCodeDocument.ts:341`
          // passes `{ schemas }` only), and contextual typing does not reach the parameter, so
          // this stand-in writes `any`; Lean's printer, which knows the node, writes its type.
          runtime: `Schema.makeFilter((a0: any) => ${body} ? undefined : { path: ${JSON.stringify(payload.path)}, issue: ${JSON.stringify(payload.reason)} })`,
          // one line per atom: rc.112 merges import lines only when their text is equal
          importDeclarations: [...atoms].sort().map(atom => `import { ${atom} } from "${preludeFromCases}"`)
        }
      }
    })
export const termCheckReviver = SchemaRepresentation.makeFilterReviver("effect4/term", TermCheck,
  ({ payload, annotations }) => {
    const filter = termFilter(payload)
    return annotations === undefined ? filter : filter.annotate(annotations)
  })

/** The persisted form a Lean writer would emit: one filter per clause, aborting, so that decoding
 * stops at the first failed clause as `inputRefusal` does. */
const clause = (term: Term, path: ReadonlyArray<string>, reason: string, params: ReadonlyArray<Json> = []): Json => ({
  _tag: "Filter", aborted: true,
  representation: { id: "effect4/term", payload: Schema.encodeSync(termCheckJson)({ term, params, path, reason }) as Json }
})

// The bridge's spellings: a natural, a string, a property.
const natRep: Json = { _tag: "Number", checks: [
  { _tag: "Filter", representation: { id: "effect/schema/isInt", payload: null }, aborted: false },
  { _tag: "Filter", representation: { id: "effect/schema/isGreaterThanOrEqualTo", payload: { minimum: 0 } }, aborted: false }] }
const strRep: Json = { _tag: "String", checks: [] }
const prop = (name: string, type: Json): Json => ({ name: { type: "string", value: name }, type, isOptional: false, isMutable: false })
const objects = (fields: ReadonlyArray<readonly [string, Json]>, checks: ReadonlyArray<Json>): Json =>
  ({ _tag: "Objects", checks: [...checks], propertySignatures: fields.map(([n, t]) => prop(n, t)), indexSignatures: [] })

let observations = 0
let failures = 0
const say = (line: string) => { observations++; console.log(line) }
const expect = (label: string, cond: boolean) => { if (!cond) failures++; say(`${cond ? "ok  " : "FAIL"} ${label}`) }

// ---- 1. the vessel's working levels and nozzle profile, as term checks --------------------------
// `inputRefusal` (Domain.lean), its clauses on these fields in their order.
const levelClauses: ReadonlyArray<readonly [Term, string, string]> = [
  [not(app("isZero", f("diameterMm"))), "diameterMm", "nonpositiveDimension"],
  [not(app("isZero", f("heightMm"))), "heightMm", "nonpositiveDimension"],
  [not(app("isZero", f("nozzleRadiusMm"))), "nozzleRadiusMm", "nonpositiveDimension"],
  [app("lt", app("mul", nat(2), f("nozzleRadiusMm")), f("diameterMm")), "nozzleRadiusMm", "nozzleOutsideProfile"],
  [app("lt", f("minimumLevelMm"), f("maximumLevelMm")), "maximumLevelMm", "invalidWorkingLevels"],
  [app("lt", f("maximumLevelMm"), f("heightMm")), "maximumLevelMm", "invalidWorkingLevels"],
  [le(f("minimumLevelMm"), f("initialLevelMm")), "initialLevelMm", "invalidWorkingLevels"],
  [le(f("initialLevelMm"), f("maximumLevelMm")), "initialLevelMm", "invalidWorkingLevels"],
  [le(f("diameterMm"), nat(100000)), "diameterMm", "outsideNumericProfile"]
]
const fields = ["diameterMm", "heightMm", "nozzleRadiusMm", "minimumLevelMm", "maximumLevelMm", "initialLevelMm"] as const
const geometryDoc: Json = {
  representation: objects(fields.map(n => [n, natRep] as const), levelClauses.map(([t, p, r]) => clause(t, [p], r))),
  references: {}
}
const revivers = [...builtins, termCheckReviver]
const Geometry = SchemaRepresentation.fromRepresentation(SchemaRepresentation.fromJson(geometryDoc), { revivers })
const good = { diameterMm: 1200, heightMm: 3000, nozzleRadiusMm: 50, minimumLevelMm: 300, maximumLevelMm: 2500, initialLevelMm: 1000 }
// Each sample breaks one clause; the expected path and reason are `inputRefusal`'s first failure.
const samples: ReadonlyArray<readonly [string, Record<string, number>, string | undefined]> = [
  ["a valid geometry", good, undefined],
  ["a zero height", { ...good, heightMm: 0 }, "heightMm: nonpositiveDimension"],
  ["a nozzle wider than half the diameter", { ...good, nozzleRadiusMm: 600 }, "nozzleRadiusMm: nozzleOutsideProfile"],
  ["inverted working levels", { ...good, minimumLevelMm: 2600 }, "maximumLevelMm: invalidWorkingLevels"],
  ["an initial level below the minimum", { ...good, initialLevelMm: 100 }, "initialLevelMm: invalidWorkingLevels"],
  ["two broken clauses, the earlier reported", { ...good, heightMm: 2000, initialLevelMm: 2600 }, "maximumLevelMm: invalidWorkingLevels"],
  ["a diameter outside the numeric profile", { ...good, diameterMm: 200000 }, "diameterMm: outsideNumericProfile"]
]
for (const [label, input, want] of samples) {
  const out = decode(Geometry, input)
  const got = "ok" in out ? undefined : out.issues.map(i => `${i.path}: ${i.message}`).join("; ")
  expect(`1 ${label}: ${got ?? "decodes"}`, got === want)
}
const geometryBack = normS(SchemaRepresentation.toJson(SchemaRepresentation.toRepresentation(Geometry.ast)))
expect("1 rc.112 writes the revived term checks back unchanged, modulo N_S", isDeepStrictEqual(geometryBack, geometryDoc))
const geometryCode = SchemaRepresentation.toCodeDocument(SchemaRepresentation.toMultiDocument(
  SchemaRepresentation.toRepresentation(Geometry.ast)))
const imports = [...new Set(geometryCode.artifacts.flatMap(a => a._tag === "Import" ? [a.importDeclaration] : []))]
const generated = [
  "// expect: none",
  "// GENERATED by probe/schema-interop/terms.run.ts from the revived geometry document; do not edit.",
  "// rc.112's code generator (`toCodeDocument`) writes each term check through its `toCode` annotation.",
  `import { Schema } from "effect"`, ...imports,
  `export const Geometry = ${geometryCode.codes[0]!.runtime}`,
  `export type Geometry = typeof Geometry.Type`,
  ""].join("\n")
writeFileSync(join(import.meta.dir, "cases/g01-term-code.generated.ts"), generated)
say(`     rc.112's code of the term checks: ${geometryCode.codes[0]!.runtime.slice(0, 160)}…`)
const reloaded = (await import(join(import.meta.dir, "cases/g01-term-code.generated.ts"))) as { Geometry: Schema.Top }
expect("1 the generated code, evaluated, decodes every geometry sample as the revived document does",
  samples.every(([, input]) => isDeepStrictEqual(decode(reloaded.Geometry, input), decode(Geometry, input))))

// ---- 2. Positive as a term, against rc.112's own isGreaterThan 0 ----------------------------------
const positiveTerm = Schema.Number.check(Schema.isInt(), termFilter({ term: not(app("isZero", self)), params: [], path: [], reason: "nonpositive" }))
const positiveHost = Schema.Number.check(Schema.isInt(), Schema.isGreaterThan(0))
const positiveSamples = [0, 1, 2, 100, -1, 1.5]
const agree = positiveSamples.filter(s => ("ok" in decode(positiveTerm, s)) === ("ok" in decode(positiveHost, s)))
say(`     Positive, term against host, per sample: ${show(positiveSamples.map(s => ["ok" in decode(positiveTerm, s), "ok" in decode(positiveHost, s)]))}`)
expect(`2 not (isZero x) and isGreaterThan 0 disagree only at -1, which the natural's own checks refuse first in Lean's spelling`,
  isDeepStrictEqual(positiveSamples.filter(s => !agree.includes(s)), [-1]))
const positiveNat = Schema.Number.check(Schema.isInt(), Schema.isGreaterThanOrEqualTo(0),
  termFilter({ term: not(app("isZero", self)), params: [], path: [], reason: "nonpositive" }))
expect("2 on Lean's natural spelling ([isInt, ≥ 0]) the term check and isGreaterThan 0 agree on every sample",
  positiveSamples.every(s => ("ok" in decode(positiveNat, s)) === ("ok" in decode(positiveHost, s))))

// ---- 3. a parameterized check: evidence relevance against an expected study --------------------
// `EvidenceRelevant` (Domain.lean), the clauses on the record: the study and the kind equal the
// expected ones (parameters 1 and 2), and the provenance fields are not empty.
const relevance = app("and", app("eq", f("studyDigest"), v(1)),
  app("and", app("eq", f("kind"), v(2)),
    app("and", not(app("eq", f("tool"), str(""))), app("and", not(app("eq", f("artifactId"), str(""))), app("eq", f("passed"), { _tag: "lit", value: { _tag: "bool", value: true } })))))
const evidenceDoc: Json = {
  representation: objects([["studyDigest", strRep], ["kind", strRep], ["tool", strRep], ["artifactId", strRep], ["passed", { _tag: "Boolean", checks: [] }]],
    [clause(relevance, ["evidence"], "irrelevantEvidence", ["sha256:ab12", "geometry"])]),
  references: {}
}
const EvidenceSchema = SchemaRepresentation.fromRepresentation(SchemaRepresentation.fromJson(evidenceDoc), { revivers })
const evidence = { studyDigest: "sha256:ab12", kind: "geometry", tool: "cad", artifactId: "a1", passed: true }
expect("3 relevant evidence decodes", "ok" in decode(EvidenceSchema, evidence))
expect("3 evidence of another study is refused at the evidence path",
  isDeepStrictEqual(decode(EvidenceSchema, { ...evidence, studyDigest: "sha256:ff00" }),
    { issues: [{ path: "evidence", message: "irrelevantEvidence" }] }))
expect("3 evidence of another kind is refused", !("ok" in decode(EvidenceSchema, { ...evidence, kind: "levelSimulation" })))

// ---- 4. a codec as a declaration: metres on the wire, millimetres in the type -------------------
const TermPair = Schema.Struct({ read: Term, write: Term })
type TermPair = typeof TermPair.Type
const termPairJson = Schema.toCodecJson(TermPair)
const codecDeclaration = (pair: TermPair, wire: Schema.Top, type: Schema.Top) =>
  Schema.declareConstructor<number, number>()([wire, type] as const, ([, t]) => (input, _ast, options) =>
    Schema.decodeUnknownEffect(t as Schema.Codec<number, number>)(input, options).pipe(
      Effect.mapError((e) => e.issue)),
  {
    representation: { id: "effect4/codec", payload: Schema.encodeSync(termPairJson)(pair) as Json },
    toCodec: ([w]) => Schema.link<number>()(w as Schema.Codec<number, number>, SchemaTransformation.transform({
      decode: (e: number) => evalTerm(pair.read, [e]) as number,
      encode: (a: number) => evalTerm(pair.write, [a]) as number
    }))
  })
const codecReviver = SchemaRepresentation.makeDeclarationReviver("effect4/codec", TermPair,
  ({ payload, typeParameters }) => codecDeclaration(payload, typeParameters[0]!, typeParameters[1]!))
const millimetres = Schema.Number.check(Schema.isInt(), Schema.isGreaterThanOrEqualTo(0), Schema.isMultipleOf(1000))
const pair: TermPair = { read: app("mul", self, nat(1000)), write: app("div", self, nat(1000)) }
const lengthDoc = normS(SchemaRepresentation.toJson(SchemaRepresentation.toRepresentation(
  codecDeclaration(pair, Schema.Number.check(Schema.isInt(), Schema.isGreaterThanOrEqualTo(0)), millimetres).ast))) as Json
say(`     the codec's document: ${JSON.stringify(lengthDoc).slice(0, 240)}…`)
const Length = SchemaRepresentation.fromRepresentation(SchemaRepresentation.fromJson(lengthDoc), { revivers: [...builtins, codecReviver] })
expect("4 rc.112 writes the revived codec declaration back unchanged, modulo N_S",
  isDeepStrictEqual(normS(SchemaRepresentation.toJson(SchemaRepresentation.toRepresentation(Length.ast))), lengthDoc))
const lengthJson = Schema.toCodecJson(Length as Schema.Codec<number, unknown>)
const reads = [0, 3, 12].map(m => decode(lengthJson, m))
expect(`4 read: metres 0, 3, 12 decode to millimetres ${show(reads)}`, isDeepStrictEqual(reads, [{ ok: 0 }, { ok: 3000 }, { ok: 12000 }]))
const writes = [3000, 1500].map(mm => encode(lengthJson, mm))
say(`     write: millimetres 3000, 1500 encode to ${show(writes)}`)
expect("4 write refuses 1500 mm: the type side's isMultipleOf 1000 is the write's domain", "ok" in writes[0]! && !("ok" in writes[1]!))
expect("4 retraction on the domain: read (write 3000) = 3000", isDeepStrictEqual(decode(lengthJson, (writes[0] as { ok: unknown }).ok), { ok: 3000 }))

void Option
void SchemaIssue
if (failures > 0) throw new Error(`${failures} term observation(s) failed`)
console.log(`PASS schema-interop terms: ${observations} observations`)
