/** The Schema document face of a declared name, on rc.112: what rc.112 revives from a document
 * whose declared names are references, and what it writes back.
 *
 * Run: `bun probe/named-types/documents.run.ts` in `ts/eff`. Each line is one observation of the
 * pinned host. A failed expectation throws. */
import { Schema, SchemaRepresentation } from "effect"
import { isDeepStrictEqual } from "node:util"

type Json = Schema.Json
const revivers = [Schema.OptionReviver, Schema.ResultReviver, Schema.ExitReviver, Schema.CauseReviver,
  Schema.JsonReviver, Schema.isIntReviver, Schema.isGreaterThanOrEqualToReviver]

// The bridge's spellings (`Schema/Bridge.lean` `schemaAlg`)
const nat: Json = { _tag: "Number", checks: [
  { _tag: "Filter", representation: { id: "effect/schema/isInt", payload: null }, aborted: false },
  { _tag: "Filter", representation: { id: "effect/schema/isGreaterThanOrEqualTo", payload: { minimum: 0 } }, aborted: false }] }
const str: Json = { _tag: "String", checks: [] }
const lit = (value: string): Json => ({ _tag: "Literal", checks: [], literal: { type: "string", value } })
const ref = ($ref: string): Json => ({ _tag: "Reference", $ref })
const suspend = (thunk: Json): Json => ({ _tag: "Suspend", checks: [], thunk })
const list = (inner: Json): Json => ({ _tag: "Arrays", checks: [], elements: [], rest: [inner] })
const prop = (name: string, type: Json): Json =>
  ({ name: { type: "string", value: name }, type, isOptional: false, isMutable: false })
const struct = (fields: ReadonlyArray<readonly [string, Json]>): Json =>
  ({ _tag: "Objects", checks: [], propertySignatures: fields.map(([n, t]) => prop(n, t)), indexSignatures: [] })
const union = (types: ReadonlyArray<Json>): Json => ({ _tag: "Union", checks: [], types: [...types], mode: "anyOf" })
const option = (inner: Json): Json =>
  ({ _tag: "Declaration", representation: { id: "effect/schema/Option", payload: null }, typeParameters: [inner], checks: [] })

const doc = (root: Json, references: Record<string, Json>): Json => ({ representation: root, references })
const revive = (json: Json) => SchemaRepresentation.fromRepresentation(SchemaRepresentation.fromJson(json), { revivers })
// `N_S` (`Schema/Bridge.lean` `normAnn`, `erasedKeys`): the annotation keys that change no decoding
// are erased from every bag, and an empty bag is absent. Comparisons below are modulo `N_S`.
const erasedKeys = ["identifier", "title", "description", "documentation", "examples", "default", "message",
  "expected", "arbitrary", "~identifier"]
const normS = (value: unknown): unknown => {
  if (Array.isArray(value)) return value.map(normS)
  if (value === null || typeof value !== "object") return value
  const out: Record<string, unknown> = {}
  for (const [key, inner] of Object.entries(value)) {
    if (key === "annotations" && inner !== null && typeof inner === "object") {
      const kept = Object.entries(inner).filter(([k]) => !erasedKeys.includes(k))
      if (kept.length > 0) out[key] = Object.fromEntries(kept)
    } else out[key] = normS(inner)
  }
  return out
}
const rewrite = (schema: Schema.Top): Json =>
  normS(SchemaRepresentation.toJson(SchemaRepresentation.toRepresentation(schema.ast))) as Json
// The proposed extension of `N_S`: a Suspend with no annotation and no check around a Reference
// is that Reference. Revival makes every reference lazy, so the Suspend decides nothing.
const unsuspend = (value: unknown): unknown => {
  if (Array.isArray(value)) return value.map(unsuspend)
  if (value === null || typeof value !== "object") return value
  const node = value as Record<string, unknown>
  if (node["_tag"] === "Suspend" && node["annotations"] === undefined && Array.isArray(node["checks"]) &&
      node["checks"].length === 0 && (node["thunk"] as Record<string, unknown> | undefined)?.["_tag"] === "Reference")
    return node["thunk"]
  return Object.fromEntries(Object.entries(node).map(([k, v]) => [k, unsuspend(v)]))
}
const rewriteR = (schema: Schema.Top): Json => unsuspend(rewrite(schema)) as Json

let observations = 0
const observe = (label: string, value: unknown) => { observations++; console.log(`${label}: ${typeof value === "string" ? value : JSON.stringify(value)}`) }
const expect = (label: string, cond: boolean) => { if (!cond) throw new Error(`expectation failed: ${label}`); observe(label, "holds") }
const decodes = (schema: Schema.Top, value: unknown) => {
  try { Schema.decodeUnknownSync(schema as Schema.Codec<unknown>)(value); return true } catch { return false }
}
const decodeNote = (schema: Schema.Top, value: unknown): string => {
  try { Schema.decodeUnknownSync(schema as Schema.Codec<unknown>)(value); return "decodes" }
  catch (e) { return `throws ${e instanceof Error ? e.name : typeof e}: ${String(e).split("\n")[0]!.slice(0, 80)}` }
}

// 1. A recursive name written as a bare reference at every occurrence.
const treeBody = (child: Json) => struct([["value", nat], ["children", list(child)]])
const treeBare = doc(ref("Tree"), { Tree: treeBody(ref("Tree")) })
const treeRevived = revive(treeBare)
expect("1a bare: rc.112 revives the recursive reference and decodes a tree",
  decodes(treeRevived, { value: 1, children: [{ value: 2, children: [] }] }))
expect("1b bare: a negative child is refused at depth", !decodes(treeRevived, { value: 1, children: [{ value: -2, children: [] }] }))
const treeBack = rewrite(treeRevived)
observe("1c bare: rc.112 writes back", treeBack)
expect("1d bare: rc.112 writes a Suspend at the back edge, so the bare document is no fixed point",
  !isDeepStrictEqual(treeBack, treeBare) && isDeepStrictEqual(treeBack, doc(ref("Tree"), { Tree: treeBody(suspend(ref("Tree"))) })))

// 2. A Suspend around every reference inside a recursive name's own component.
const treeSuspended = doc(ref("Tree"), { Tree: treeBody(suspend(ref("Tree"))) })
expect("2a suspended: rc.112 writes the document back unchanged", isDeepStrictEqual(rewrite(revive(treeSuspended)), treeSuspended))

// 3. Mutual recursion: the back edge depends on the root under the bare form, not under the suspended form.
const evenBody = (odd: Json) => union([struct([["_tag", lit("Zero")]]), struct([["_tag", lit("SuccE")], ["pred", odd]])])
const oddBody = (even: Json) => struct([["_tag", lit("SuccO")], ["pred", even]])
const mutualBare = (root: string) => doc(ref(root), { Even: evenBody(ref("Odd")), Odd: oddBody(ref("Even")) })
const mutualSuspended = (root: string) =>
  doc(ref(root), { Even: evenBody(suspend(ref("Odd"))), Odd: oddBody(suspend(ref("Even"))) })
const backEven = rewrite(revive(mutualBare("Even"))) as { references: Record<string, Json> }
const backOdd = rewrite(revive(mutualBare("Odd"))) as { references: Record<string, Json> }
observe("3a bare, root Even: rc.112 writes Even's body", backEven.references["Even"])
observe("3b bare, root Odd: rc.112 writes Even's body", backOdd.references["Even"])
expect("3c bare: the written bodies depend on the root", !isDeepStrictEqual(backEven.references, backOdd.references))
expect("3d suspended: a fixed point at either root",
  isDeepStrictEqual(rewrite(revive(mutualSuspended("Even"))), mutualSuspended("Even")) &&
  isDeepStrictEqual(rewrite(revive(mutualSuspended("Odd"))), mutualSuspended("Odd")))
expect("3e suspended: decodes 2 and refuses a wrong tag",
  decodes(revive(mutualSuspended("Even")), { _tag: "SuccE", pred: { _tag: "SuccO", pred: { _tag: "Zero" } } }) &&
  !decodes(revive(mutualSuspended("Even")), { _tag: "SuccE", pred: { _tag: "Zero" } }))

// 4. A name with no recursion stays a bare reference, used once or twice.
const userId = doc(struct([["owner", ref("UserId")], ["buyer", ref("UserId")]]), { UserId: nat })
expect("4a alias: a fixed point with bare references", isDeepStrictEqual(rewrite(revive(userId)), userId))

// 5. A Suspend at an edge outside any cycle is kept: rc.112 writes back what it was given.
const userIdSuspended = doc(struct([["owner", suspend(ref("UserId"))]]), { UserId: nat })
expect("5a a needless Suspend survives the round trip", isDeepStrictEqual(rewrite(revive(userIdSuspended)), userIdSuspended))

// 6. Recursion through Option (Peano), suspended at the cycle.
const peano = doc(ref("Peano"), { Peano: option(suspend(ref("Peano"))) })
expect("6a Peano through Option: a fixed point", isDeepStrictEqual(rewrite(revive(peano)), peano))

// 7. An unguarded table: rc.112 revives it, and decoding does not terminate normally.
const unguarded = doc(ref("Loop"), { Loop: union([ref("Loop"), str]) })
const loop = revive(unguarded)
observe("7a unguarded Loop = Loop | string, at \"a\"", decodeNote(loop, "a"))
observe("7b unguarded Loop = Loop | string, at 1", decodeNote(loop, 1))

// 8. rc.112's code of the suspended Tree and of the mutual pair.
const code = (json: Json) => {
  const document = SchemaRepresentation.toMultiDocument(SchemaRepresentation.fromJson(json))
  try {
    const c = SchemaRepresentation.toCodeDocument(document)
    return { codes: c.codes, nonRecursives: c.references.nonRecursives, recursives: c.references.recursives }
  } catch (e) { return `throws ${String(e).split("\n")[0]}` }
}
const plainTree = doc(ref("Tree"), { Tree: struct([["value", { _tag: "Number", checks: [] }], ["children", list(ref("Tree"))]]) })
observe("8a code of the bare Tree (no checks)", code(plainTree))
observe("8b code of the bare mutual pair", code(mutualBare("Even")))
observe("8c code of the bare Tree with the natural's checks, from the document", code(treeBare))

// 9. The bare document is a fixed point modulo the extended `N_S`, at every root.
expect("9a bare Tree", isDeepStrictEqual(rewriteR(revive(treeBare)), treeBare))
expect("9b bare mutual pair, root Even and root Odd",
  isDeepStrictEqual(rewriteR(revive(mutualBare("Even"))), mutualBare("Even")) &&
  isDeepStrictEqual(rewriteR(revive(mutualBare("Odd"))), mutualBare("Odd")))
const peanoBare = doc(ref("Peano"), { Peano: option(ref("Peano")) })
expect("9c bare Peano through Option", isDeepStrictEqual(rewriteR(revive(peanoBare)), peanoBare))

// 10. Two recursive names, one referring to the other outside any cycle (Grove -> Tree).
const groveDoc = (treeAt: (j: Json) => Json, back: (j: Json) => Json) => doc(ref("Grove"), {
  Tree: treeBody(back(ref("Tree"))),
  Grove: struct([["tree", treeAt(ref("Tree"))], ["next", option(back(ref("Grove")))]]) })
const id = (j: Json) => j
expect("10a bare Grove and Tree: a fixed point modulo the extended N_S",
  isDeepStrictEqual(rewriteR(revive(groveDoc(id, id))), groveDoc(id, id)))
expect("10b suspended within each cycle: a fixed point", isDeepStrictEqual(rewrite(revive(groveDoc(id, suspend))), groveDoc(id, suspend)))
const crossSuspended = rewrite(revive(groveDoc(suspend, suspend))) as { references: Record<string, Json> }
observe("10c suspended also at Grove -> Tree, Grove written back as", crossSuspended.references["Grove"])
observe("10d its reference table's keys", Object.keys(crossSuspended.references))

// 11. Three names on one cycle with a chord: A -> B -> C -> A and C -> B.
const tri = (at: (j: Json) => Json) => doc(ref("A"), {
  A: struct([["b", at(ref("B"))]]),
  B: struct([["c", at(ref("C"))]]),
  C: union([struct([["a", at(ref("A"))]]), struct([["b", at(ref("B"))]]), str]) })
expect("11a bare: a fixed point modulo the extended N_S", isDeepStrictEqual(rewriteR(revive(tri(id))), tri(id)))
const triSuspended = rewrite(revive(tri(suspend))) as { references: Record<string, Json> }
observe("11b suspended at every edge of the cycle: the reference table's keys", Object.keys(triSuspended.references))
expect("11c bare: decodes a C that closes the cycle", decodes(revive(tri(id)), { b: { c: { b: { c: "end" } } } }))

// 12. rc.112's code of bare documents, from rc.112's revival, transpiled and evaluated.
const revivedCode = (json: Json) => {
  const c = SchemaRepresentation.toCodeDocument(SchemaRepresentation.toMultiDocument(
    SchemaRepresentation.toRepresentation(revive(json).ast)))
  return { codes: c.codes, nonRecursives: c.references.nonRecursives, recursives: c.references.recursives }
}
const transpiler = new Bun.Transpiler({ loader: "ts" })
const evaluate = (code: ReturnType<typeof revivedCode>): Schema.Top => {
  const lines = [...code.nonRecursives.map(({ $ref, code }) => `const ${$ref} = ${code.runtime}`),
    ...Object.entries(code.recursives).map(([$ref, c]) => `const ${$ref} = ${c.runtime}`),
    `return ${code.codes[0]!.runtime}`]
  return new Function("Schema", transpiler.transformSync(lines.join(";\n"))) (Schema) as Schema.Top
}
const treeCode = revivedCode(treeBare)
observe("12a rc.112's code of the bare Tree", treeCode.recursives)
expect("12b that code, evaluated, writes the bare Tree modulo the extended N_S", isDeepStrictEqual(rewriteR(evaluate(treeCode)), treeBare))
const groveCode = revivedCode(groveDoc(id, id))
observe("12c rc.112's code of the bare Grove: Grove", groveCode.recursives["Grove"]!.runtime)
expect("12d that code, evaluated, writes the bare Grove modulo the extended N_S",
  isDeepStrictEqual(rewriteR(evaluate(groveCode)), groveDoc(id, id)))
observe("12e rc.112's code of the alias document", revivedCode(userId))

// 13. Schema code as a printer would write it: rc.112 allocates a reference by the identifier.
const natCode = Schema.Number.check(Schema.isInt()).check(Schema.isGreaterThanOrEqualTo(0))
type Tree = { readonly value: number; readonly children: ReadonlyArray<Tree> }
const TreeAnon = Schema.Struct({
  value: natCode, children: Schema.Array(Schema.suspend((): Schema.Codec<Tree> => TreeAnon)) })
observe("13a Tree code with no identifier: rc.112 names the reference", (rewrite(TreeAnon) as { representation: Json }).representation)
const TreeCode = Schema.Struct({
  value: natCode, children: Schema.Array(Schema.suspend((): Schema.Codec<Tree> => TreeCode)) }).annotate({ identifier: "Tree" })
expect("13b Tree code with its identifier: the bare Tree modulo the extended N_S", isDeepStrictEqual(rewriteR(TreeCode), treeBare))
const UserIdCode = natCode.annotate({ identifier: "UserId" })
expect("13c alias code with its identifier: the alias document",
  isDeepStrictEqual(rewrite(Schema.Struct({ owner: UserIdCode, buyer: UserIdCode })), userId))
observe("13d alias code with no identifier: the reference table",
  (rewrite(Schema.Struct({ owner: natCode, buyer: natCode })) as { references: Json }).references)

console.log(`PASS named-types documents: ${observations} observations`)
