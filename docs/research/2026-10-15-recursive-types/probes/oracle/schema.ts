// The Schema face of a recursive declaration, on rc.112 (decisions row 400's probe).
// Run from this folder: `bun schema.ts` (node_modules links to harness/truth's pinned install).
import { Schema, SchemaRepresentation } from "effect"

interface Tree { readonly _tag: "leaf" }
interface Node { readonly _tag: "node"; readonly children: ReadonlyArray<Tree | Node>; readonly label: string }
type T = Tree | Node

// Lean's `Tree` declaration as rc.112 writes it: a union of tagged structs, the recursive
// occurrence under `Schema.suspend`, the declaration named by its identifier.
const TreeSchema: Schema.Codec<T> = Schema.Union([
  Schema.Struct({ _tag: Schema.Literal("leaf") }),
  Schema.Struct({
    _tag: Schema.Literal("node"),
    children: Schema.Array(Schema.suspend((): Schema.Codec<T> => TreeSchema)),
    label: Schema.String,
  }),
]).annotate({ identifier: "Tree" })

// the probe's sample values (Recursive.lean, `tree3` and `treeBad`), as their JSON
const tree3 = { _tag: "node", label: "root", children: [{ _tag: "leaf" },
  { _tag: "node", label: "mid", children: [{ _tag: "leaf" }] }, { _tag: "leaf" }] }
const treeBad = { _tag: "node", label: "root", children: [{ _tag: "leaf" },
  { _tag: "node", label: "mid", children: ["oops"] }] }

const decode = Schema.decodeUnknownSync(TreeSchema)
const ok = (x: unknown) => { try { decode(x); return true } catch { return false } }
console.log("decode tree3:", ok(tree3), "treeBad:", ok(treeBad))

// how rc.112 persists the recursion: the document's root and its references table
const doc = SchemaRepresentation.toRepresentation(TreeSchema.ast)
const json = SchemaRepresentation.toJson(doc)
console.log(JSON.stringify(json, null, 1))

// the persisted document revived, then the same two decodes
const revived = SchemaRepresentation.fromRepresentation(SchemaRepresentation.fromJson(json), { revivers: [] })
const decode2 = Schema.decodeUnknownSync(revived as Schema.Codec<unknown>)
const ok2 = (x: unknown) => { try { decode2(x); return true } catch { return false } }
console.log("revived decode tree3:", ok2(tree3), "treeBad:", ok2(treeBad))
