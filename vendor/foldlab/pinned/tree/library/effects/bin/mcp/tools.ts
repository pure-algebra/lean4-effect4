/**
 * The six tools, as the manifest declares them.
 *
 * Two spellings sit beside each other in this file on purpose:
 *
 * - the SERVED TABLE (`servedTools`), the names, self-descriptions,
 *   and canonical schema codes `Cas/Backend/Mcp.lean` emits. It is not
 *   written here at all: `lake exe mcpspec` renders the same
 *   `Cas.Backend.Mcp.tools` list twice — once as
 *   `mcp/cas-tools.json`, once as the typed constant this module
 *   imports — so the table this host serves and the document it is
 *   gated against are two projections of one value. `manifest.ts`
 *   still compares them, byte for byte through the canonical printer,
 *   at boot; that gate is now defence in depth rather than the only
 *   thing standing between the host and a typo.
 *
 * - the CARRIER (`parameters`/`success`), the Effect Schema the
 *   handler actually decodes and encodes through. It is the estate's
 *   own — `Cas.ConformanceVector.VectorNode` for the node document,
 *   `Cas.ContentId` for addresses, `Cas.Byte` for the version and tag
 *   plane — so nothing here mints a shape. The carrier says what the
 *   code deliberately cannot: the manifest types a payload `String`
 *   because the code language has no byte code, and the carrier says
 *   which string — hex, `Schema.Uint8ArrayFromHex`, the one spelling
 *   the vectors, `cas show --json`, and the wire already share.
 *
 * The served table says WHAT is served; the carrier is HOW. Neither is
 * authoritative over the Lean estate.
 *
 * ## OWED — the `Ast → Schema` door
 *
 * The carriers below are still held to the codes by REVIEW, not by a
 * gate: nothing mechanically checks that `RunDocument` is the schema
 * `RunParams.schemaCode` describes. Closing that needs a door the
 * estate does not have — a total lowering from a canonical code to an
 * Effect Schema (or from a Schema back to a code) — and it is not
 * built here. `McpCarrier.test.ts` adds the honest check the present
 * pieces allow: every carrier round-trips the wire documents the
 * handlers actually see.
 */
import { Schema } from "effect"
import { Tool, Toolkit } from "effect/unstable/ai"
import { Cas } from "../../src/index.ts"
import {
  McpToolCodes,
  McpToolDescriptions,
} from "../../src/cas/generated/McpToolCodes.ts"
import type { ServedTool } from "./manifest.ts"

/* ── the carrier schemas ─────────────────────────────────────────── */

/** An address, alone: the params of `cas_load` and `cas_publish_root`,
 * and the reply of `cas_put`. */
export const AddressDocument = Schema.Struct({ address: Cas.ContentId })

/** The empty document: `cas_list_roots`' params and
 * `cas_publish_root`'s reply. A publication answers nothing because
 * the store answers nothing — `RootStore.publish` is `void` and
 * idempotent.
 *
 * Spelled as a record of nothing rather than a struct of no fields:
 * `Schema.Struct({})` projects to `anyOf: [object, array]` in JSON
 * Schema, which is not an object schema and is not what an MCP tool's
 * input may be. This is Effect's own spelling for the case
 * (`Tool.EmptyParams`), and it projects to a plain empty object. */
export const EmptyDocument = Schema.Record(Schema.String, Schema.Never)

/** The published roots. */
export const RootsDocument = Schema.Struct({
  roots: Schema.Array(Cas.ContentId),
})

/** One operand of a code point: the index of an earlier instruction's
 * answer, or a literal content address.
 *
 * Both arms, since queue item 22. The two projection theorems that used
 * to say the document COULD NOT spell a literal or a load have flipped
 * (`RunOperand.ofPIn_lit`, `RunInstruction.ofPLine_load`) and collapsed
 * into one totality theorem — `ofPProg_isSome`, every well-formed table
 * has a document — so the carrier grows to match. A literal operand is
 * what lets a program name stored content, which is what lets a program
 * be run by address at all.
 *
 * A derived union's mode is part of its identity, so this is
 * `Schema.Union([...], { mode: "oneOf" })` and the members are in the
 * canonical order the deriving handler spells. */
export const RunOperand = Schema.Union([
  Schema.Struct({
    _tag: Schema.Literal("answer"),
    index: Schema.Int.check(Schema.isGreaterThanOrEqualTo(0)),
  }),
  Schema.Struct({
    _tag: Schema.Literal("literal"),
    addressHex: Cas.ContentId,
  }),
], { mode: "oneOf" })

/** One straight-line reference: an expected kind tag and the operand
 * naming what it points at. */
export const RunReference = Schema.Struct({
  expectedTag: Cas.Byte,
  source: RunOperand,
})

/** One instruction: a put whose references name operands, or a load of
 * an operand. The payload arrives as hex — the field is named
 * `payloadHex` in the document itself. */
export const RunInstruction = Schema.Union([
  Schema.Struct({
    _tag: Schema.Literal("load"),
    source: RunOperand,
  }),
  Schema.Struct({
    _tag: Schema.Literal("put"),
    version: Cas.Byte,
    tag: Cas.Byte,
    payloadHex: Schema.Uint8ArrayFromHex,
    refs: Schema.Array(RunReference),
  }),
], { mode: "oneOf" })

/** A straight-line program, submitted inline.
 *
 * It is no longer SELF-CONTAINED and the word was struck rather than
 * softened. A document whose operands only name earlier answers depends
 * on nothing but itself; one that can name a literal address, or load
 * one, is asking about what this store already holds. So a run's
 * meaning is relative to its starting word — which, on this host, is
 * the store. Two hosts handed the same document over different stores
 * can honestly answer different words, and that is the semantics, not
 * a defect. */
export const RunDocument = Schema.Struct({
  instructions: Schema.Array(RunInstruction),
})

/** The run-by-address params: the address of a `cont` node, and
 * nothing else. A program is content; its address is its identity;
 * everything else about it is reachable by loading. */
export const RunRefDocument = Schema.Struct({ root: Cas.ContentId })

/** The word: the run's history in admission order, one address per
 * instruction. */
export const WordDocument = Schema.Struct({
  word: Schema.Array(Schema.Struct({ address: Cas.ContentId })),
})

/* ── the refusal ─────────────────────────────────────────────────── */

/**
 * What a tool answers when the store refuses. The clause is the
 * library's own error tag and the detail is the CLI's own rendering,
 * so a refusal reads the same whether it arrives down a pipe or out of
 * a shell — one vocabulary, per the vocabulary law. Declared as the
 * tools' failure schema, which is what makes the MCP layer report it
 * as a tool error carrying this message instead of swallowing it as an
 * internal error.
 */
export class Refused extends Schema.TaggedError<Refused>()(
  "mcp/Refused",
  { clause: Schema.String, detail: Schema.String },
) {
  override get message(): string {
    return this.detail
  }
}

/* ── the tools ───────────────────────────────────────────────────── */

export const casPut = Tool.make("cas_put", {
  description: McpToolDescriptions.cas_put,
  parameters: Cas.ConformanceVector.VectorNode,
  success: AddressDocument,
  failure: Refused,
  dependencies: [Cas.Store],
})
  // Admission is content-addressed: the same node admitted twice
  // answers the same address and changes nothing, so the write is
  // idempotent and never destructive.
  .annotate(Tool.Readonly, false)
  .annotate(Tool.Destructive, false)
  .annotate(Tool.Idempotent, true)
  .annotate(Tool.OpenWorld, false)

export const casLoad = Tool.make("cas_load", {
  description: McpToolDescriptions.cas_load,
  parameters: AddressDocument,
  success: Cas.ConformanceVector.VectorNode,
  failure: Refused,
  dependencies: [Cas.Loader],
})
  .annotate(Tool.Readonly, true)
  .annotate(Tool.Destructive, false)
  .annotate(Tool.Idempotent, true)
  .annotate(Tool.OpenWorld, false)

export const casRun = Tool.make("cas_run", {
  description: McpToolDescriptions.cas_run,
  parameters: RunDocument,
  success: WordDocument,
  failure: Refused,
  dependencies: [Cas.Store],
})
  .annotate(Tool.Readonly, false)
  .annotate(Tool.Destructive, false)
  .annotate(Tool.Idempotent, true)
  .annotate(Tool.OpenWorld, false)

export const casRunRef = Tool.make("cas_run_ref", {
  description: McpToolDescriptions.cas_run_ref,
  parameters: RunRefDocument,
  success: WordDocument,
  failure: Refused,
  dependencies: [Cas.Store],
})
  // Running a stored program admits the nodes the program puts, which
  // is exactly as idempotent as `cas_run` on the same table: the same
  // program answers the same addresses, and a second run is a run of
  // duplicate puts, which are inert.
  .annotate(Tool.Readonly, false)
  .annotate(Tool.Destructive, false)
  .annotate(Tool.Idempotent, true)
  .annotate(Tool.OpenWorld, false)

export const casPublishRoot = Tool.make("cas_publish_root", {
  description: McpToolDescriptions.cas_publish_root,
  parameters: AddressDocument,
  success: EmptyDocument,
  failure: Refused,
  dependencies: [Cas.Loader, Cas.RootStore],
})
  // The published set only grows and publication is idempotent
  // (`RootStoreShape.publish`), so nothing here can remove a root.
  .annotate(Tool.Readonly, false)
  .annotate(Tool.Destructive, false)
  .annotate(Tool.Idempotent, true)
  .annotate(Tool.OpenWorld, false)

export const casListRoots = Tool.make("cas_list_roots", {
  description: McpToolDescriptions.cas_list_roots,
  parameters: EmptyDocument,
  success: RootsDocument,
  failure: Refused,
  dependencies: [Cas.RootStore],
})
  .annotate(Tool.Readonly, true)
  .annotate(Tool.Destructive, false)
  .annotate(Tool.Idempotent, true)
  .annotate(Tool.OpenWorld, false)

/**
 * The toolkit, in the manifest's order.
 *
 * ## SEAM — `cas_emit_layers` (G6-a)
 *
 * When `SystemNode` + `EmitLayer` land, the verb is ONE row in
 * `Mcp.lean:298-319` plus a `manifestVersion` bump, and on this side:
 * one `Tool.make` below, one handler in `handlers.ts`, and
 * `implementedManifestVersion` following the bump. The served row
 * arrives by regenerating — `lake exe mcpspec` emits it into
 * `McpToolCodes.ts` — so nothing in this package writes it, and the
 * boot gate refuses a host that serves a tool the manifest lacks.
 *
 * ## SEAM — the CODE REGISTER (operator ruling, 2026-08-29)
 *
 * The five tools below are the FLOOR, not the interface. The ruled
 * default register is code: a client submits an estate document — a
 * schema code through the ingest door, a program document through
 * `Lift`/`decodeLift`, a described value like `SystemNode` — or a
 * TypeScript module composed against the emitted typed surfaces, and
 * the host routes it to the doors that already exist.
 *
 * Nothing in this file's shape has to change for that. A code register
 * is one more row of the same kind: a `Tool.make` whose `parameters`
 * carry the submitted document (or module text) and whose handler
 * dispatches to `Cas.CanonicalSchema.admitNode`, `Cas.Materialize`, or
 * the `Cas.Store` doors the handlers here already speak — the same
 * services, the same typed refusals, the same `Refused` clause on the
 * wire. What the register does NOT get is a second trust surface: the
 * gates carry all trust, so a submitted document earns admission the
 * way every other node does — at put, by decode-back, by word
 * equality — and a code register that bypassed them would be the
 * defect, not the feature.
 *
 * Three things it needs that this lane must not invent:
 *
 * 1. THE MANIFEST ROW. `Mcp.lean` is the authority on tool names,
 *    params, and results, and its rows are ruled. The row (and the
 *    `manifestVersion` bump it forces) is Lean's; the boot gate here
 *    refuses any host that serves a tool the manifest does not carry,
 *    which is exactly the protection that makes adding it safe.
 * 2. DISPATCH. Which door a submitted document goes to is decided by
 *    the document's own kind, not by a flag — the estate already has
 *    the kind registry that decides it.
 * 3. SANDBOXING, for the TypeScript half only. A submitted DOCUMENT
 *    needs none: it is data, and admission is its gate. A submitted
 *    MODULE is execution, and this host runs in the operator's own
 *    process over the operator's own store — so the isolation story
 *    (a worker, a fresh runtime, a capability-restricted context, and
 *    what the module is allowed to import) is a ruling this lane did
 *    not take and did not prejudge.
 */
export const casToolkit = Toolkit.make(
  casPut,
  casLoad,
  casRun,
  casRunRef,
  casPublishRoot,
  casListRoots,
)

/**
 * The served table in the manifest's vocabulary — what the boot gate
 * compares. The order is the manifest's order, and it is part of what
 * is compared.
 *
 * It IS the emitted table, re-exported under the name the host and its
 * gate already use. What this module still owns is the join above:
 * that `cas_run`'s row is served by `RunDocument` and not by some
 * other carrier. The row itself is no longer anyone's transcription.
 */
export const servedTools: ReadonlyArray<ServedTool> = McpToolCodes

/** What a forked pair of name sets resolves to. It is a string literal
 * rather than `never` so the compiler's own message at the use site
 * says which invariant broke instead of `not assignable to never`. */
type ForkedToolNames =
  "the emitted MCP tool names and the registered toolkit names have forked"

/** Two name sets that must be one set. Mutual assignability IS equality
 * for unions of string literals, and it is checked in the alias body
 * because TypeScript refuses type parameters that constrain each
 * other. */
type SameNames<Emitted, Registered> = [Emitted] extends [Registered]
  ? [Registered] extends [Emitted] ? Emitted : ForkedToolNames
  : ForkedToolNames

/**
 * A served tool's name, as a type.
 *
 * `McpToolCodes` is a `ReadonlyArray<McpToolRow>` and a row's `name` is
 * `string`, so the emitted table cannot give a name union on its own.
 * `McpToolDescriptions` can: it is the same rows keyed BY name, so its
 * key set is the emitted name set, spelled by `lake exe mcpspec` and
 * byte-identity-gated like the rest of the generated module.
 *
 * The definition is also the gate-join. Passing that key set through
 * `SameNames` against the toolkit's own registered keys makes this
 * alias fail to resolve unless the two agree, so a tool served without
 * an emitted row — or an emitted row nothing serves — is a type error
 * here rather than a boot-time comparison failure in `manifest.ts` or,
 * worse, a name that only telemetry ever sees.
 *
 * What it fixes at the use site: `bin/mcp/handlers.ts` labels every
 * store-touching call with its tool name for the log annotation and
 * the `cas.host.calls` counter, and those labels were six free-standing
 * string literals. Typed as this, a name outside the emitted set does
 * not compile. What it still does NOT catch is a name that is emitted
 * but wrong for the handler it labels (`cas_load` written inside the
 * `cas_put` arm); binding each label to its own handler key needs the
 * table built through a mapped helper, which would restructure
 * `layerHandlers` for a mislabel that no gate has ever seen.
 */
export type ServedToolName = SameNames<
  keyof typeof McpToolDescriptions,
  keyof typeof casToolkit.tools
>
