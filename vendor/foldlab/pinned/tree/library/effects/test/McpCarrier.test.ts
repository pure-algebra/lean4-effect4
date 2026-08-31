/**
 * The CARRIERS, held to the wire.
 *
 * `McpHost.test.ts` covers two claims: that the served table is the
 * emitted manifest's, and that the tools behave like the store's own
 * verbs over a real protocol. This file covers the third, and it is
 * the one the host lane named as resting on review.
 *
 * A served tool has two halves. The manifest half — name,
 * self-description, params code, result code — is now GENERATED on
 * both sides (`lake exe mcpspec` renders `Cas.Backend.Mcp.tools` as
 * `mcp/cas-tools.json` and as `src/cas/generated/McpToolCodes.ts`), so
 * the boot gate compares two projections of one value. The carrier
 * half — the Effect Schema each `Tool.make` actually decodes requests
 * with and encodes replies with — is gated by nothing.
 *
 * ## OWED — the `Ast → Schema` door
 *
 * What would close it is a door the estate does not have: a total
 * lowering from a canonical schema code to an Effect Schema (or a
 * total raising the other way), so that `casRun.parametersSchema`
 * could be CHECKED against `RunParams.schemaCode` rather than reviewed
 * against it. `Cas/Backend/EmitAst.lean` lowers a code to Effect
 * Schema SOURCE for the generated mirrors, which is the same journey
 * one register down — a door would have to make that a value-level
 * comparison the host can run at boot, and decide what it means for a
 * carrier to say MORE than its code (the payload the manifest types
 * `String` and the carrier types hex bytes is exactly that case, and
 * it is intended, not drift). Neither is settled, and neither is
 * invented here.
 *
 * ## What this file does instead
 *
 * The honest check the present pieces allow: every tool's carrier is
 * exercised on the wire documents the handlers actually see, pinned as
 * LITERALS. Each fixture is decoded through the tool's own
 * `parametersSchema`/`successSchema` and encoded back, and the
 * round-trip must return the literal it started from. That does not
 * prove the carrier is the code; it proves the carrier accepts, and
 * faithfully returns, the exact wire vocabulary the manifest declares
 * — which is the drift a silent carrier edit would produce first.
 *
 * The literals are the same documents `McpHost.test.ts` sends over the
 * protocol, spelled once here so a carrier change that breaks them
 * fails at the schema and not three layers up in a JSON-RPC frame.
 */
import { describe, expect, it } from "@effect/vitest"
import { Schema } from "effect"
import { Cas } from "../src/index.ts"
import {
  casListRoots,
  casLoad,
  casPublishRoot,
  casPut,
  casRun,
} from "../bin/mcp/tools.ts"

/** "hello", as the node document spells a payload. */
const helloHex = "68656c6c6f"

/** Two addresses in the store's own spelling — 32 bytes of hex. A
 * carrier that stopped being `Cas.ContentId` would take a shorter one,
 * which is why they are spelled at full width here. */
const addressA = "a".repeat(64)
const addressB = "b".repeat(64)

/** One node document, exactly as `cas_put` receives it and `cas_load`
 * answers it: the ONE node wire shape across vectors, replay, and MCP. */
const nodeWire = {
  version: Cas.SchemeVersion,
  tag: 1,
  payload: helloHex,
  refs: [] as ReadonlyArray<{ readonly expectedTag: number; readonly id: string }>,
}

/** The same document carrying a reference — the half of the node shape
 * an empty `refs` never exercises. */
const linkedNodeWire = {
  version: Cas.SchemeVersion,
  tag: 9,
  payload: "",
  refs: [{ expectedTag: 1, id: addressA }],
}

/** A four-instruction straight-line program, exercising every arm the
 * document has since queue item 22: a value node, a tree node naming
 * the first answer BY INDEX, a tree node naming a LITERAL ADDRESS, and
 * a LOAD. The last two had no spelling at all before the growth. */
const runWire = {
  instructions: [
    {
      _tag: "put",
      version: Cas.SchemeVersion,
      tag: 1,
      payloadHex: helloHex,
      refs: [],
    },
    {
      _tag: "put",
      version: Cas.SchemeVersion,
      tag: 9,
      payloadHex: "",
      refs: [{ expectedTag: 1, source: { _tag: "answer", index: 0 } }],
    },
    {
      _tag: "put",
      version: Cas.SchemeVersion,
      tag: 9,
      payloadHex: "",
      refs: [{
        expectedTag: 1,
        source: { _tag: "literal", addressHex: addressA },
      }],
    },
    { _tag: "load", source: { _tag: "answer", index: 0 } },
  ],
}

/** One fixture: a carrier, and a wire document that carrier must take
 * and give back unchanged. */
interface RoundTrip {
  readonly what: string
  readonly schema: Schema.Codec<unknown, unknown>
  readonly wire: unknown
}

/** Every tool's two carriers, against the wire each one sees. The
 * schemas are read off the TOOLS, not off the exported consts they
 * were built from: what is under test is what the handler decodes
 * with. */
const roundTrips: ReadonlyArray<RoundTrip> = [
  {
    what: "cas_put params — a node document",
    schema: casPut.parametersSchema,
    wire: nodeWire,
  },
  {
    what: "cas_put params — a node document with a reference",
    schema: casPut.parametersSchema,
    wire: linkedNodeWire,
  },
  {
    what: "cas_put result — the content address",
    schema: casPut.successSchema,
    wire: { address: addressA },
  },
  {
    what: "cas_load params — an address",
    schema: casLoad.parametersSchema,
    wire: { address: addressA },
  },
  {
    what: "cas_load result — the node as stored",
    schema: casLoad.successSchema,
    wire: linkedNodeWire,
  },
  {
    what: "cas_run params — a straight-line program",
    schema: casRun.parametersSchema,
    wire: runWire,
  },
  {
    what: "cas_run result — the word, in admission order",
    schema: casRun.successSchema,
    wire: { word: [{ address: addressA }, { address: addressB }] },
  },
  {
    what: "cas_publish_root params — the address published",
    schema: casPublishRoot.parametersSchema,
    wire: { address: addressB },
  },
  {
    what: "cas_publish_root result — a publication answers nothing",
    schema: casPublishRoot.successSchema,
    wire: {},
  },
  {
    what: "cas_list_roots params — no question to ask",
    schema: casListRoots.parametersSchema,
    wire: {},
  },
  {
    what: "cas_list_roots result — the published roots",
    schema: casListRoots.successSchema,
    wire: { roots: [addressA, addressB] },
  },
]

describe("the tool carriers round-trip the wire the handlers see", () => {
  for (const { schema, what, wire } of roundTrips) {
    it(what, () => {
      const decoded = Schema.decodeUnknownSync(schema)(wire)
      expect(Schema.encodeUnknownSync(schema)(decoded)).toEqual(wire)
    })
  }

  // The carriers say MORE than the codes do, and that is the point of
  // having both: the manifest types a payload `String` because the
  // code language has no byte code, and the carrier says WHICH string.
  // A carrier that stopped refusing these would be accepting documents
  // the estate's own doors would not.
  it("refuses a payload that is not hex", () => {
    expect(() =>
      Schema.decodeUnknownSync(casPut.parametersSchema)({ ...nodeWire, payload: "nothex" })
    ).toThrow()
  })

  it("refuses an address that is not a content address", () => {
    expect(() =>
      Schema.decodeUnknownSync(casLoad.parametersSchema)({ address: "deadbeef" })
    ).toThrow()
  })

  it("refuses a reference that names an address instead of an answer", () => {
    expect(() =>
      Schema.decodeUnknownSync(casRun.parametersSchema)({
        instructions: [{
          version: Cas.SchemeVersion,
          tag: 9,
          payloadHex: "",
          refs: [{ expectedTag: 1, id: addressA }],
        }],
      })
    ).toThrow()
  })
})
