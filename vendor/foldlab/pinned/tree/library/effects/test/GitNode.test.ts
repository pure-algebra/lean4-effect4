/**
 * The git sort (0x47): a git object as store content, its payload the
 * loose-object preimage — so the git SHA-1 identity is DERIVABLE from
 * the payload, never declared. This suite recomputes it: the
 * git-pin-commit vector's payload must hash to the lean4-tree-sitter
 * pin commit recorded in the stand-up receipt. A provenance pin is
 * now store content with dual identity — store address (replayed by
 * the vector suites) and git id (checked here).
 */
import { expect, it } from "@effect/vitest"
import { createHash } from "node:crypto"
import { Effect } from "effect"
import { GitKindTag } from "../src/internal/kindTags.ts"
import { layerDiskFs } from "./fixtures/diskFs.ts"
import { readFixtureString } from "./fixtures/read.ts"

const PIN = "3a57f55e1401484251cfe80e26583d9ed94c82c8"

it.effect("the git node's payload sha1s to the pinned commit id", () =>
  Effect.gen(function* () {
    const vector = JSON.parse(
      yield* readFixtureString("../cas/vectors/git-pin-commit.json").pipe(Effect.orDie),
    ) as { word: ReadonlyArray<{ node: { tag: number; payload: string } }> }
    expect(vector.word.length).toBe(1)
    const node = vector.word[0]!.node
    expect(node.tag).toBe(GitKindTag)
    const payload = Buffer.from(node.payload, "hex")
    const header = payload.subarray(0, payload.indexOf(0))
    const content = payload.subarray(payload.indexOf(0) + 1)
    expect(header.toString("utf8")).toBe(`commit ${content.length}`)
    expect(createHash("sha1").update(payload).digest("hex")).toBe(PIN)
  }).pipe(Effect.provide(layerDiskFs)))
