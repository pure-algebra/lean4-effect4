/**
 * The guardedness walk's COST — PDD-3 break-pass finding F3.
 *
 * Packet: `library/cas/contracts/PDD-3.contract.md`, law L2a.
 *
 * The packet's `DECREASES` clause always read `|dom(R)| - |visited|`,
 * and until the fix pass neither host had a visited set: the search
 * re-walked every path, so a table whose entries each name the next one
 * TWICE cost `Θ(2ⁿ)`. The break pass measured 18 271 ms in TypeScript
 * at 23 acyclic entries and 302 915 ms in Lean at 25, doubling per
 * entry, on a 7 657-byte payload. This is the ingestion door for
 * foreign content, so the input is attacker-chosen and the door is
 * synchronous.
 *
 * The witness is that table — `Attack.lean` §5's `fanTable`, rebuilt
 * here — at a size the exponential walk cannot reach. The assertion is
 * WALL CLOCK, deliberately: there is no theorem about schedules, and
 * the only honest statement about a schedule is that the door came
 * back. Nothing here is timed inside Lean's kernel; the Lean witness is
 * the `#guard` on `fanOutTable 30` in `Cas/Schema/Guarded.lean`.
 *
 * The budget is loose on purpose — the memoized walk does about `2n`
 * edges and returns in single-digit milliseconds, so anything under a
 * second separates it from a walk that would not finish this century.
 */
import { expect, it } from "@effect/vitest"
import { Effect } from "effect"
import { Cas } from "../src/index.ts"
import { canonicalJson } from "../src/cas/Value.ts"

const M = Cas.Materialize
const utf8 = new TextEncoder()

/** The break pass's blowup table: `n + 1` entries, each one naming the
 * next TWICE, the last a plain string, rooted at the first. Acyclic, so
 * the door walks all of it and then ADMITS — which is what makes this a
 * door problem rather than a refusal problem. */
const fanTablePayload = (n: number): Uint8Array => {
  const references: Record<string, unknown> = {}
  for (let index = 0; index < n; index += 1) {
    const next = { _tag: "Reference", $ref: `n${index + 1}` }
    references[`n${index}`] = {
      _tag: "Objects",
      checks: [],
      indexSignatures: [],
      propertySignatures: ["x", "y"].map((name) => ({
        isMutable: false,
        isOptional: false,
        name: { type: "string", value: name },
        type: next,
      })),
    }
  }
  references[`n${n}`] = { _tag: "String", checks: [] }
  return utf8.encode(canonicalJson({
    revision: Cas.CanonicalSchema.Revision,
    value: { references, representation: { _tag: "Reference", $ref: "n0" } },
  }))
}

it.effect("the door settles a fan table the exponential walk cannot reach", () =>
  Effect.gen(function* () {
    const payload = fanTablePayload(40)
    const started = Date.now()
    // ADMITTED, and that is half the point: the table is acyclic, so
    // the door does the whole walk before it says yes.
    yield* M.fromPayload(payload)
    const elapsed = Date.now() - started
    expect(elapsed).toBeLessThan(1000)
  }).pipe(Effect.provide(Cas.layerMemoryLive)))

it.effect("the memo does not admit a cycle hiding behind a fan", () =>
  Effect.gen(function* () {
    // The same shape with the tail wired back to the head: every name is
    // reachable twice over, so a walk that memoized on ENTRY rather than
    // on the way back out would call the cycle settled.
    const text = new TextDecoder().decode(fanTablePayload(40))
    const document = JSON.parse(text) as {
      value: { references: Record<string, unknown> }
    }
    document.value.references["n40"] = { _tag: "Reference", $ref: "n0" }
    const outcome = yield* Effect.result(
      M.fromPayload(utf8.encode(canonicalJson(document as never))),
    )
    expect(outcome._tag).toBe("Failure")
    if (outcome._tag === "Failure") {
      expect(String((outcome.failure as Cas.ProjectionCodecFailure).issue))
        .toContain("unguardedCycle")
    }
  }).pipe(Effect.provide(Cas.layerMemoryLive)))
