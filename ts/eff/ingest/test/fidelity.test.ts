import { test, expect } from "bun:test"
import { sourceModule } from "../fidelity/source.ts"
import { compareObserved } from "../fidelity/roundtrip.ts"
import type { Observed } from "../fidelity/fidelity-contract.ts"
const observed = (exit: unknown, schedule: string[] = ["started 0", "exited 0 success"], parked = false): Observed => ({ status: "observed", effect: "4.0.0-rc.112", timeoutMs: 300, observation: { exit, schedule, parked } })
test("fidelity compares payloads and schedules, and cannot-run never agrees", () => {
  expect(compareObserved(observed({ success: 1 }), observed({ success: 2 })).status).toBe("disagree")
  expect(compareObserved(observed({ failure: { reasons: [{ die: "one" }] } }), observed({ failure: { reasons: [{ die: "two" }] } })).status).toBe("disagree")
  expect(compareObserved(observed({ success: 1 }), observed({ success: 1 }, ["started 0", "parked 0", "exited 0 success"])).status).toBe("disagree")
  expect(compareObserved({ status: "could-not-run", error: "timeout" }, { status: "could-not-run", error: "timeout" }).status).toBe("could-not-run")
  expect(compareObserved(observed(null, [], true), observed(null, [], false)).status).toBe("disagree")
})
test("fidelity retains the existing scheduled-row policy only", () => {
  expect(compareObserved(observed({ success: 1 }), observed({ success: 1 }, ["started 0", "scheduled 0 0", "exited 0 success"])).status).toBe("agree")
})
test("original declarations remain verbatim; foreign module dependencies are excluded", () => {
  const source = 'import { Effect } from "effect"; const p = Effect.succeed(42)'
  const module = sourceModule(source, "p.ts"), exposed = module.expose("p")
  expect(module.foreign).toEqual([])
  expect(exposed.source.startsWith(source + "\n")).toBe(true)
  expect(exposed.source).toContain(`export { p as ${exposed.name} }`)
  expect(sourceModule('import type { X } from "elsewhere"; export * from "node:fs"; const x = import("./local")', "p.ts").foreign).toEqual(["./local", "elsewhere", "node:fs"])
  expect(sourceModule('const x = require(name)', "p.ts").foreign).toEqual(["<computed module>"])
  expect(() => module.expose("Effect.runPromise#0")).toThrow("without changing execution")
})

test("top-level runtime entry arguments execute through the recorder entry", () => {
  const source = 'import { Effect } from "effect"; Effect.runSyncExit(Effect.succeed(42));'
  const start = source.indexOf("Effect.succeed(42)")
  const exposed = sourceModule(source, "entry.ts").expose("Effect.runSyncExit#0", 0, { start, end: start + "Effect.succeed(42)".length })
  expect(exposed.source).toContain(`export const ${exposed.name} = (Effect.succeed(42));`)
  expect(exposed.source).not.toContain("Effect.runSyncExit(")
})
