import { expect, it } from "@effect/vitest"
import { findKillWitnesses } from "./harness.ts"

it("self-test, never conformance evidence: a structurally wrong in-memory row is red", () => {
  const witnesses = findKillWitnesses(
    [{ case: "wrong-row", expect: { value: 1 } }],
    () => ({ value: 2 }),
  )
  expect(witnesses).toEqual(["wrong-row"])
})
