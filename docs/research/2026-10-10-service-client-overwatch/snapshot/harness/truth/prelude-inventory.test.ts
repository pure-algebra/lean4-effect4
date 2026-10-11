import { expect, test } from "bun:test"
import { atomNames } from "../../ts/eff/profile.gen.ts"
import { selfTestCases } from "./prelude.ts"
import { preludeInventoryFailures } from "./prelude-inventory.ts"

test("actual prelude cases cover every actual generated atom and execute correctly", () => {
  expect(preludeInventoryFailures(atomNames, selfTestCases)).toEqual([])
  for (const entry of selfTestCases) expect(entry.apply()).toBe(entry.expected)
})

test("removing each atom's cases is independently detected", () => {
  for (const atom of atomNames) {
    const failures = preludeInventoryFailures(atomNames, selfTestCases.filter(c => c.atom !== atom))
    expect(failures).toEqual([`atom ${atom} is in the profile's atom set and has no prelude self-test case`])
  }
})

test("a new inventory entry cannot be hidden by an unrelated case", () => {
  expect(preludeInventoryFailures([...atomNames, "omitted-control"], selfTestCases)).toEqual([
    "atom omitted-control is in the profile's atom set and has no prelude self-test case",
  ])
})
