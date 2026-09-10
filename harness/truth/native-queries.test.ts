/** S3 cause/exit query controls against the production prelude, rc.112. */
import { expect, test } from "bun:test"
import { Cause, Exit, Option } from "effect"
import { causeIsFail, causeIsDie, causeIsInterrupt, causeError } from "./prelude.ts"

test("cause query adapter covers success, empty cause and separate reason categories", () => {
  const cases = [
    { value: Exit.succeed(7), expected: [false, false, false] },
    { value: Cause.empty, expected: [false, false, false] },
    { value: Cause.fail("lost"), expected: [true, false, false] },
    { value: Cause.die("defect"), expected: [false, true, false] },
    { value: Cause.interrupt(1), expected: [false, false, true] },
  ]
  for (const { value, expected } of cases) {
    expect([causeIsFail(value), causeIsDie(value), causeIsInterrupt(value)]).toEqual(expected)
  }
})

test("mixed cause and failed exit expose the first error and all reason categories", () => {
  const cause = Cause.fromReasons([
    Cause.makeInterruptReason(1), Cause.makeFailReason("first"),
    Cause.makeDieReason("defect"), Cause.makeFailReason("second"),
  ])
  for (const input of [cause, Exit.failCause(cause)]) {
    expect([causeIsFail(input), causeIsDie(input), causeIsInterrupt(input)]).toEqual([true, true, true])
    expect(causeError(input)).toEqual(Option.some("first"))
  }
})

test("no Fail gives none, while the ordinary string boom remains an ordinary payload", () => {
  expect(causeError(Exit.succeed(1))).toEqual(Option.none())
  expect(causeError(Cause.combine(Cause.die("defect"), Cause.interrupt(1)))).toEqual(Option.none())
  expect(causeError(Cause.fail("boom"))).toEqual(Option.some("boom"))
})
