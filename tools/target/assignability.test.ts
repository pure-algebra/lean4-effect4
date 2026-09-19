import { expect, test } from "bun:test"
import { classify, readVectors, render } from "./assignability.ts"
import type { PairObservation } from "./oracle.ts"

const vector = (over: Partial<ReturnType<typeof readVectors>[number]> = {}) => ({
  id: "t/0-1", left: '{"_tag":"nat"}', right: '{"_tag":"string"}',
  renderLeft: "number", renderRight: "string",
  subLR: false, subRL: false, mutantLR: false, mutantRL: false, ...over,
})
const answer = (lr: boolean, rl: boolean, over: Partial<PairObservation> = {}): PairObservation => ({
  id: "t/0-1", left: "number", right: "string", leftText: "number", rightText: "string",
  leftToRight: { assignable: lr, statement: lr }, rightToLeft: { assignable: rl, statement: rl },
  issues: [], diagnostics: [], ...over,
})

test("the four verdicts follow the direction of the disagreement, not the pair's name", () => {
  expect(classify(vector(), answer(false, false)).verdict).toBe("agree")
  // the order refuses what the target accepts: sound, not complete
  expect(classify(vector(), answer(true, false)).verdict).toBe("incomplete")
  // the order accepts what the target refuses: the direction that must never happen
  expect(classify(vector({ subLR: true }), answer(false, false)).verdict).toBe("defect")
  // one target spelling for two types is a cut, and it is decided by the rendered text
  expect(classify(vector({ renderRight: "number" }), answer(true, true)).verdict).toBe("cut")
  // ... but only when the two types really are different
  expect(classify(vector({ left: '{"_tag":"nat"}', right: '{"_tag":"nat"}', renderRight: "number" }), answer(true, true)).verdict).toBe("incomplete")
  // an unanswered pair is never an agreement
  expect(classify(vector(), answer(false, false, { issues: [{ code: "pair-diagnostic", message: "TS2304" }] })).verdict).toBe("refused")
  expect(classify(vector(), { ...answer(false, false), leftToRight: { assignable: null, statement: null } }).verdict).toBe("refused")
})

test("the two readings of a direction are reported, never conflated", () => {
  const split = answer(false, false, { leftToRight: { assignable: true, statement: false } })
  const row = classify(vector(), split)
  expect(row.verdict).toBe("agree")
  expect(row.note).toContain("disagree")
  expect(row.assignableLR).toBe(true)
  expect(row.statementLR).toBe(false)
})

test("the vectors are read exactly, and the table keeps every column", () => {
  const text = "# comment\nt/0-1\t{\"_tag\":\"nat\"}\t{\"_tag\":\"string\"}\tnumber\tstring\tfalse\tfalse\ttrue\tfalse\n"
  const [read] = readVectors(text)
  expect(read).toEqual(vector({ mutantLR: true }))
  expect(() => readVectors("# only a comment\n")).toThrow("no pairs")
  expect(() => readVectors("a\tb\tc\n")).toThrow("9 columns")
  expect(() => readVectors("t\ta\tb\tc\td\tyes\tfalse\tfalse\tfalse\n")).toThrow("boolean")
  const table = render([classify(vector(), answer(false, false))], "7.0.0-dev")
  expect(table.split("\n")[6]).toContain("t/0-1\tnumber\tstring\tfalse\tfalse\tfalse\tfalse\tfalse\tfalse\tagree")
  expect(table).toContain("7.0.0-dev")
})
