// Seat B: one bun run. Decodes the slice instance with the proposed schema, then red controls,
// each a one-field mutation that must be refused, and one control that shows the default
// decoder strips an excess key (why the checker decodes with onExcessProperty: "error").
import * as Schema from "/Users/pooks/Dev/lean4-effect4/ts/eff/node_modules/effect/dist/Schema.js"
import { SemanticsReport, decodeSemanticsReport } from "./semantics.mts"
import slice from "./slice.json"

type Row = { name: string; accepted: boolean; expected: boolean; agrees: boolean; error: string | null }
const results: Array<Row> = []
const clone = (): any => JSON.parse(JSON.stringify(slice))
function check(name: string, value: unknown, expected: boolean, decode: (u: unknown) => unknown = decodeSemanticsReport) {
  let accepted = false
  let error: string | null = null
  try { decode(value); accepted = true } catch (e) { error = String(e).slice(0, 400) }
  results.push({ name, accepted, expected, agrees: accepted === expected, error })
}

check("green: the slice instance", clone(), true)
{ const v = clone(); v.timestamp = "2026-10-01T19:00:00Z"; check("red: wall-clock key at the root", v, false) }
{ const v = clone(); v.timestamp = "2026-10-01T19:00:00Z"; check("default decoder strips the wall-clock key (accepted)", v, true, Schema.decodeUnknownSync(SemanticsReport)) }
{ const v = clone(); v.claims[0].concept = "store-typing"; check("red: dangling concept link", v, false) }
{ const v = clone(); v.claims[1].id = "seq-typed"; check("red: duplicate claim id", v, false) }
{ const v = clone(); delete v.claims[0].status.witness; check("red: proved without a witness", v, false) }
{ const v = clone(); v.claims[0].status.witness.name = "seq typed"; check("red: malformed nested name", v, false) }
{ const v = clone(); v.claims[0].status._tag = "checked"; check("red: unknown status tag", v, false) }
{ const v = clone(); v.claims[2].status.counterexample.id = "E4-TYPED-CE-1"; check("red: malformed register id", v, false) }
{ const v = clone(); v.claims[2].status.counterexample.registerStatus = "OPEN"; check("red: register status not a register word", v, false) }
{ const v = clone(); v.concepts[0].counts.proved = 2; check("red: concept counts disagree with the claims", v, false) }
{ const v = clone(); v.concepts[0].counts.assumed = -1; check("red: negative count", v, false) }
{ const v = clone(); v.claims[3].status = JSON.parse(JSON.stringify(v.claims[1].status)); check("red: one goal counted by two claims", v, false) }
{ const v = clone(); v.placement.declarations[0].placement = "provisional"; check("red: placement outside tagged/inherited", v, false) }
{ const v = clone(); v.claims[3].status.reason = "   "; check("red: absent without a reason", v, false) }
{ const v = clone(); v.claims[2].status.counterexample.witness = { name: "x" }; check("red: malformed nested counterexample witness", v, false) }

const allAgree = results.every((r) => r.agrees)
console.log(JSON.stringify({ allAgree, results }, null, 2))
// a disagreeing control fails the run (no `process` typing needed)
if (!allAgree) throw new Error("a control disagrees with its expectation")
