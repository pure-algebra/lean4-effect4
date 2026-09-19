import { expect, test } from "bun:test"
import { resolve } from "node:path"
import { query } from "./oracle.ts"
import { rowSignatures } from "./profile.ts"
import { queries } from "./rows.ts"

const repo = resolve(import.meta.dir, "../..")

// The red control for the template atoms' lane: `some` agrees at its probes, `getOrElse`'s export
// checked against `some`'s template does not, and `ite` instantiated with a type argument too
// many is refused rather than read.
test("a template atom agrees at its probes, and a wrong template or instantiation does not", () => {
  const some = rowSignatures(repo).get("Atom/some")!
  expect(some.typeArgs).toBe('<"p0">')
  const signatures = new Map([
    ["Atom/some", some],
    ["Atom/getOrElse", some],
    ["Atom/ite", { ...some, typeArgs: '<"p0", "p1">' }],
  ])
  const report = query(repo, queries(repo, signatures), "effect@4.0.0-rc.112/rows")
  const status = new Map(report.observations.map(o => [o.id, o.status]))
  expect(status.get("Atom/some")).toBe("agree")
  expect(status.get("Atom/getOrElse")).toBe("mismatch")
  expect(status.get("Atom/ite")).toBe("refused")
}, 60_000)
