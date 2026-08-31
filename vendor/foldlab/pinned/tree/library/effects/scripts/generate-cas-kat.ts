/**
 * Generate the committed scheme-0 known-answer fixture.
 *
 * Addresses come from the shipped SHA-256 address function over the platform's
 * WebCrypto, through the same builder the suite regenerates in memory, so the
 * committed file is never hand-typed and can never drift from the production
 * digest path without failing the gate.
 */
import { Effect } from "effect"
import { writeFileSync } from "node:fs"
import { fileURLToPath } from "node:url"
import {
  buildCasKatFixture,
  casKatFixtureUrl,
  productionCrypto,
  renderCasKatFixture,
} from "../test/fixtures/casScheme0.ts"

const fixture = await Effect.runPromise(
  buildCasKatFixture.pipe(Effect.provide(productionCrypto)),
)

writeFileSync(fileURLToPath(casKatFixtureUrl), renderCasKatFixture(fixture))
console.log(`wrote ${fixture.vectors.length} scheme-0 known-answer vectors`)
