/**
 * Commit the EFFECT-NATIVE register's materialized modules.
 *
 * `Cas.Materialize.source` prints a stored schema node through Effect's
 * own `SchemaRepresentation.toCodeDocument`; this writes that output,
 * one module per registered canonical-schema fixture, under
 * `test/generated/materialized/effect/`. Its estate-native counterpart
 * is `lake exe materialize`, which writes the same nodes through the
 * Lean printer under `../estate/`.
 *
 * Two reasons the snapshot is committed rather than rendered in memory:
 * the differential suite EVALUATES both registers' modules (never
 * compares their text — the two printers legitimately differ in
 * spelling), and a committed `.ts` file inside `tsconfig.test.json`'s
 * include is typechecked by `bun run typecheck` for free, which is the
 * compile gate SCHEMA-MATERIALIZATION.md ruling-queue item 17 asks for.
 *
 * Freshness is the suite's job, not a second gate's: the
 * MaterializeDifferential suite re-renders every module and compares
 * bytes, so a stale snapshot is red under `mise run check:effects:ts`.
 */
import { mkdir, writeFile } from "node:fs/promises"
import { BunFileSystem } from "@effect/platform-bun"
import { Effect, Layer } from "effect"
import { Cas } from "../src/index.ts"
import {
  effectRegisterIndex,
  effectRegisterModule,
  registeredNames,
} from "../test/fixtures/materialized.ts"

const outDir = new URL("../test/generated/materialized/effect/", import.meta.url)

const rendered = await Effect.runPromise(
  Effect.gen(function* () {
    const names = yield* registeredNames
    const modules = yield* Effect.forEach(names, (name) =>
      effectRegisterModule(name).pipe(
        Effect.map((text) => [name, text] as const),
      ))
    return { modules, index: effectRegisterIndex(names) }
  }).pipe(
    Effect.provide(Layer.mergeAll(
      BunFileSystem.layer,
      Cas.layerAddressSha256Live,
    )),
  ),
)

await mkdir(outDir, { recursive: true })
for (const [name, text] of rendered.modules) {
  await writeFile(new URL(`${name}.ts`, outDir), text)
}
await writeFile(new URL("index.ts", outDir), rendered.index)
console.log(
  `materialized ${rendered.modules.length} Effect-native modules into test/generated/materialized/effect/`,
)
