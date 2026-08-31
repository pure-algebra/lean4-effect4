/**
 * The two materialization registers, named in one place.
 *
 * P6's differential needs two independent generators over one stored
 * node. The ESTATE register is Lean's — `lake exe materialize` lowers
 * the committed payload through `Cas/Backend/EmitAst.lean` and commits
 * the module under `test/generated/materialized/estate/`. The EFFECT
 * register is this package's — `Cas.Materialize.source` prints the same
 * node through Effect's own `SchemaRepresentation.toCodeDocument`, and
 * `scripts/gen-materialized.ts` commits ITS module under
 * `test/generated/materialized/effect/`.
 *
 * Both committed trees sit inside `tsconfig.test.json`'s include, so
 * `bun run typecheck` compiles generated output from both registers as
 * a matter of course — the compile gate of SCHEMA-MATERIALIZATION.md
 * ruling-queue item 17, paid for by placement rather than by machinery.
 *
 * The rendering below is the ONE definition of the Effect register's
 * committed artifact: the generator writes what it says, and
 * `MaterializeDifferential.test.ts` re-renders it and compares bytes,
 * so a drifted snapshot is a red suite rather than a stale file.
 */
import { Effect, FileSystem } from "effect"
import { Cas } from "../../src/index.ts"
import { readFixtureBytes, readFixtureString } from "./read.ts"

/** Where the Lean-emitted payloads live, relative to the package root
 * (vitest and the generator both run with cwd = `library/effects`). */
export const schemaPayload = (name: string): string =>
  `../cas/schemas/${name}.json`

/** The registered fixture names, in registry order, read from the
 * Lean-emitted manifest — the same file `lake exe materialize` reads.
 * Neither register carries its own copy of the registry. */
export const registeredNames: Effect.Effect<
  ReadonlyArray<string>,
  never,
  FileSystem.FileSystem
> = readFixtureString("../cas/schemas/index.json").pipe(
  Effect.orDie,
  Effect.map((text) =>
    (JSON.parse(text) as { schemas: ReadonlyArray<{ name: string }> })
      .schemas.map((row) => row.name)
  ),
)

/** `union-pin` ⇒ `unionPin` — the same transliteration
 * `MaterializeMain.bindingName` applies to the same registry name. */
export const bindingName = (name: string): string =>
  name.split("-").map((word, index) =>
    index === 0 ? word : `${word[0]!.toUpperCase()}${word.slice(1)}`
  ).join("")

/** The Effect register's module for one registered fixture: the payload
 * bytes materialized through the door that derives its own address, and
 * `Materialize.source` on the single binding. */
export const effectRegisterModule = (
  name: string,
): Effect.Effect<
  string,
  never,
  FileSystem.FileSystem | Cas.AddressScheme
> =>
  Effect.gen(function* () {
    const payload = yield* readFixtureBytes(schemaPayload(name))
    const materialized = yield* Cas.Materialize.fromPayload(payload)
    return Cas.Materialize.source([
      { ...materialized, name: bindingName(name) },
    ])
  }).pipe(Effect.orDie)

/** The Effect register's barrel, written by the generator and re-derived
 * by the suite: one re-export per registered fixture, in registry
 * order. */
export const effectRegisterIndex = (
  names: ReadonlyArray<string>,
): string =>
  `${[
    `/**`,
    ` * GENERATED — do not edit. The Effect-native materialized modules,`,
    ` * one export per registered canonical-schema fixture, written by`,
    ` * \`bun scripts/gen-materialized.ts\` (\`mise run gen\`); the`,
    ` * MaterializeDifferential suite re-renders every one of them and`,
    ` * compares bytes, so a stale snapshot is a red suite.`,
    ` *`,
    ` * The estate-native counterpart is emitted by \`lake exe materialize\``,
    ` * under \`../estate/\`, and the two are held to one denotation.`,
    ` */`,
    ``,
    ...names.map((name) =>
      `export { ${bindingName(name)} } from "./${name}.ts"`
    ),
  ].join("\n")}\n`
