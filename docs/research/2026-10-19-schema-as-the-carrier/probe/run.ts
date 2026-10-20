/** Run each printed program of Faces.lean under Bun on effect 4.0.0-rc.112, and print its exit
 * encoded with the case's exit Schema (`out/cases.gen.ts`): one line a case, in Faces.lean's
 * order, `refused` where the type has no Schema code.
 *
 *     bun docs/research/2026-10-19-schema-as-the-carrier/probe/run.ts */
import { Effect, Schema } from "effect"
import { cases, order, refused } from "./out/cases.gen.ts"

type Json = null | boolean | number | string | ReadonlyArray<Json> | { readonly [key: string]: Json }
const canon = (v: Json): string =>
  Array.isArray(v) ? `[${v.map(canon).join(",")}]`
  : v !== null && typeof v === "object" ? `{${Object.keys(v).sort().map(k => `${JSON.stringify(k)}:${canon((v as { readonly [key: string]: Json })[k] ?? null)}`).join(",")}}`
  : JSON.stringify(v)

for (const name of order) {
  if (refused.includes(name)) { console.log(name, "refused"); continue }
  const entry = cases[name]
  if (entry === undefined) { console.log(name, "no case"); continue }
  const codec = entry.codec as Schema.Codec<unknown, unknown>
  let line: string
  try {
    const mod = (await import(`./out/${name}.gen.ts`)) as { main: Effect.Effect<unknown, unknown> }
    const exit = entry.sync ? Effect.runSyncExit(mod.main) : await Effect.runPromiseExit(mod.main)
    line = canon(Schema.encodeSync(codec)(exit) as Json)
  } catch (error) {
    line = "REFUSED " + String(error).split("\n")[0]!.slice(0, 160)
  }
  console.log(name, line)
}
