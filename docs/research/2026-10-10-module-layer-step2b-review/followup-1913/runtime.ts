import { Effect, Exit } from "/Users/pooks/Dev/lean4-effect4-wt/module-layers/harness/truth/node_modules/effect/dist/index.js"
import { main, readKey } from "/Users/pooks/Dev/lean4-effect4-wt/module-layers/harness/truth/generated/pDefsModuleLayer.ts"

const observations = [
  ["definition-sync", Effect.runSyncExit(readKey(1))],
  ["main-sync", Effect.runSyncExit(main)],
  ["main-async", await Effect.runPromiseExit(main)],
] as const
for (const [name, exit] of observations) {
  if (!Exit.isSuccess(exit) || exit.value !== 7) throw new Error(`${name}: unexpected exit`)
  console.log(JSON.stringify({ name, exit: "success", value: exit.value }))
}
