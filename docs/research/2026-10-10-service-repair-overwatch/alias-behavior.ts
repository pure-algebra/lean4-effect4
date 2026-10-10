import { Effect } from "effect"
import * as Canonical from "./canonical.ts"
import * as Alias from "./alias.ts"
const keys = await Effect.runPromise(Effect.provide(Effect.map(Alias.S, Object.keys), Alias.SLayer))
const restoredKeys = await Effect.runPromise(Effect.provide(Effect.map(Canonical.S, Object.keys), Canonical.SLayer))
const answer = await Effect.runPromise(Effect.provide(Effect.flatMap(Alias.S, s => s.alias()), Alias.SLayer))
const originalMain = await Effect.runPromise(Canonical.main)
const aliasMain = await Effect.runPromise(Alias.main)
if (JSON.stringify(keys) !== '["get","alias"]' || JSON.stringify(restoredKeys) !== '["get"]' || answer !== 1 || originalMain !== 1 || aliasMain !== 1) throw new Error("alias control failed")
console.log(JSON.stringify({keys,restoredKeys,answer,originalMain,aliasMain}))
