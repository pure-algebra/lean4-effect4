import { Effect } from "effect"
import { ifCase } from "./prelude.ts"
export const main: Effect.Effect<number | string> = ifCase(() => true, () => Effect.succeed(1), () => Effect.succeed("other"))
