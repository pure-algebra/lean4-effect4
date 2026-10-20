import { Schema } from "effect"
export const Observation = Schema.Struct({ exit: Schema.Unknown, parked: Schema.Boolean, schedule: Schema.Array(Schema.String) })
export const Observed = Schema.Union([
  Schema.Struct({ status: Schema.Literal("observed"), effect: Schema.Literal("4.0.0-rc.112"), timeoutMs: Schema.Number, observation: Observation }),
  Schema.Struct({ status: Schema.Literal("could-not-run"), error: Schema.String })
])
export type Observed = typeof Observed.Type
