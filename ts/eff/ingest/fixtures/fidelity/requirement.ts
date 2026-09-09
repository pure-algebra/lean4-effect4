import { Context, Effect } from "effect"
const Key = Context.Service<number>("Number")
export const requires = Effect.service(Key)
