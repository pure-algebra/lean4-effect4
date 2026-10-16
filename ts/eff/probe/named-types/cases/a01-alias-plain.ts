// expect: none
// A declared name with no recursion is an alias; the order compares aliases by structure.
import { Effect } from "effect"
export type UserId = number
export type OrderId = number
export const user: Effect.Effect<UserId> = Effect.succeed(7)
const asOrder = (id: OrderId): OrderId => id
// tsgo accepts what the nominal Lean order refuses: UserId where OrderId is expected
export const crossed: Effect.Effect<OrderId> = Effect.map(user, asOrder)
