// expect: none
// Recursion through a union of tagged records (a derived sum type).
import { Effect } from "effect"
export type Expr =
  | { readonly _tag: "Lit"; readonly value: number }
  | { readonly _tag: "Add"; readonly left: Expr; readonly right: Expr }
export const expr: Effect.Effect<Expr> = Effect.succeed({
  _tag: "Add", left: { _tag: "Lit", value: 1 }, right: { _tag: "Lit", value: 2 }
})
