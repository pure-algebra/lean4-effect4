/**
 * select-controls.ts: the three strict type-check controls of `caseTag`'s narrowing
 * (select packet §1.8) and one of `optionCase`. Compiled, never run: a failed narrowing
 * is a type error here. Two tags, a repeated tag, and a bare scalar beside a tagged pair.
 */
import { Effect, Option } from "effect"
import { caseTag, ifCase, optionCase, pair } from "./prelude.ts"

type TwoTags = readonly ["A", number] | readonly ["B", string]
declare const twoTags: TwoTags
export const twoTagControl: Effect.Effect<number | string> = caseTag(
  twoTags,
  "A",
  (payload: number) => Effect.succeed(payload),
  (rest: readonly ["B", string]) => Effect.succeed(rest[1]))

type RepeatedTag = readonly ["A", number] | readonly ["A", boolean] | readonly ["B", string]
declare const repeated: RepeatedTag
export const repeatedTagControl: Effect.Effect<number | boolean | string> = caseTag(
  repeated,
  "A",
  (payload: number | boolean) => Effect.succeed(payload),
  (rest: readonly ["B", string]) => Effect.succeed(rest[1]))

type WithScalar = readonly ["A", number] | string
declare const withScalar: WithScalar
export const bareScalarControl: Effect.Effect<number | string> = caseTag(
  withScalar,
  "A",
  (payload: number) => Effect.succeed(payload),
  (rest: string) => Effect.succeed(rest))

declare const maybe: Option.Option<number>
export const optionControl: Effect.Effect<number> = optionCase(
  maybe,
  () => Effect.succeed(0),
  (value: number) => Effect.succeed(value + 1))

export const literalPairControl = caseTag(
  pair("A", 1) as readonly ["A", number] | readonly ["B", string],
  "B",
  (payload: string) => Effect.succeed(payload.length),
  (rest: readonly ["A", number]) => Effect.succeed(rest[1]))

// Exact independent branch columns; a missing member in any column must refuse.
type BranchService0 = { readonly branchService: "zero" }
type BranchService1 = { readonly branchService: "one" }
declare const trueArm: Effect.Effect<number, "error0", BranchService0>
declare const falseArm: Effect.Effect<string, "error1", BranchService1>
export const booleanJoined = ifCase(() => true, () => trueArm, () => falseArm)
type Equal<X, Y> = (<T>() => T extends X ? 1 : 2) extends
  (<T>() => T extends Y ? 1 : 2) ? true : false
export const booleanSuccessExact: Equal<Effect.Success<typeof booleanJoined>, number | string> = true
export const booleanErrorExact: Equal<Effect.Error<typeof booleanJoined>, "error0" | "error1"> = true
export const booleanServicesExact: Equal<Effect.Services<typeof booleanJoined>, BranchService0 | BranchService1> = true
// @ts-expect-error The string success member cannot disappear.
export const booleanDroppedSuccess: Effect.Effect<number, "error0" | "error1", BranchService0 | BranchService1> = booleanJoined
// @ts-expect-error The second error member cannot disappear.
export const booleanDroppedError: Effect.Effect<number | string, "error0", BranchService0 | BranchService1> = booleanJoined
// @ts-expect-error The second service requirement cannot disappear.
export const booleanDroppedService: Effect.Effect<number | string, "error0" | "error1", BranchService0> = booleanJoined
