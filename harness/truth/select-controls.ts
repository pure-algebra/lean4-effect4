/**
 * select-controls.ts: the three strict type-check controls of `caseTag`'s narrowing
 * (select packet §1.8) and one of `optionCase`. Compiled, never run: a failed narrowing
 * is a type error here. Two tags, a repeated tag, and a bare scalar beside a tagged pair.
 */
import { Effect, Option } from "effect"
import { caseTag, optionCase, pair } from "./prelude.ts"

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
