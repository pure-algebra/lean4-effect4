// Compiler checks of the error payload face (decisions row 120, part E2): the class declarations
// and constructions the printer writes, verbatim (`Test/Codegen/PayloadClasses.lean` pins each
// text), checked by tsgo 7 against effect@4.0.0-rc.112. Finite target assignment evidence, not an
// execution theorem. The red twin is `test/red/payload-classes.red.ts`; `payload-classes.test.ts`
// runs it and pins its error codes.
import { Data, Effect, Exit } from "effect"

export class NotFound extends Data.TaggedError("NotFound")<{ readonly id: number }> {}
export class Unauthorized extends Data.TaggedError("Unauthorized")<{ readonly reason: string }> {}
export class Wrapped extends Data.TaggedError("Wrapped")<{ readonly cause: string }> {}

// Every route seat E1's probe lists prints the class: `fail` of the construction, a bound
// variable failed later, a failure handled inside, a failure reified by `exit`, and the
// construction as data.
export const failDirect: Effect.Effect<never, NotFound, never> = Effect.fail(new NotFound({ id: 9 }))
export const failBound: Effect.Effect<never, NotFound, never> = Effect.flatMap(Effect.succeed(new NotFound({ id: 9 })), (a0) => Effect.fail(a0))
export const handled: Effect.Effect<number, never, never> = Effect.catchCause(Effect.flatMap(Effect.succeed(new NotFound({ id: 9 })), (a0) => Effect.fail(a0)), (a0) => Effect.succeed(0))
export const reified: Effect.Effect<Exit.Exit<never, NotFound>, never, never> = Effect.flatMap(Effect.succeed(new NotFound({ id: 9 })), (a0) => Effect.exit(Effect.fail(a0)))
export const asData: Effect.Effect<NotFound, never, never> = Effect.succeed(new NotFound({ id: 9 }))
// two classes: the error column is their union (the `select` route is DI-55's finding F3, red)
export const classUnion: Effect.Effect<never, NotFound | Unauthorized, never> = Effect.flatMap(Effect.fail(new NotFound({ id: 9 })), (a0) => Effect.fail(new Unauthorized({ reason: "bad token" })))
// a field named `cause` is an ordinary field (rc.112 passes a truthy one on as `ErrorOptions.cause`)
export const withCause: Effect.Effect<never, Wrapped, never> = Effect.fail(new Wrapped({ cause: "disk" }))
// the instance is below its structural record (probe T's e2), so a record-typed slot takes it
export const below: { readonly _tag: "NotFound"; readonly id: number } = new NotFound({ id: 9 })

// red controls, each the twin's line with its expected error
// @ts-expect-error TS2740: a structural record lacks the class's `Error` members
export const structuralValue: NotFound = { _tag: "NotFound", id: 9 }
// @ts-expect-error TS2375: a structural failure does not fit an error column that names the class
export const structuralFail: Effect.Effect<never, NotFound, never> = Effect.fail({ _tag: "NotFound" as const, id: 9 })
// @ts-expect-error TS2375: nor a union of classes
export const structuralUnion: Effect.Effect<never, NotFound | Unauthorized, never> = Effect.fail({ _tag: "Unauthorized" as const, reason: "bad token" })
// @ts-expect-error the constructor takes no `_tag`: the class carries it
export const taggedArgs = new NotFound({ _tag: "NotFound", id: 9 })
// @ts-expect-error the constructor keeps its fields' types
export const wrongField = new NotFound({ id: "9" })
void [failDirect, failBound, handled, reified, asData, classUnion, withCause, below, structuralValue, structuralFail, structuralUnion, taggedArgs, wrongField]
