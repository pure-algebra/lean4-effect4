// The red twin of `test/payload-classes.typecheck.ts` (decisions row 120, part E2): each line
// must be refused by tsgo 7 against effect@4.0.0-rc.112, with the code `payload-classes.test.ts`
// pins. Excluded from the package's own check (`tsconfig.json`); checked by `test/red/tsconfig.json`.
import { Data, Effect } from "effect"

export class NotFound extends Data.TaggedError("NotFound")<{ readonly id: number }> {}
export class Unauthorized extends Data.TaggedError("Unauthorized")<{ readonly reason: string }> {}

export const structuralValue: NotFound = { _tag: "NotFound", id: 9 }
export const structuralFail: Effect.Effect<never, NotFound, never> = Effect.fail({ _tag: "NotFound" as const, id: 9 })
export const structuralUnion: Effect.Effect<never, NotFound | Unauthorized, never> = Effect.fail({ _tag: "Unauthorized" as const, reason: "bad token" })
export const taggedArgs = new NotFound({ _tag: "NotFound", id: 9 })
export const wrongField = new NotFound({ id: "9" })
// DI-55's finding F3: the former raw suspension infers one arm's error, not the union
export const selectUnion: Effect.Effect<never, NotFound | Unauthorized, never> = Effect.flatMap(Effect.succeed(true), (a0) => Effect.suspend(() => a0 ? Effect.fail(new NotFound({ id: 9 })) : Effect.fail(new Unauthorized({ reason: "bad token" }))))
