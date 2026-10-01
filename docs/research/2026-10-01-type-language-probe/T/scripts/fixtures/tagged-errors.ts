// Seat T fixture for form_census.ts's tagged-error measurements; counts in tagged-errors.expected.tsv.
import { Data, Schema } from "effect"
class Gone extends Data.TaggedError("Gone") {}
class Oops extends Data.TaggedError("OopsTag")<{ readonly message: string }> {}
class NotFound extends Data.TaggedError("NotFound")<{ readonly id: number; readonly cause: unknown; readonly at: ReadonlyArray<string> }> {}
class Bad extends Schema.TaggedError<Bad>()("Bad", { id: Schema.Number, cause: Schema.Defect, note: Schema.optional(Schema.String) }) {}
