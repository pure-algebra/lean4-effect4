// Seat T: declarations as an idiomatic module writes them (p1-p5 style), imported by the spelling checks.
import { Data, Schema } from "effect"
export class NotFound extends Data.TaggedError("NotFound")<{ readonly id: number }> {}
export class NotFoundOtherTag extends Data.TaggedError("Missing")<{ readonly id: number }> {}
export interface Response { readonly status: number; readonly body: string }
export class UserClass extends Schema.Class<UserClass>("User")({ id: Schema.Number, name: Schema.String }) {}
