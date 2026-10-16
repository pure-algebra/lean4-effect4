// expect: none
// A recursive Schema whose body holds an Exit: the defect slot's encoded side is Json, its type
// side unknown. `Schema.Codec<T>` still holds: Exit has no defect parameter on either side.
import { Exit, Schema } from "effect"
export type Job = { readonly name: string; readonly last: Exit.Exit<Job, string> }
export const Job = Schema.Struct({
  name: Schema.String,
  last: Schema.Exit(Schema.suspend((): Schema.Codec<Job> => Job), Schema.String, Schema.Defect())
})
