import { recordOptional } from "./records.ts"
export const missingPropertyRead = (value: { readonly present: number }) => recordOptional("missing")(value)
