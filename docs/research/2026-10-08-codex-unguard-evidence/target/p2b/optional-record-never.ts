import { recordOptional } from "./records.ts"
declare const impossible: never
export const neverValue = recordOptional("x")(impossible)
