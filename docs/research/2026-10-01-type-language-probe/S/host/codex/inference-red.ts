import { FromEntries } from "./inference"
type Equal<A, B> = (<T>() => T extends A ? 1 : 2) extends
  (<T>() => T extends B ? 1 : 2) ? true : false
type Assert<T extends true> = T
type Expected = { readonly "a-b": string; readonly "__proto__": number }
export type ClaimedExactInference = Assert<Equal<typeof FromEntries.Type, Expected>>
