// expect: TS2440
// A declared name equal to a prelude type the module imports.
import type { Int } from "./_prelude.ts"
export type Int = string
export type Keep = Int
