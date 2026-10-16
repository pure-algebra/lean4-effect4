// expect: none
// A declared name equal to a type-only import of a namespace (the printed header imports
// `type Option` from "effect"): no type meaning, so no clash; the printer must refuse it.
import { type Option } from "effect"
export type Option = number
export type Keep = Option
