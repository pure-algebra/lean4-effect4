// expect: none
// A declared name equal to a namespace import: a namespace has no type meaning, so tsgo accepts
// the alias silently and the name now spells two things. The printer must refuse it itself.
import { Option } from "effect"
export type Option = number
export const keep = Option.none()
