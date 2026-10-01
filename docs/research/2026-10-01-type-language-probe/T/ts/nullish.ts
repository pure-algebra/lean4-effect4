// Seat T: can today's `unit` (printed `void`) or the handle spellings stand for undefined and null? (green: exit 0)
import { Option } from "effect"
type Mutual<A, B> = [A] extends [B] ? ([B] extends [A] ? true : false) : false
export const u1: Mutual<string | undefined, string | void> = false // unit prints `void`: not the undefined type
export const u2: [undefined] extends [void] ? true : false = true // one direction only
export const u3: Mutual<string | null, Option.Option<string>> = false // Option is not the nullable spelling
export const u4: Mutual<{ readonly a?: string }, { readonly a?: string | void }> = false
export const u5: Mutual<null, undefined> = false
