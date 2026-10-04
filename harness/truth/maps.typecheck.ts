import { Option } from "effect"
import { mapEmpty, mapGet, mapSet, mapEntries, mapFromEntries } from "./prelude-atoms.gen.ts"

const numbers: Readonly<Record<string, number>> = mapSet(mapEmpty(), "count", 1)
const mixed: Readonly<Record<string, number | string>> = mapSet(numbers, "label", "x")
const lookup: Option.Option<number | string> = mapGet(mixed, "label")
const entries: ReadonlyArray<readonly [string, number | string]> = mapEntries(mixed)
const restored: Readonly<Record<string, number | string>> = mapFromEntries(entries)
// @ts-expect-error Updates retain the original value type.
const narrowed: Readonly<Record<string, string>> = mapSet(numbers, "label", "x")
// @ts-expect-error Map keys are strings.
mapGet(numbers, 1)
// @ts-expect-error Map inputs use pairs with a string key.
mapFromEntries([[1, 2]])
void [lookup, restored, narrowed]
