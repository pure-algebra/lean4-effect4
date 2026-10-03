// Compiler checks of the structural target types emitted by Codegen.Types.
// This is finite target assignment evidence, not an execution theorem.
import { Option } from "effect"

type Person = { readonly id: number; readonly nickname?: string }
const missing: Person = { id: 1 }
const present: Person = { id: 1, nickname: "N" }
// @ts-expect-error An optional key does not admit a present undefined value.
const wrongPresence: Person = { id: 1, nickname: undefined }
// @ts-expect-error A required field cannot be absent.
const wrongRequired: Person = { nickname: "N" }
const explicitUndefined: { readonly nickname?: string | undefined } = { nickname: undefined }
const names: { readonly __proto__: number; readonly "a-b": null } = { ["__proto__"]: 1, ["a-b"]: null }
const tuple: readonly [number, { readonly x?: Uint8Array }] = [1, { x: new Uint8Array([0, 255]) }]
// @ts-expect-error Tuple arity is fixed.
const shortTuple: readonly [number, string] = [1]
// @ts-expect-error Tuple components retain their positions.
const swappedTuple: readonly [number, string] = ["x", 1]
const map: Readonly<Record<string, Option.Option<undefined>>> = { x: Option.some(undefined), y: Option.none() }
// @ts-expect-error The projected map is readonly.
map.x = Option.none()
// @ts-expect-error A field with a string type is not a byte array.
const wrongBytes: { readonly x?: Uint8Array } = { x: "bytes" }
void [missing, present, wrongPresence, wrongRequired, explicitUndefined, names, tuple, shortTuple, swappedTuple, map, wrongBytes]
