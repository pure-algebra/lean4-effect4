/** Structure comes from the Lean protocol projection. This decoder checks tape identity
 * and per-key bookkeeping; the Lean session separately checks the actual machine envelope. */
import { hostProtocol, type ProtocolState, type ProtocolTag } from "./protocol.gen.ts"
import { equalJson, keys, nat, text, ProtocolRefusal, type Json } from "./protocol.ts"
export { hostProtocol }
export interface Key { fiber: number; token: number }
export const keyText = (key: Key): string => `${key.fiber}:${key.token}`
export interface DecisionRecord extends Record<string, unknown> { kind: string; version: 2; session: string }
export interface KeyedHeader { format: "effect4-host-session-v2"; version: 2; session: string; profile: "keyed-v2"; program: string; table: Json[] }
export interface KeyedRecording { header: KeyedHeader; records: DecisionRecord[] }
const bad = (why: string): never => { throw new ProtocolRefusal("malformed", why) }
const natural = (value: unknown): number => { if (Object.is(value, -0)) bad("negative zero"); return nat(value) }
export const allows = (source: ProtocolState, label: ProtocolTag, target: ProtocolState): boolean =>
  hostProtocol.transitions.some(edge => edge[0] === source && edge[1] === label && edge[2] === target)
export const transition = (source: ProtocolState, label: ProtocolTag, target: ProtocolState): ProtocolState => {
  if (!allows(source, label, target)) bad(`protocol edge ${source}/${label}/${target}`)
  return target
}
export const recordKey = (record: DecisionRecord): Key => ({ fiber: natural(record.fiber), token: natural(record.token) })
/** JSON payloads remain data. A depth limit bounds a malformed transport before Lean's
 * typed decoder; arbitrary objects, unsafe naturals, and absent values never cross. */
const jsonData = (value: unknown, fuel = 64): void => {
  if (fuel === 0) bad("JSON depth")
  if (value === null || typeof value === "boolean") return
  if (typeof value === "number") { natural(value); return }
  if (typeof value === "string") { text(value); return }
  if (Array.isArray(value)) { value.forEach(v => jsonData(v, fuel - 1)); return }
  if (typeof value !== "object" || value === null || Object.getPrototypeOf(value) !== Object.prototype) bad("expected JSON data")
  Object.entries(value as Record<string, unknown>).forEach(([k, v]) => { text(k); jsonData(v, fuel - 1) })
}
export const decodeRecord = (value: unknown, session: string): DecisionRecord => {
  if (typeof value !== "object" || value === null) bad("expected record")
  const kind = (value as Record<string, unknown>).kind
  const shape = hostProtocol.records.find(shape => shape.kind === kind)
  if (!shape) return bad("unknown record kind")
  const record = keys(value, ["kind", "version", "session", ...Object.keys(shape.fields)])
  if (record.version !== hostProtocol.version || record.session !== session) bad("record identity mismatch")
  for (const [name, fieldType] of Object.entries(shape.fields)) {
    const type: string = fieldType
    if (type === "natural") natural(record[name])
    else if (type === "text") text(record[name])
    else if (type === "boolean") { if (typeof record[name] !== "boolean") bad("expected boolean") }
    else jsonData(record[name])
  }
  return structuredClone(record) as DecisionRecord
}
export const decodeKeyed = (value: unknown, expected: { program: string; table: Json[] }): KeyedRecording => {
  const body = keys(value, ["header", "records"])
  const h = keys(body.header, ["format", "version", "session", "profile", "program", "table"])
  if (h.version !== hostProtocol.version || h.format !== "effect4-host-session-v2") bad("version 2 required; legacy migration must be explicit")
  const session = text(h.session)
  if (!session || h.profile !== "keyed-v2" || h.program !== expected.program) bad("header identity mismatch")
  if (!equalJson(h.table, expected.table)) bad("full table mismatch")
  if (!Array.isArray(body.records)) bad("expected records")
  const records = (body.records as unknown[]).map(record => decodeRecord(record, session))
  let next = 0
  const active = new Map<string, number>(), pending = new Set<string>(), used = new Set<string>()
  for (const record of records) {
    if (record.kind === "call") {
      const key = keyText(recordKey(record)), id = natural(record.callId)
      if (used.has(key)) bad("duplicate call key")
      if (id !== next++) bad("call order")
      if (natural(record.row) >= expected.table.length) bad("unknown row")
      active.set(key, id); used.add(key)
    } else if (record.kind === "reply") {
      const key = keyText(recordKey(record))
      if (!active.has(key) || active.get(key) !== natural(record.callId)) bad("unknown call association")
      if (pending.has(key)) bad("duplicate pending reply")
      const completion = record.completion as Record<string, unknown> | null
      if (!completion || typeof completion !== "object" || Array.isArray(completion)) bad("expected completion")
      if (Object.hasOwn(completion!, "success")) keys(completion, ["success"])
      else { const failure = keys(completion, ["failure"]); if (!Array.isArray(failure.failure)) bad("expected ordered reasons") }
      pending.add(key)
    } else if (record.kind === "apply") {
      const key = keyText(recordKey(record))
      if (!active.has(key) || !pending.has(key)) bad("application needs this key's stored reply")
      active.delete(key); pending.delete(key)
    }
  }
  return { header: structuredClone(h) as unknown as KeyedHeader, records }
}
