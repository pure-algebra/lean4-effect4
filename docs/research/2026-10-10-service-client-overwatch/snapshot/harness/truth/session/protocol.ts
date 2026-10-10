/** Versioned evidence for the serial-root scalar binding. Canonical program syntax remains
 * Eff. The full table is the Tools.ProfileJson view emitted by the Lean fixture driver;
 * exact structural equality, including every field, is required at this boundary. */
export type Json = null | boolean | number | string | Json[] | { [key: string]: Json }
export interface Header {
  format: "effect4-host-session-v1"
  version: 1
  session: string
  profile: "serial-root-scalar-v1"
  program: string
  table: Json[]
  rootRuntimeFiber: number
}
export interface Call {
  kind: "call"
  version: 1
  session: string
  callId: number
  fiber: 0
  runtimeFiber: number
  row: number
  request: number
}
export type Completion =
  | { kind: "success"; value: number }
  | { kind: "fail"; error: [string, string]; diagnostic: { category: "Fail"; tag: string; message: string } }
  | { kind: "die"; message: string; diagnostic: { category: "Die"; message: string } }
export interface Reply {
  kind: "reply"
  version: 1
  session: string
  callId: number
  completion: Completion
}
export interface Recording { header: Header; records: Array<Call | Reply> }
export interface Expected { program: string; table: Json[]; natBound: number }
export class ProtocolRefusal extends Error {
  constructor(readonly category: "malformed" | "outsideProfile", message: string) { super(message) }
}
const bad = (message: string): never => { throw new ProtocolRefusal("malformed", message) }
export const keys = (value: unknown, fields: string[]): Record<string, unknown> => {
  if (value === null || typeof value !== "object" || Array.isArray(value)) bad("expected object")
  const record = value as Record<string, unknown>
  if (Object.keys(record).sort().join("\u0000") !== [...fields].sort().join("\u0000")) bad("missing or extra fields")
  return record
}
export const text = (value: unknown): string => {
  if (typeof value !== "string" || value.length > 4096) bad("expected bounded text")
  return value as string
}
export const nat = (value: unknown): number => {
  if (typeof value !== "number" || !Number.isSafeInteger(value) || value < 0) bad("expected safe natural")
  return value as number
}
const scalar = (value: unknown, bound: number): number => {
  const n = nat(value)
  if (n > bound) throw new ProtocolRefusal("outsideProfile", "natural exceeds selected profile")
  return n
}
/** Structural JSON equality; object insertion order is irrelevant, field omission is not. */
export const equalJson = (a: unknown, b: unknown): boolean => {
  if (a === b) return true
  if (a === null || b === null || typeof a !== "object" || typeof b !== "object") return false
  if (Array.isArray(a) || Array.isArray(b)) return Array.isArray(a) && Array.isArray(b) && a.length === b.length && a.every((v, i) => equalJson(v, b[i]))
  const x = a as Record<string, unknown>, y = b as Record<string, unknown>
  const ks = Object.keys(x)
  return ks.length === Object.keys(y).length && ks.every(k => Object.hasOwn(y, k) && equalJson(x[k], y[k]))
}
export const completion = (value: unknown, bound: number): Completion => {
  if (value === null || typeof value !== "object") bad("expected completion")
  const kind = (value as Record<string, unknown>).kind
  if (kind === "success") {
    const c = keys(value, ["kind", "value"])
    return { kind, value: scalar(c.value, bound) }
  }
  if (kind === "fail") {
    const c = keys(value, ["kind", "error", "diagnostic"])
    if (!Array.isArray(c.error) || c.error.length !== 2) bad("expected pair failure")
    const error = (c.error as unknown[]).map(text) as [string, string]
    const d = keys(c.diagnostic, ["category", "tag", "message"])
    if (d.category !== "Fail" || d.tag !== error[0] || d.message !== error[1]) bad("contradictory failure diagnostic")
    return { kind, error, diagnostic: { category: "Fail", tag: error[0], message: error[1] } }
  }
  if (kind === "die") {
    const c = keys(value, ["kind", "message", "diagnostic"])
    const message = text(c.message), d = keys(c.diagnostic, ["category", "message"])
    if (d.category !== "Die" || d.message !== message) bad("contradictory defect diagnostic")
    return { kind, message, diagnostic: { category: "Die", message } }
  }
  return bad("unsupported completion category")
}
/** Strict boundary, before any machine decision. A final call without its reply is a valid
 * prefix. Multiple/mixed causes, arbitrary objects, child fibers, extra fields and legacy
 * tapes have no implicit conversion into this version. */
export const decode = (value: unknown, expected: Expected): Recording => {
  const body = keys(value, ["header", "records"])
  const h = keys(body.header, ["format", "version", "session", "profile", "program", "table", "rootRuntimeFiber"])
  if (h.format !== "effect4-host-session-v1" || h.version !== 1) bad("unknown protocol version")
  const session = text(h.session)
  if (session.length === 0) bad("empty session")
  if (h.profile !== "serial-root-scalar-v1" || h.program !== expected.program) bad("profile/program mismatch")
  if (!equalJson(h.table, expected.table)) bad("full table mismatch")
  const rootRuntimeFiber = nat(h.rootRuntimeFiber)
  const header: Header = { format: "effect4-host-session-v1", version: 1, session,
    profile: "serial-root-scalar-v1", program: expected.program, table: structuredClone(h.table) as Json[], rootRuntimeFiber }
  if (!Array.isArray(body.records)) bad("expected record list")
  let next = 0, active: number | undefined
  const records: Array<Call | Reply> = []
  for (const raw of body.records as unknown[]) {
    if (raw === null || typeof raw !== "object") bad("expected record")
    const kind = (raw as Record<string, unknown>).kind
    if (kind === "call") {
      const c = keys(raw, ["kind", "version", "session", "callId", "fiber", "runtimeFiber", "row", "request"])
      if (c.version !== 1 || c.session !== session) bad("call identity mismatch")
      const callId = nat(c.callId), row = nat(c.row), runtimeFiber = nat(c.runtimeFiber)
      if (c.fiber !== 0 || runtimeFiber !== rootRuntimeFiber) bad("outside serial root fiber")
      if (active !== undefined || callId !== next++) bad("call order/concurrency mismatch")
      if (row >= expected.table.length) bad("unknown row")
      active = callId
      records.push({ kind, version: 1, session, callId, fiber: 0, runtimeFiber, row, request: scalar(c.request, expected.natBound) })
    } else if (kind === "reply") {
      const r = keys(raw, ["kind", "version", "session", "callId", "completion"])
      if (r.version !== 1 || r.session !== session) bad("reply identity mismatch")
      const callId = nat(r.callId)
      if (active === undefined || callId !== active) bad("duplicate or out-of-order reply")
      active = undefined
      records.push({ kind, version: 1, session, callId, completion: completion(r.completion, expected.natBound) })
    } else bad("unknown record kind")
  }
  return { header, records }
}
