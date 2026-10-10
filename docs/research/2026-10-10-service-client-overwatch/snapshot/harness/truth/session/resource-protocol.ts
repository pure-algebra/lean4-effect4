/** Explicit resource profile of the version-one session envelope. Resource request identity
 * and raw fresh allocation indices have different wire shapes. */
import { completion, equalJson, keys, nat, text, ProtocolRefusal, type Expected, type Header } from "./protocol.ts"
import { resourceTarget, type ResourceCompletion, type ResourceRecord } from "./resource.ts"
export interface ResourceHeader extends Omit<Header, "profile"> { profile: "serial-root-resource-v1" }
export interface ResourceRecording { header: ResourceHeader; records: ResourceRecord[] }
const bad = (message: string): never => { throw new ProtocolRefusal("malformed", message) }

export const decodeResource = (value: unknown, expected: Expected): ResourceRecording => {
  const body = keys(value, ["header", "records"])
  const h = keys(body.header, ["format", "version", "session", "profile", "program", "table", "rootRuntimeFiber"])
  if (h.format !== "effect4-host-session-v1" || h.version !== 1 || h.profile !== "serial-root-resource-v1") bad("resource version/profile mismatch")
  const session = text(h.session)
  if (!session || h.program !== expected.program) bad("resource session/program mismatch")
  if (!equalJson(h.table, expected.table)) bad("full resource table mismatch")
  const runtimeFiber = nat(h.rootRuntimeFiber)
  const header: ResourceHeader = { format: "effect4-host-session-v1", version: 1, session,
    profile: "serial-root-resource-v1", program: expected.program, table: structuredClone(expected.table), rootRuntimeFiber: runtimeFiber }
  if (!Array.isArray(body.records)) bad("expected resource record list")
  let next = 0, allocations = 0
  let active: Extract<ResourceRecord, { kind: "call" }> | undefined
  const records: ResourceRecord[] = []
  for (const raw of body.records as unknown[]) {
    if (!raw || typeof raw !== "object") bad("expected resource record")
    const kind = (raw as Record<string, unknown>).kind
    if (kind === "call") {
      const c = keys(raw, ["kind", "version", "session", "callId", "fiber", "runtimeFiber", "row", "request"])
      const callId = nat(c.callId), row = nat(c.row)
      if (c.version !== 1 || c.session !== session || c.fiber !== 0 || nat(c.runtimeFiber) !== runtimeFiber) bad("resource call identity mismatch")
      if (active || callId !== next++ || row > 2) bad("resource call order/row mismatch")
      let request: null | { resource: { session: string; target: string; index: number } }
      if (row === 0) {
        if (c.request !== null) bad("acquire requires unit")
        request = null
      } else {
        const r = keys(c.request, ["resource"]), claim = keys(r.resource, ["session", "target", "index"])
        const index = nat(claim.index)
        if (claim.session !== session || claim.target !== resourceTarget || index >= allocations) bad("foreign or unallocated resource claim")
        request = { resource: { session, target: resourceTarget, index } }
      }
      active = { kind, version: 1, session, callId, fiber: 0, runtimeFiber, row, request }
      records.push(active)
    } else if (kind === "reply") {
      const r = keys(raw, ["kind", "version", "session", "callId", "completion"])
      const callId = nat(r.callId)
      if (r.version !== 1 || r.session !== session || !active || callId !== active.callId) bad("stale/duplicate resource reply")
      const current = active!
      const rawCompletion = r.completion as Record<string, unknown> | null
      let decoded: ResourceCompletion
      if (rawCompletion?.kind === "success" && rawCompletion.value === null) {
        keys(rawCompletion, ["kind", "value"])
        if (current.row !== 2) bad("unit on non-release row")
        decoded = { kind: "success", value: null }
      } else {
        decoded = completion(rawCompletion, expected.natBound)
        if (decoded.kind === "success") {
          if (current.row === 2) bad("non-unit release success")
          if (current.row === 0) {
            if (decoded.value !== allocations) bad("allocation index is not fresh")
            allocations += 1
          }
        }
        if (decoded.kind === "fail" && current.row !== 1) bad("failure on never-error resource row")
      }
      records.push({ kind, version: 1, session, callId, completion: decoded })
      active = undefined
    } else bad("unknown resource record")
  }
  return { header, records }
}
