/** A keyed recorder around real host operations. The supplied binding plan is explicit
 * evidence from a fixed Lean program/schedule; runtime fiber numbers are never guard tokens.
 * Actual call starts must match its row and request, and runtime/semantic fiber association
 * is bijective. Actual completions are stored before a separate application resumes Effect. */
import { Cause, Effect, Exit, Option, Result } from "effect"
import { equalJson, type Json } from "./protocol.ts"
import { decodeKeyed, decodeRecord, keyText, transition, type DecisionRecord, type Key, type KeyedHeader, type KeyedRecording } from "./keyed-protocol.ts"
import type { ProtocolState } from "./protocol.gen.ts"
export interface PlannedCall extends Key { callId: number; row: number; request: Json }
export interface PlannedAnswer { answerFor: number; completion: Json }
export interface KeyedFixture { name: string; expression: string; table: Json[]; source: null | { variant: number; pulls: number }; plan: Array<PlannedCall | PlannedAnswer>; expected: Json }
export type Pair = readonly [string, string]
export interface ExternalHandle { readonly index: number; readonly session: string }
export const valueJson = (value: unknown): Json => {
  if (value === undefined || value === null) return null
  if (typeof value === "boolean" || typeof value === "string") return value
  if (typeof value === "number" && Number.isSafeInteger(value) && value >= 0 && !Object.is(value, -0)) return value
  if (Array.isArray(value)) return value.map(valueJson)
  if (Option.isOption(value)) return Option.isNone(value) ? { none: true } : { some: valueJson(value.value) }
  if (Exit.isExit(value)) {
    if (Exit.isFailure(value)) throw Error("nested failed Exit requires an explicit cause image")
    return { ctor: 0, args: [valueJson(value.value)] }
  }
  if (Result.isResult(value)) return Result.isFailure(value)
    ? { ctor: 0, args: [valueJson(value.failure)] } : { ctor: 1, args: [valueJson(value.success)] }
  if (typeof value === "object" && value && "index" in value && "session" in value)
    return { handle: valueJson(value.index) }
  throw Error("value outside the selected transport profile")
}
export const exitJson = (exit: Exit.Exit<unknown, unknown>, fiberMap: ReadonlyMap<number, number> = new Map()): Json => {
  if (Exit.isSuccess(exit)) return { success: valueJson(exit.value) }
  return { failure: exit.cause.reasons.map(reason => {
    if (Cause.isFailReason(reason)) return { fail: valueJson(reason.error) }
    if (Cause.isDieReason(reason)) {
      if (typeof reason.defect !== "string" && typeof reason.defect !== "number") throw Error("unsupported defect projection")
      return { die: valueJson(reason.defect) }
    }
    if (reason.fiberId === undefined) return { interrupt: null }
    const fiber = fiberMap.get(reason.fiberId)
    if (fiber === undefined) throw Error("unassociated interruptor")
    return { interrupt: fiber }
  }) }
}
interface Waiting { call: PlannedCall; work: Effect.Effect<unknown, unknown>; resume: (effect: Effect.Effect<unknown, unknown>) => void }
interface Stored { waiting: Waiting; exit: Exit.Exit<unknown, unknown>; completion: Json }
export class KeyedRecorder {
  private nextCall = 0
  private readonly calls: PlannedCall[]
  private readonly waiters = new Map<string, Waiting>()
  private readonly stored = new Map<string, Stored>()
  private readonly fibers = new Map<number, number>()
  private readonly semanticFibers = new Map<number, number>()
  private phase: ProtocolState = "idle"
  private refused: Error | undefined
  readonly records: DecisionRecord[] = []
  readonly header: KeyedHeader
  constructor(readonly fixture: KeyedFixture, readonly session: string) {
    this.calls = fixture.plan.filter((entry): entry is PlannedCall => "callId" in entry)
    this.header = { format: "effect4-host-session-v2", version: 2, session, profile: "keyed-v2", program: fixture.name, table: fixture.table }
    this.record({ kind: "evaluate", fiber: 0 })
  }
  private record(fields: Record<string, unknown>): void {
    this.records.push(decodeRecord({ ...fields, version: 2, session: this.session }, this.session))
  }
  external<A, E>(row: number, request: Json, work: Effect.Effect<A, E>): Effect.Effect<A, E> {
    return Effect.withFiber(fiber => Effect.callback<A, E>(resume => {
      try {
        const call = this.calls[this.nextCall]
        if (!call || call.callId !== this.nextCall || call.row !== row || !equalJson(call.request, request))
          throw Error(`call association differs at ${this.nextCall}: ${row}/${JSON.stringify(request)}`)
        const old = this.fibers.get(fiber.id), runtime = this.semanticFibers.get(call.fiber)
        if ((old !== undefined && old !== call.fiber) || (runtime !== undefined && runtime !== fiber.id)) throw Error("fiber association is not bijective")
        this.fibers.set(fiber.id, call.fiber); this.semanticFibers.set(call.fiber, fiber.id)
        this.nextCall++
        const key = keyText(call)
        if (this.waiters.has(key) || this.stored.has(key)) throw Error("duplicate outstanding key")
        this.phase = transition(this.phase, "schedule", "awaitingAsync")
        this.record({ kind: "call", ...call })
        this.waiters.set(key, { call, work, resume: resume as Waiting["resume"] })
        return Effect.sync(() => { this.waiters.delete(key) })
      } catch (error) {
        this.refused = error instanceof Error ? error : Error(String(error))
        resume(Effect.die(this.refused))
      }
    }))
  }
  outstanding(): PlannedCall[] { return [...this.waiters.values()].map(w => w.call).sort((a, b) => a.callId - b.callId) }
  pending(): number[] { return [...this.stored.values()].map(s => s.waiting.call.callId).sort((a, b) => a - b) }
  hasReply(key: Key): boolean { return this.stored.has(keyText(key)) }
  async arrive(key: Key): Promise<void> {
    if (this.refused) throw this.refused
    const id = keyText(key), waiting = this.waiters.get(id)
    if (!waiting || this.stored.has(id)) throw Error("unknown or duplicate arrival")
    const exit = await Effect.runPromiseExit(waiting.work)
    if (!this.waiters.has(id)) throw Error("operation completed after cancellation; binding cleanup required")
    const allocation = this.fixture.name === "kv" || this.fixture.name === "concurrentStreams" || this.fixture.name.startsWith("stream-")
    const completion = allocation && waiting.call.row === 0 && Exit.isSuccess(exit)
      ? { success: (exit.value as ExternalHandle).index } : exitJson(exit, this.fibers)
    this.phase = transition(this.phase, "submit", this.phase)
    this.stored.set(id, { waiting, exit, completion })
    this.record({ kind: "reply", callId: waiting.call.callId, fiber: key.fiber, token: key.token, completion })
  }
  apply(key: Key): void {
    const id = keyText(key), stored = this.stored.get(id)
    if (!stored || !this.waiters.has(id)) throw Error("no stored reply for selected key")
    this.record({ kind: "apply", fiber: key.fiber, token: key.token })
    this.stored.delete(id); this.waiters.delete(id)
    this.phase = transition(this.phase, "answer", this.waiters.size ? "awaitingAsync" : "idle")
    stored.waiting.resume(Exit.isSuccess(stored.exit) ? Effect.succeed(stored.exit.value) : Effect.failCause(stored.exit.cause))
    if (this.refused) throw this.refused
  }
  finish(): KeyedRecording {
    if (this.refused) throw this.refused
    if (this.waiters.size || this.stored.size) throw Error("finished with unconsumed replies")
    this.phase = transition(this.phase, "schedule", "terminated")
    this.record({ kind: "flush" })
    return decodeKeyed({ header: this.header, records: this.records }, { program: this.fixture.name, table: this.fixture.table })
  }
  associations(): Array<{ runtimeFiber: number; fiber: number }> {
    return [...this.fibers].map(([runtimeFiber, fiber]) => ({ runtimeFiber, fiber })).sort((a, b) => a.fiber - b.fiber)
  }
}
