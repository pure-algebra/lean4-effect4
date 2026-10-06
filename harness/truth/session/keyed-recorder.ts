/** A keyed recorder around real host operations. The supplied binding plan is explicit
 * evidence from a fixed Lean program/schedule; runtime fiber numbers are never guard tokens.
 * Actual call starts must match its row and request, and runtime/semantic fiber association
 * is bijective. Actual completions are stored before a separate application resumes Effect.
 *
 * A scenario's fixture is `scripted` (decisions row 254). Its script holds each call, so a call
 * that starts is recorded when the script holds it. The recorder then keeps a ledger of the
 * held calls. A cancellation retires the held calls whose callback it interrupts, each with the
 * reply that waited. An operation that completes after its call is gone is a late reply: the
 * recorder writes its record, stores nothing and resumes nothing.
 *
 * The recorder is no second session. From its ledger it predicts the session's verdict of two
 * acts, by two rules that the session has (`src/Effect4/Api/HostSession.lean`): `submit` refuses
 * a reply with no live bound call as `noCall` and a second reply at a key as `pendingReply`,
 * and `applyReply` refuses a key with no bound call or no stored reply as `noCall`. The lane's
 * check compares each prediction with the verdict that Lean's replay gives the same record. */
import { Cause, Deferred, Effect, Exit, Option, Result, type Fiber } from "effect"
import { canonicalJson, payloadOf } from "../prelude.ts"
import { equalJson, type Json } from "./protocol.ts"
import { decodeKeyed, decodeRecord, hostProtocol, keyText, transition, type DecisionRecord, type Key, type KeyedHeader, type KeyedRecording } from "./keyed-protocol.ts"
import type { ProtocolState } from "./protocol.gen.ts"
import type { Rc112ClockBoundary } from "./clock.ts"
export interface PlannedCall extends Key { callId: number; row: number; request: Json }
export interface PlannedAnswer { answerFor: number; completion: Json }
export interface KeyedFixture { name: string; expression: string; table: Json[]; source: null | { variant: number; pulls: number }; plan: Array<PlannedCall | PlannedAnswer>; expected: Json; scripted?: true }
/** A call that a scenario's script holds: one entry of the recorder's ledger. `reply` is the
 * completion that the recorder stored for it. `kept` says whether that reply waited when a
 * cancellation retired the call. */
export interface HeldCall extends Key { callId: number; row: number; request: Json; state: "live" | "applied" | "retired"; reply?: Json; kept?: boolean }
/** A prediction of the recorder's ledger: the session refuses the record at this index, for
 * this reason. The row's kind is the session's: a reply is a `submit` row. */
export interface LedgerRefusal { readonly at: number; readonly row: "submit" | "apply"; readonly reason: "noCall" | "pendingReply" }
export type Pair = readonly [string, string]
export interface ExternalHandle { readonly index: number; readonly session: string }
/** The image of a value, under one choice: whether a `Deferred` has an image. */
const imageOf = (deferred: boolean): ((value: unknown) => Json) => {
  const image = (value: unknown): Json => {
    if (value === undefined || value === null) return null
    if (typeof value === "boolean" || typeof value === "string") return value
    if (typeof value === "number" && Number.isSafeInteger(value) && value >= 0 && !Object.is(value, -0)) return value
    if (Array.isArray(value)) return value.map(image)
    if (Option.isOption(value)) return Option.isNone(value) ? { none: true } : { some: image(value.value) }
    if (Exit.isExit(value)) {
      if (Exit.isFailure(value)) throw Error("nested failed Exit requires an explicit cause image")
      return { ctor: 0, args: [image(value.value)] }
    }
    if (Result.isResult(value)) return Result.isFailure(value)
      ? { ctor: 0, args: [image(value.failure)] } : { ctor: 1, args: [image(value.success)] }
    if (typeof value === "object" && value && "index" in value && "session" in value)
      return { handle: image(value.index) }
    if (deferred && Deferred.isDeferred(value)) return { handle: "deferred" }
    // A payload class instance (`Data.TaggedError`, decisions row 120) is the record of its data.
    const payload = payloadOf(value)
    if (payload !== null) return image(payload)
    // A record is the frame of `Effect4.Machine.Record.frame`: its names in UTF-8 byte order,
    // then its values. A printed module builds a record as a plain object (`recordValue`).
    if (typeof value === "object" && value && Object.getPrototypeOf(value) === Object.prototype) {
      const record = value as Record<string, unknown>
      const names = Object.keys(canonicalJson(Object.fromEntries(Object.keys(record).map(name => [name, null]))) as object)
      return { ctor: 0, args: [names, names.map(name => image(record[name]))] }
    }
    throw Error("value outside the selected transport profile")
  }
  return image
}
/** The image of a value of the transport profile: a call's request, a completion, an exit. A
 * `Deferred` is outside the profile. */
export const valueJson = imageOf(false)
/** The image of a cell that the cells reader reads. It is `valueJson`, and a `Deferred` has an
 * image too. A `Deferred` has no number on the host, so its image holds no identity:
 * `{"handle": "deferred"}`. Lean writes the same image where a scenario's wire chooses its
 * writer of the same name (`cellJson`, `Keyed.lean`): for a module's private cell, whose waiting
 * requests hold `Deferred` handles. The lane then compares such a cell up to its handles. It
 * does not compare which handle stands where. */
export const cellJson = imageOf(true)
/** The inverse of `valueJson` on a scripted completion: unit, a number, a boolean, a string, a
 * list, an option and a record. A record's frame has two columns of one length, and its first
 * column holds its names. Any other frame is refused. */
export const wireValue = (wire: Json): unknown => {
  if (wire === null) return undefined
  if (typeof wire !== "object") return wire
  if (Array.isArray(wire)) return wire.map(wireValue)
  if (equalJson(wire, { none: true })) return Option.none()
  if (Object.keys(wire).length === 1 && Object.hasOwn(wire, "some")) return Option.some(wireValue(wire.some!))
  const args = wire.ctor === 0 && Object.keys(wire).length === 2 ? wire.args : undefined
  if (Array.isArray(args) && args.length === 2) {
    const [names, values] = args
    if (Array.isArray(names) && Array.isArray(values) && names.length === values.length && names.every(name => typeof name === "string"))
      return Object.fromEntries(names.map((name, index) => [name as string, wireValue(values[index]!)]))
  }
  throw Error("scripted value outside the selected transport profile")
}
/** A scripted completion as the host operation that gives it: a success, or one typed failure. */
export const wireExit = (completion: Json): Effect.Effect<unknown, unknown> => {
  if (completion !== null && typeof completion === "object" && !Array.isArray(completion)) {
    if (Object.keys(completion).length === 1 && Object.hasOwn(completion, "success")) return Effect.succeed(wireValue(completion.success!))
    const reasons = Object.keys(completion).length === 1 ? completion.failure : undefined
    const reason = Array.isArray(reasons) && reasons.length === 1 ? reasons[0] : undefined
    if (reason !== null && typeof reason === "object" && !Array.isArray(reason) && Object.keys(reason).length === 1 && Object.hasOwn(reason, "fail"))
      return Effect.fail(wireValue(reason.fail!))
  }
  throw Error("scripted completion outside the selected transport profile")
}
export const exitJson = (exit: Exit.Exit<unknown, unknown>, fiberMap: ReadonlyMap<number, number> = new Map()): Json => {
  if (Exit.isSuccess(exit)) return { success: valueJson(exit.value) }
  return { failure: exit.cause.reasons.map(reason => {
    if (Cause.isFailReason(reason)) return { fail: valueJson(reason.error) }
    if (Cause.isDieReason(reason)) {
      if (typeof reason.defect !== "string" && typeof reason.defect !== "number") throw Error("unsupported defect projection", { cause: reason.defect })
      return { die: valueJson(reason.defect) }
    }
    if (reason.fiberId === undefined) return { interrupt: null }
    const fiber = fiberMap.get(reason.fiberId)
    if (fiber === undefined) throw Error("unassociated interruptor")
    return { interrupt: fiber }
  }) }
}
interface Waiting { call: PlannedCall; work: Effect.Effect<unknown, unknown>; resume: (effect: Effect.Effect<unknown, unknown>) => void; held?: Held }
interface Stored { waiting: Waiting; exit: Exit.Exit<unknown, unknown>; completion: Json }
/** A ledger entry with the host operation of its call: a reply may come after the call is gone. */
interface Held extends HeldCall { work: Effect.Effect<unknown, unknown> }
export class KeyedRecorder {
  private nextCall = 0
  private readonly calls: PlannedCall[]
  private readonly waiters = new Map<string, Waiting>()
  private readonly stored = new Map<string, Stored>()
  private readonly fibers = new Map<number, number>()
  private readonly semanticFibers = new Map<number, number>()
  private readonly runtime = new Map<number, Fiber.Fiber<unknown, unknown>>()
  private readonly ledger: Held[] = []
  private readonly ledgerRefusals: LedgerRefusal[] = []
  private readonly received: Held[] = []
  private readonly applied: Held[] = []
  private readonly retirements: Array<{ call: Held; kept: boolean; act: number }> = []
  private closed = false
  private phase: ProtocolState = "idle"
  private refused: Error | undefined
  readonly records: DecisionRecord[] = []
  readonly header: KeyedHeader
  constructor(readonly fixture: KeyedFixture, readonly session: string) {
    this.calls = fixture.plan.filter((entry): entry is PlannedCall => "callId" in entry)
    this.header = { format: "effect4-host-session-v3", version: hostProtocol.version, session, profile: "keyed-v3", program: fixture.name, table: fixture.table }
    this.record({ kind: "evaluate", fiber: 0 })
  }
  private record(fields: Record<string, unknown>): void {
    this.records.push(decodeRecord({ ...fields, version: hostProtocol.version, session: this.session }, this.session))
  }
  external<A, E>(row: number, request: Json, work: Effect.Effect<A, E>): Effect.Effect<A, E> {
    return Effect.withFiber(fiber => Effect.callback<A, E>(resume => {
      try {
        const call = this.calls[this.nextCall]
        if (!call || call.callId !== this.nextCall || call.row !== row || !equalJson(call.request, request))
          throw Error(`call association differs at ${this.nextCall}: ${row}/${JSON.stringify(request)}`)
        this.associate(call.fiber, fiber)
        this.nextCall++
        const key = keyText(call)
        if (this.waiters.has(key) || this.stored.has(key)) throw Error("duplicate outstanding key")
        this.phase = transition(this.phase, "schedule", "awaitingAsync")
        if (!this.fixture.scripted) this.record({ kind: "call", ...call })
        this.waiters.set(key, { call, work, resume: resume as Waiting["resume"] })
        return Effect.sync(() => { this.waiters.delete(key); this.retire(key) })
      } catch (error) {
        this.refused = error instanceof Error ? error : Error(String(error))
        resume(Effect.die(this.refused))
      }
    }))
  }
  /** A runtime fiber is one fiber of the machine, and a fiber of the machine is one runtime fiber. */
  private associate(fiber: number, runtime: Fiber.Fiber<unknown, unknown>): void {
    const old = this.fibers.get(runtime.id), other = this.semanticFibers.get(fiber)
    if ((old !== undefined && old !== fiber) || (other !== undefined && other !== runtime.id)) throw Error("fiber association is not bijective")
    this.fibers.set(runtime.id, fiber); this.semanticFibers.set(fiber, runtime.id); this.runtime.set(fiber, runtime)
  }
  /** The runtime fiber that the runner started is the machine's root, fiber 0. */
  attachRoot(runtime: Fiber.Fiber<unknown, unknown>): void { this.associate(0, runtime) }
  /** A cancellation interrupted the callback of the call at this key. A held call is retired,
   * with the reply that waited for it. A call that the script never held leaves no record. */
  private retire(id: string): void {
    const held = this.ledger.find(entry => keyText(entry) === id && entry.state === "live")
    if (this.closed || !held) return
    held.state = "retired"
    held.kept = this.stored.delete(id)
    this.retirements.push({ call: held, kept: held.kept, act: this.records.length })
    if (!this.waiters.size) this.phase = "idle"
  }
  /** The ledger predicts that the session refuses the record just written. */
  private predict(row: LedgerRefusal["row"], reason: LedgerRefusal["reason"]): void {
    this.ledgerRefusals.push({ at: this.records.length - 1, row, reason })
  }
  /** The script holds the call at this key: the session binds the call, with no reply. */
  hold(key: Key): void {
    if (this.refused) throw this.refused
    const id = keyText(key), waiting = this.waiters.get(id)
    if (!waiting) throw Error(`the script holds a call that the module did not start: ${id}`)
    const { fiber, token, row, request } = waiting.call
    if (waiting.held) throw Error(`the script holds a call twice: ${id}`)
    this.record({ kind: "call", callId: this.ledger.length, fiber, token, row, request })
    waiting.held = { callId: this.ledger.length, fiber, token, row, request, state: "live", work: waiting.work }
    this.ledger.push(waiting.held)
  }
  /** The host cancels a fiber of the machine: `interruptUnsafe` with no interruptor. */
  cancel(fiber: number): void {
    if (this.refused) throw this.refused
    const runtime = this.runtime.get(fiber)
    if (!runtime) throw Error(`no runtime fiber is associated with fiber ${fiber}`)
    this.record({ kind: "cancel", fiber })
    runtime.interruptUnsafe()
    if (this.refused) throw this.refused
  }
  /** The script's own flush: the host lets every dispatcher run after it. */
  flush(): void {
    if (this.refused) throw this.refused
    this.record({ kind: "flush" })
  }
  outstanding(): PlannedCall[] { return [...this.waiters.values()].map(w => w.call).sort((a, b) => a.callId - b.callId) }
  pending(): number[] { return [...this.stored.values()].map(s => s.waiting.call.callId).sort((a, b) => a - b) }
  hasReply(key: Key): boolean { return this.stored.has(keyText(key)) }
  async advanceClock(clock: Rc112ClockBoundary, millis: string): Promise<void> {
    if (this.refused) throw this.refused
    try {
      await clock.advance(millis, () => {
        if (this.refused) throw this.refused
        this.record({ kind: "advanceClock", millis })
      })
    } catch (error) {
      // Preflight refusals record nothing. A refusal after the advance begins retains
      // its attempted decision and any enabled calls, but can never publish a receipt.
      this.refused ??= error instanceof Error ? error : Error(String(error))
      throw this.refused
    }
  }
  async arrive(key: Key): Promise<void> {
    if (this.refused) throw this.refused
    const id = keyText(key), waiting = this.waiters.get(id)
    if (this.fixture.scripted) {
      // The reply of the call that the script holds or held at this key. The record is written
      // whatever the ledger says, so the session gives the row its own verdict.
      const held = this.ledger.find(entry => keyText(entry) === id)
      if (!held) throw Error(`the script answers a call that it never held: ${id}`)
      const exit = await Effect.runPromiseExit(held.work)
      const completion = exitJson(exit, this.fibers)
      this.record({ kind: "reply", callId: held.callId, fiber: key.fiber, token: key.token, completion })
      if (this.stored.has(id)) { this.predict("submit", "pendingReply"); return }
      if (held.state !== "live" || !this.waiters.has(id)) { this.predict("submit", "noCall"); return }
      this.phase = transition(this.phase, "submit", this.phase)
      this.stored.set(id, { waiting: this.waiters.get(id)!, exit, completion })
      held.reply = completion; this.received.push(held)
      return
    }
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
    if (this.fixture.scripted && (!stored || !this.waiters.has(id))) {
      this.record({ kind: "apply", fiber: key.fiber, token: key.token })
      this.predict("apply", "noCall")
      return
    }
    if (!stored || !this.waiters.has(id)) throw Error("no stored reply for selected key")
    this.record({ kind: "apply", fiber: key.fiber, token: key.token })
    this.stored.delete(id); this.waiters.delete(id)
    const held = stored.waiting.held
    if (held) { held.state = "applied"; this.applied.push(held) }
    this.phase = transition(this.phase, "answer", this.waiters.size ? "awaitingAsync" : "idle")
    stored.waiting.resume(Exit.isSuccess(stored.exit) ? Effect.succeed(stored.exit.value) : Effect.failCause(stored.exit.cause))
    if (this.refused) throw this.refused
  }
  /** An exit in the wire, with each interruptor as its fiber of the machine. The fibers reader
   * gives the forked fibers in fork order: the n-th is fiber n of the machine. */
  exitOf(exit: Exit.Exit<unknown, unknown>, forks: ReadonlyArray<Fiber.Fiber<unknown, unknown>> = []): Json {
    const fibers = new Map(this.fibers)
    forks.forEach((fork, index) => {
      const known = fibers.get(fork.id)
      if (known !== undefined && known !== index + 1) throw Error("a forked fiber has another number by its call")
      fibers.set(fork.id, index + 1)
    })
    return exitJson(exit, fibers)
  }
  /** The machine's number of a runtime fiber: the root's, or a caller's. */
  fiberOf(runtime: Fiber.Fiber<unknown, unknown>): number | undefined { return this.fibers.get(runtime.id) }
  /** The recording so far, by name `snapshot`: a script may end before the root does, so no
   * terminating flush is appended and a live call or a stored reply is no fault. Each record
   * passed `decodeRecord` when it was written. The per-key bookkeeping of `decodeKeyed` is not
   * applied: a recording of a script may hold a row that the session refuses. After a snapshot
   * the recorder notes nothing more, so the runner's teardown leaves no trace. */
  snapshot(): KeyedRecording {
    if (this.refused) throw this.refused
    this.closed = true
    return structuredClone({ header: this.header, records: this.records })
  }
  /** What the recorder measured by itself, for a scenario's observation. The calls the script
   * held, in hold order. The replies the ledger stored and the replies it applied, in order.
   * The retired calls, by the act that retired them and then in hold order, as the session's
   * `retire` lists them. The stored replies, in hold order. The live calls of the module, held
   * or not, by the machine's fiber. The ledger's predictions of a refusal, in order. */
  measurements(): { held: HeldCall[]; receipts: HeldCall[]; applications: HeldCall[]; retired: Array<{ call: HeldCall; kept: boolean }>; stored: HeldCall[]; live: PlannedCall[]; refusals: LedgerRefusal[] } {
    const plain = ({ work: _work, ...call }: Held): HeldCall => ({ ...call })
    return {
      held: this.ledger.map(plain), receipts: this.received.map(plain), applications: this.applied.map(plain),
      retired: [...this.retirements].sort((a, b) => a.act - b.act || a.call.callId - b.call.callId).map(({ call, kept }) => ({ call: plain(call), kept })),
      stored: this.ledger.filter(entry => this.stored.has(keyText(entry))).map(plain),
      live: [...this.waiters.values()].map(waiting => waiting.call).sort((a, b) => a.fiber - b.fiber),
      refusals: [...this.ledgerRefusals]
    }
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
