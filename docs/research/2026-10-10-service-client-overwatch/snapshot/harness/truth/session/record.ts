/** Actual Effect rc.112 binding. Record immutable request/fiber/call association when the
 * call begins, then join its selected completion. Raw Exit objects remain transient. */
import { Cause, Effect, Exit } from "effect"
import { decode, ProtocolRefusal, type Call, type Completion, type Expected, type Header, type Recording } from "./protocol.ts"

export class ScalarRecorder {
  private readonly records: Recording["records"] = []
  private nextCall = 0
  private rootFiber: number | undefined
  private boundaryRefusal: ProtocolRefusal | undefined
  private refuse(category: "malformed" | "outsideProfile", message: string): ProtocolRefusal {
    const why = new ProtocolRefusal(category, message)
    this.boundaryRefusal ??= why
    return why
  }
  constructor(readonly session: string, readonly expected: Expected, readonly failAt?: number) {}

  readonly Host = {
    wait: (request: number): Effect.Effect<number, readonly [string, string]> => Effect.withFiber(fiber => Effect.suspend(() => {
      if (this.rootFiber === undefined || fiber.id !== this.rootFiber) return Effect.die(this.refuse("malformed", "outside serial root fiber"))
      if (!Number.isSafeInteger(request) || request < 0 || request > this.expected.natBound)
        return Effect.die(this.refuse("outsideProfile", "natural exceeds selected profile"))
      const call: Call = { kind: "call", version: 1, session: this.session, callId: this.nextCall++,
        fiber: 0, runtimeFiber: fiber.id, row: 0, request }
      this.records.push(structuredClone(call))
      const effect: Effect.Effect<number, readonly [string, string]> = request === this.failAt
        ? Effect.fail(["Scalar", "selected failure"] as const) : Effect.succeed(request)
      return Effect.onExit(effect, exit => Effect.sync(() => {
        this.records.push({ kind: "reply", version: 1, session: call.session,
          callId: call.callId, completion: this.project(exit) })
      }))
    }))
  }

  private project(exit: Exit.Exit<number, readonly [string, string]>): Completion {
    if (Exit.isSuccess(exit)) return { kind: "success", value: exit.value }
    if (exit.cause.reasons.length !== 1) throw this.refuse("malformed", "unsupported multiple/mixed cause")
    const reason = exit.cause.reasons[0]!
    if (Cause.isFailReason(reason)) {
      const [tag, message] = reason.error
      return { kind: "fail", error: [tag, message], diagnostic: { category: "Fail", tag, message } }
    }
    if (Cause.isDieReason(reason) && typeof reason.defect === "string")
      return { kind: "die", message: reason.defect, diagnostic: { category: "Die", message: reason.defect } }
    throw this.refuse("malformed", "unsupported raw cause; no canonical error invented")
  }

  async run(program: Effect.Effect<number, readonly [string, string]>): Promise<{ recording: Recording; exit: Exit.Exit<number, readonly [string, string]>; completion: Completion }> {
    if (this.rootFiber !== undefined) throw new ProtocolRefusal("malformed", "recorder already used")
    const exit = await Effect.runPromiseExit(Effect.withFiber(fiber => {
      this.rootFiber = fiber.id
      return program
    }))
    if (this.boundaryRefusal) throw this.boundaryRefusal
    const header: Header = { format: "effect4-host-session-v1", version: 1, session: this.session,
      profile: "serial-root-scalar-v1", program: this.expected.program,
      table: structuredClone(this.expected.table), rootRuntimeFiber: this.rootFiber! }
    return { recording: decode({ header, records: this.records }, this.expected), exit, completion: this.project(exit) }
  }
}
