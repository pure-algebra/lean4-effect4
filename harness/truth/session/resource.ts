/** Selected resource binding. The registry owns identity, allocation and cleanup; an object
 * with matching public fields cannot impersonate a registered object. All mutation occurs
 * before the returned Fail/Die is observed. Raw Error objects are transient. */
import { Cause, Effect, Exit } from "effect"
import { ProtocolRefusal } from "./protocol.ts"

export const resourceTarget = "Host.Resource"
export const resourceQuota = 2
export const resourceSpent = ["Resource", "the resource's use budget is spent"] as const
export interface ResourceClaim { readonly session: string; readonly target: string; readonly index: number }
export interface ResourceSnapshot { readonly slots: boolean[]; readonly uses: number; readonly closes: number[]; readonly compensated: Array<{ physicalId: number; open: boolean; closes: number }> }
export class ResourceHandle {
  readonly target = resourceTarget
  constructor(readonly session: string, readonly index: number) {}
}
type Pair = readonly [string, string]
export type ResourceCompletion =
  | { kind: "success"; value: number | null }
  | { kind: "fail"; error: [string, string]; diagnostic: { category: "Fail"; tag: string; message: string } }
  | { kind: "die"; message: string; diagnostic: { category: "Die"; message: string } }
export type ResourceRecord =
  | { kind: "call"; version: 1; session: string; callId: number; fiber: 0; runtimeFiber: number; row: number; request: null | { resource: ResourceClaim } }
  | { kind: "reply"; version: 1; session: string; callId: number; completion: ResourceCompletion }
interface PhysicalResource { readonly physicalId: number; open: boolean; closes: number }
interface Slot extends PhysicalResource { readonly object: ResourceHandle }

export class ResourceBinding {
  private readonly slots: Slot[] = []
  private uses = 0
  private readonly compensated: PhysicalResource[] = []
  private nextPhysical = 0
  private nextCall = 0
  private rootFiber: number | undefined
  private boundaryRefusal: ProtocolRefusal | undefined
  readonly records: ResourceRecord[] = []
  constructor(readonly session: string) {
    if (!session) throw new ProtocolRefusal("malformed", "empty resource session")
  }
  private refuse(message: string): ProtocolRefusal {
    const why = new ProtocolRefusal("malformed", message)
    this.boundaryRefusal ??= why
    return why
  }
  private slot(handle: ResourceHandle): Slot {
    if (handle === null || typeof handle !== "object" || handle.session !== this.session ||
      handle.target !== resourceTarget || !Number.isSafeInteger(handle.index) || handle.index < 0)
      throw this.refuse("foreign resource identity")
    const slot = this.slots[handle.index]
    if (!slot || slot.object !== handle) throw this.refuse("unallocated or impersonated resource")
    return slot
  }
  claim(handle: ResourceHandle): ResourceClaim {
    this.slot(handle)
    return { session: handle.session, target: handle.target, index: handle.index }
  }
  snapshot(): ResourceSnapshot {
    return { slots: this.slots.map(x => x.open), uses: this.uses,
      closes: this.slots.map(x => x.closes), compensated: this.compensated.map(x => ({ ...x })) }
  }
  private physical(): PhysicalResource { return { physicalId: this.nextPhysical++, open: true, closes: 0 } }
  private allocate(physical = this.physical()): ResourceHandle {
    const handle = new ResourceHandle(this.session, this.slots.length)
    this.slots.push({ object: handle, ...physical })
    return handle
  }
  /** Projection owned by these known misuse rows: category Die and the controlled Error's
   * message become the program-visible text defect. No arbitrary object is coerced. */
  private misuse(message: "resource used after release" | "resource released twice"): Effect.Effect<never> {
    const raw = new Error(message)
    return Effect.die(raw.message)
  }
  private project<A>(row: number, exit: Exit.Exit<A, Pair>): ResourceCompletion {
    if (Exit.isSuccess(exit)) {
      if (row === 0) {
        const handle = exit.value as ResourceHandle
        this.slot(handle)
        return { kind: "success", value: handle.index }
      }
      if (row === 1 && typeof exit.value === "number") return { kind: "success", value: exit.value }
      if (row === 2 && exit.value === undefined) return { kind: "success", value: null }
      throw this.refuse("unexpected row success shape")
    }
    if (exit.cause.reasons.length !== 1) throw this.refuse("unsupported resource cause combination")
    const reason = exit.cause.reasons[0]!
    if (Cause.isFailReason(reason)) {
      const [tag, message] = reason.error
      return { kind: "fail", error: [tag, message], diagnostic: { category: "Fail", tag, message } }
    }
    if (Cause.isDieReason(reason) && typeof reason.defect === "string")
      return { kind: "die", message: reason.defect, diagnostic: { category: "Die", message: reason.defect } }
    throw this.refuse("unsupported raw resource cause")
  }
  private call<A, E extends Pair>(row: number, request: () => null | { resource: ResourceClaim }, body: () => Effect.Effect<A, E>): Effect.Effect<A, E> {
    return Effect.withFiber(fiber => Effect.suspend(() => {
      if (fiber.id !== this.rootFiber) throw this.refuse("outside serial resource root")
      const callId = this.nextCall++
      this.records.push({ kind: "call", version: 1, session: this.session, callId, fiber: 0,
        runtimeFiber: fiber.id, row, request: structuredClone(request()) })
      return Effect.onExit(body(), exit => Effect.sync(() => {
        this.records.push({ kind: "reply", version: 1, session: this.session, callId, completion: this.project(row, exit) })
      }))
    }))
  }
  readonly Host = {
    acquire: (): Effect.Effect<ResourceHandle> => this.call(0, () => null, () => Effect.sync(() => this.allocate())),
    use: (handle: ResourceHandle): Effect.Effect<number, Pair> => this.call(1, () => ({ resource: this.claim(handle) }), () => Effect.suspend(() => {
      const slot = this.slot(handle)
      if (!slot.open) return this.misuse("resource used after release")
      this.uses += 1
      return this.uses <= resourceQuota ? Effect.succeed(this.uses) : Effect.fail(resourceSpent)
    })),
    release: (handle: ResourceHandle): Effect.Effect<void> => this.call(2, () => ({ resource: this.claim(handle) }), () => Effect.suspend(() => {
      const slot = this.slot(handle)
      if (!slot.open) return this.misuse("resource released twice")
      slot.open = false
      slot.closes += 1
      return Effect.void
    }))
  }
  async run<A>(program: Effect.Effect<A, Pair>): Promise<{ exit: Exit.Exit<A, Pair>; state: ResourceSnapshot; records: ResourceRecord[]; rootRuntimeFiber: number }> {
    if (this.rootFiber !== undefined) throw this.refuse("resource binding already run")
    const exit = await Effect.runPromiseExit(Effect.withFiber(fiber => { this.rootFiber = fiber.id; return program }))
    if (this.boundaryRefusal) throw this.boundaryRefusal
    return { exit, state: this.snapshot(), records: structuredClone(this.records), rootRuntimeFiber: this.rootFiber! }
  }
  /** Separate cancellation boundary. An uncancellable host allocation may finish after the
   * awaiting Effect is interrupted. The registry then closes the never-delivered object.
   * No response is reported applied, and no finalizer registration is mistaken for cleanup. */
  delayedAcquire(work: Promise<void>): Effect.Effect<ResourceHandle> {
    return Effect.callback((resume, signal) => {
      let delivered = false
      void work.then(() => {
        const physical = this.physical()
        if (signal.aborted) {
          physical.open = false
          physical.closes += 1
          this.compensated.push(physical)
        } else {
          const handle = this.allocate(physical)
          delivered = true
          resume(Effect.succeed(handle))
        }
      }, error => { resume(Effect.die(error)) })
      return Effect.sync(() => {
        // Ownership transfers only at delivery. Before it, the allocation callback retains
        // the obligation to inspect signal.aborted and compensate when work completes.
        if (delivered) return
      })
    })
  }
}

/** Actual exported target type for the resource row descriptor. */
export namespace Host { export type Resource = ResourceHandle }
