/**
 * The receipt sink for abort-path witness persistence.
 *
 * A session that ends by interruption or defect persists its aborted
 * witness from inside the session's own finalizer — owned by the session
 * fiber, bounded by an explicit deadline, never detached. The write's
 * outcome is delivered here as one receipt per persistence attempt, so a
 * witness written on the abort path is discoverable and a sacrificed one
 * (store failure, deadline) is observable instead of silent. The default
 * sink drops receipts; production compositions override the reference
 * per scope or per layer. A sink can never fail the session it observes.
 */
import { Context, Effect } from "effect"
import type { CasError, ContentId } from "../cas/Node.ts"

export interface WitnessReceipt {
  readonly executionId: string
  /** Why the session aborted: an interrupt, or a transported defect. */
  readonly reason: "Interrupted" | "Defect"
  readonly result:
    | { readonly _tag: "Persisted"; readonly witness: ContentId }
    | { readonly _tag: "Failed"; readonly error: CasError }
    | { readonly _tag: "TimedOut" }
}

export interface WitnessSinkShape {
  readonly record: (receipt: WitnessReceipt) => Effect.Effect<void>
}

export const WitnessSink: Context.Reference<WitnessSinkShape> =
  Context.Reference("foldlab/effect-replay/WitnessSink", {
    defaultValue: (): WitnessSinkShape => ({ record: () => Effect.void }),
  })
