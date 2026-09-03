import * as Effect from "effect/Effect"
import type * as Scheduler from "effect/Scheduler"

/** Public Effect code only. The separate controller supplies scheduling and replies. */
export function begin(
  masked: boolean,
  cancellation: boolean,
  scheduler: Scheduler.Scheduler,
  ordinaryFinalizer = false
) {
  const events: Array<string> = []
  let firstReply: () => void = () => { throw new Error("first callback not registered") }
  let secondReply: () => void = () => { throw new Error("second callback not registered") }
  const first = Effect.callback<number>((resume) => {
    events.push("register:first")
    firstReply = () => resume(Effect.succeed(42))
    if (cancellation) return Effect.sync(() => { events.push("cancel:first") })
  })
  const initial = ordinaryFinalizer
    ? Effect.onExit(first, () => Effect.sync(() => { events.push("finalize:first") }))
    : first
  const program = Effect.flatMap(initial, (value) => {
    events.push(`between:${value}`)
    return Effect.callback<number>((resume) => {
      events.push("register:second")
      secondReply = () => resume(Effect.succeed(7))
    })
  })
  const fiber = Effect.runFork(masked ? Effect.uninterruptible(program) : program, { scheduler })
  return { fiber, events, replyFirst: () => firstReply(), replySecond: () => secondReply() }
}
