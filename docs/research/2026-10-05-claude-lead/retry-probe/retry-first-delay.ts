// The delay before each retry under an exponential schedule (2026-10-06). One finite host run
// on real time, not a proof.
//
// Run: EFFECT_DIR=<an effect package directory> bun run retry-first-delay.ts
// The attempt fails three times and then succeeds. The output gives the time of each attempt,
// in milliseconds from the first, rounded to the nearest 50.
import { readFileSync } from "node:fs"

const dir = process.env.EFFECT_DIR!
const version: string = JSON.parse(readFileSync(`${dir}/package.json`, "utf8")).version
const { Effect, Schedule } = await import(`${dir}/dist/index.js`)

const base = 100
const times: Array<number> = []
let start = 0
const attempt = Effect.suspend(() => {
  const now = Date.now()
  if (times.length === 0) start = now
  times.push(now - start)
  return times.length <= 3 ? Effect.fail("again") : Effect.succeed("ok")
})

const answer = await Effect.runPromise(
  Effect.retry(attempt, { schedule: Schedule.exponential(base), times: 3 })
)
const rounded = times.map((t) => Math.round(t / 50) * 50)
const delays = rounded.slice(1).map((t, i) => t - rounded[i])
console.log(JSON.stringify({
  effect: version,
  runtime: `bun ${Bun.version}`,
  base,
  answer,
  attemptTimesRoundedTo50: rounded,
  delayBeforeEachRetry: delays
}, null, 1))
