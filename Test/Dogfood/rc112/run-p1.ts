/** Program 1 on rc.112 with a scripted host: `fetch` is replaced by a fake whose answers are a
 * tape. Attempt 1 hangs until its AbortSignal fires (the 2 s timeout interrupts it); attempt 2
 * answers 503; attempt 3 answers 200 with a JSON body. Then the cache serves the second get. */
import { Effect, Exit } from "effect"
import { program, fetchQuote } from "./p1-http-cache.ts"

const calls: Array<string> = []
let attempt = 0
;(globalThis as any).fetch = (url: string, init?: { signal?: AbortSignal }) => {
  attempt += 1
  const n = attempt
  calls.push(`call ${n} ${url}`)
  if (n === 1) {
    return new Promise((_resolve, reject) => {
      init?.signal?.addEventListener("abort", () => {
        calls.push(`abort ${n}`)
        reject(new Error("aborted"))
      })
    })
  }
  if (n === 2) return Promise.resolve({ ok: false, status: 503, url, json: async () => ({}) })
  return Promise.resolve({ ok: true, status: 200, url, json: async () => ({ symbol: "EFX", price: 21 }) })
}

const t0 = Date.now()
const answer = await Effect.runPromise(program)
console.log("p1 answer", answer, "elapsedMs>=2000", Date.now() - t0 >= 2000)
console.log("p1 host", JSON.stringify(calls))
// A 404 is not retried (the `while` predicate), and the typed error reaches catchTag: -404.
attempt = 10
;(globalThis as any).fetch = (url: string) => {
  calls.push(`call404 ${url}`)
  return Promise.resolve({ ok: false, status: 404, url, json: async () => ({}) })
}
const exit = await Effect.runPromiseExit(fetchQuote("NOPE"))
console.log("p1 404", Exit.isFailure(exit) ? JSON.stringify(exit.cause) : "success", "calls", calls.filter((c) => c.startsWith("call404")).length)
