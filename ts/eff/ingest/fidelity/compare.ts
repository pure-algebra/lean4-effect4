import { canonJson } from "../contract.ts"
import type { Observed } from "./fidelity-contract.ts"
/** Compare an original unit's observation with its reprint's: the exit, whether the run parked,
 * and the schedule without its `scheduled` rows. An observation that could not run never agrees.
 * The alphabet is the deleted truth runner's (`git:8e93a284f:git:9c197bb67:harness/truth/run-truth.ts`); the
 * runner of the observations went with it on 2026-10-20. */
export function compareObserved(original: Observed, printed: Observed) {
  if (original.status !== "observed" || printed.status !== "observed") return { status: "could-not-run" as const, exitAgree: null, scheduleAgree: null }
  const a = original.observation, b = printed.observation
  const schedule = (s: readonly string[]) => s.filter(r => !r.startsWith("scheduled "))
  const exitAgree = a.parked === b.parked && canonJson(a.exit) === canonJson(b.exit)
  const scheduleAgree = canonJson(schedule(a.schedule)) === canonJson(schedule(b.schedule))
  return { status: exitAgree && scheduleAgree ? "agree" as const : "disagree" as const, exitAgree, scheduleAgree }
}
