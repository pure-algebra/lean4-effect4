/** Retargeted from foldlab experiments/lift-harness/src/gate.ts at 4005d34f.
 * Agreement is exact verdict equality in source order. An absent run is not a pass.
 */
import { canonJson, verdictKey, type Verdict } from "./contract.ts"

export type Agreement =
  | { readonly status: "not-run" }
  | { readonly status: "agree"; readonly count: number }
  | { readonly status: "disagree"; readonly indices: readonly number[] }

export function compareVerdicts(left: readonly Verdict[] | undefined, right: readonly Verdict[] | undefined): Agreement {
  if (left === undefined || right === undefined) return { status: "not-run" }
  const indices: number[] = []
  for (let i = 0; i < Math.max(left.length, right.length); i++) {
    const a = left[i], b = right[i]
    if (!a || !b || canonJson(verdictKey(a)) !== canonJson(verdictKey(b))) indices.push(i)
  }
  return indices.length ? { status: "disagree", indices } : { status: "agree", count: left.length }
}
