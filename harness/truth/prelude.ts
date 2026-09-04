/**
 * prelude.ts — the pure atoms and Ref function names of the native route, on rc.112.
 *
 * What it is: one export per name the printed programs can mention outside the `effect`
 * package: the pure atoms of `src/Effect4/Program/Native.lean` (`nativeAtom`) and the
 * `FnName`s of `src/Effect4/Machine/Stores.lean` (`FnName.total`, `FnName.partialUpdate`).
 * Part of the truth claim: `NOTES.md` §4 is the table mapping each export to its Lean
 * definition. Hand-written transcription (no generator exists for it yet); when either Lean
 * table changes, this file and the NOTES table change with it.
 *
 * Depends on `effect` (`Option`) only.
 *
 * Behaviours held:
 *  - each atom agrees with `nativeAtom` on the values `typeOf` admits — naturals, booleans,
 *    pairs (tested: `run-truth.ts` `selfTest` evaluates the table below against fixed cases
 *    before any program runs);
 *  - `pred` is Lean's truncated subtraction, `pred(0) = 0` (by construction);
 *  - one identifier, one shape: `incr`, `double`, `takeAndBump` are the `FnName.total`
 *    shape `(a) => a` that `Ref.update`/`getAndUpdate`/`updateAndGet` take;
 *    `zeroWhenPositive`, `noChange` are the `FnName.partialUpdate` shape `(a) => Option<a>`
 *    that `Ref.updateSome`/`getAndUpdateSome`/`updateSomeAndGet` take. The `modify` and
 *    `modifySome` shapes (`FnName.modify`, `FnName.modifySome`: `(a) => [b, a']`) are NOT
 *    these identifiers — a printed `Ref.modify(ref, takeAndBump)` would call the total shape
 *    and misbehave on rc.112. Recorded as finding F3 in `REPORT.md`; not patched here.
 */
import { Option } from "effect"

// ---- nativeAtom (Native.lean:59-70) -------------------------------------------------

/** `"succ", [nat n] => nat (n + 1)` */
export const succ = (n: number): number => n + 1
/** `"pred", [nat n] => nat (n - 1)` — Lean `Nat` subtraction truncates at zero. */
export const pred = (n: number): number => (n === 0 ? 0 : n - 1)
/** `"isZero", [nat n] => bool (n = 0)` */
export const isZero = (n: number): boolean => n === 0
/** `"not", [bool b] => bool (!b)` */
export const not = (b: boolean): boolean => !b
/** `"add", [nat a, nat b] => nat (a + b)` */
export const add = (a: number, b: number): number => a + b
/** `"lt", [nat a, nat b] => bool (a < b)` */
export const lt = (a: number, b: number): boolean => a < b
/** `"eq", [nat a, nat b] => bool (a = b)` */
export const eq = (a: number, b: number): boolean => a === b
/** `"pair", [a, b] => Val.tuple [a, b]` — a two-element tuple, the wire's JSON array. */
export const pair = <A, B>(a: A, b: B): readonly [A, B] => [a, b]
/** `"fst", [exitCons a _] => a` */
export const fst = <A, B>(p: readonly [A, B]): A => p[0]
/** `"snd", [exitCons _ (exitCons b _)] => b` */
export const snd = <A, B>(p: readonly [A, B]): B => p[1]

// ---- FnName, total shape (Stores.lean:458-462 `FnName.total`) ------------------------

/** `FnName.incr`: `a ↦ a + 1`. */
export const incr = (a: number): number => a + 1
/** `FnName.double`: `a ↦ 2 * a`. */
export const double = (a: number): number => a * 2
/** `FnName.takeAndBump` under `FnName.total`: `a ↦ a + 1` (its `modify` shape is
 * `a ↦ [a, a + 1]`, not this identifier — see the header). */
export const takeAndBump = (a: number): number => a + 1

// ---- FnName, partial shape (Stores.lean:465-469 `FnName.partialUpdate`) --------------

/** `FnName.zeroWhenPositive`: `Some 0` on a positive cell, `None` otherwise. */
export const zeroWhenPositive = (a: number): Option.Option<number> =>
  a > 0 ? Option.some(0) : Option.none()
/** `FnName.noChange`: `None` always. */
export const noChange = (_a: number): Option.Option<number> => Option.none()

/** The table the runner's self-test walks: `[name, apply, expected]`. */
export const selfTestCases: ReadonlyArray<readonly [string, () => unknown, unknown]> = [
  ["succ 41", () => succ(41), 42],
  ["pred 0", () => pred(0), 0],
  ["pred 5", () => pred(5), 4],
  ["isZero 0", () => isZero(0), true],
  ["isZero 3", () => isZero(3), false],
  ["not true", () => not(true), false],
  ["add 2 3", () => add(2, 3), 5],
  ["lt 2 3", () => lt(2, 3), true],
  ["lt 3 3", () => lt(3, 3), false],
  ["eq 3 3", () => eq(3, 3), true],
  ["fst (pair 1 2)", () => fst(pair(1, 2)), 1],
  ["snd (pair 1 2)", () => snd(pair(1, 2)), 2],
  ["incr 1", () => incr(1), 2],
  ["double 4", () => double(4), 8],
  ["takeAndBump 4", () => takeAndBump(4), 5],
  ["zeroWhenPositive 3", () => Option.getOrUndefined(zeroWhenPositive(3)), 0],
  ["zeroWhenPositive 0 is none", () => Option.isNone(zeroWhenPositive(0)), true],
  ["noChange 7 is none", () => Option.isNone(noChange(7)), true]
]
