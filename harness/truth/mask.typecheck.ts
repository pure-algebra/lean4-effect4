/**
 * mask.typecheck.ts: the mask's saved state under the one compiler, at the prelude's alias
 * `MaskRestore` (decisions rows 244 to 246). A finite compiler control, not a run: `check-truth`
 * type-checks it beside the printed modules. Each `@ts-expect-error` line is a red control that
 * the compiler must keep refusing.
 *
 * The three positive bodies are Lean's own text: the module that `Api.printModule` prints for a
 * program of `Test/Program/MaskClaims.lean`, which pins each text in full. Only the constant's
 * name differs: the printed module names it `main`. Each one states the saved state's type in
 * an annotated position, which no printed module of the truth corpus does: the two truth
 * programs of the mask answer numbers and Booleans (`harness/truth/Truth.lean`, `pMaskWait` and
 * `pMaskedRestore`).
 *
 * What this control states: the compiler accepts the getter's answer at the alias, in a tuple,
 * in a promise and in a cell, and it accepts a restore site of a value read back from a cell.
 * It states no run and no law of the mask: the laws are in
 * `src/Effect4/Laws/Program/Typed/Mask.lean` and `src/Effect4/Laws/Codegen/Mask.lean`.
 * The three red controls are hand-written, because the checker refuses each program before
 * the printer sees it (`TypeReason.maskRestoreExpected`, `predicateNotBool`).
 */
import { Deferred, Effect, Ref, pipe } from "effect"
import { not, tuple, type MaskRestore } from "./prelude.ts"

// S1 of the fixture (`Test.Program.MaskContract.s1`): the getter under an interruptible caller
// and under a masked one. The answer is a tuple of two saved states.
export const flags: Effect.Effect<readonly [MaskRestore, MaskRestore], never, never> = Effect.flatMap(Effect.uninterruptibleMask((a0) => Effect.succeed(a0)), (a0) => Effect.flatMap(Effect.uninterruptible(Effect.uninterruptibleMask((a1) => Effect.succeed(a1))), (a1) => Effect.succeed(tuple(a0, a1))))

// A saved state kept in a promise and awaited (`Test.Program.MaskClaims.keptInPromise`). The
// promise's type argument is the alias.
export const keptInPromise: Effect.Effect<MaskRestore, never, never> = Effect.flatMap(Deferred.make<MaskRestore, never>(), (a0) => Effect.flatMap(Effect.uninterruptibleMask((a1) => Effect.succeed(a1)), (a1) => Effect.flatMap(Deferred.succeed(a0, a1), (a2) => Deferred.await(a0))))

// A saved state kept in a cell, read back, and applied at a restore site whose body is the
// getter (`Test.Program.MaskClaims.keptInCell`).
export const keptInCell: Effect.Effect<MaskRestore, never, never> = Effect.flatMap(Effect.uninterruptibleMask((a0) => Effect.succeed(a0)), (a0) => Effect.flatMap(Ref.make(a0), (a1) => Effect.flatMap(Ref.get(a1), (a2) => pipe(Effect.uninterruptibleMask((a3) => Effect.succeed(a3)), a2))))

// Red controls. Without its expectation line each one reports its own error under tsgo 7:
// TS2345 for the first two, and TS2375 for the third (seat MASK's receipt).

// A Boolean is no saved state: a restore site of `true` has no type.
// @ts-expect-error a Boolean is no saved state
export const redBooleanAsSaved = Effect.uninterruptible(pipe(Effect.succeed(1), true))

// A saved state is no Boolean: it has no type where a Boolean is asked.
// @ts-expect-error a saved state is no Boolean
export const redSavedAsBoolean = (saved: MaskRestore) => not(saved)

// A restore site answers its body's type, and no other.
// @ts-expect-error a restore site answers its body's type
export const redSiteType = (saved: MaskRestore): Effect.Effect<string, never, never> => pipe(Effect.succeed(1), saved)
