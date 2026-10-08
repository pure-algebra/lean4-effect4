import Effect4.Laws.Program.Typed.Mask
import Effect4.Laws.Codegen.Mask
import Effect4.Laws.Program.Authoring.Mask
import Test.Program.MaskContract
import TypeScript.Render

/-!
# The mask's five claims: their statements, and the printed form

The five registry claims of the mask (`tools/Tools/SemanticsRegistry.lean`) have their
statements in `src/Effect4/Laws/Program/Typed/Mask.lean` and
`src/Effect4/Laws/Codegen/Mask.lean`. This battery reads the claims' statements, and
it holds the finite controls of the printed form: a mask around one wait prints
as the note's F5 shows, and it reads back.

Every pin of rendered text is inside a `#guard`: a definition that folds over a rendered
string reaches `Classical.choice`.

It establishes no agreement with a target. tsgo 7 checks the printed modules in the truth
lane (`harness/truth/Truth.lean`, `pMaskWait` and `pMaskedRestore`). The same lane checks the
alias in its annotated positions: `harness/truth/mask.typecheck.ts` copies three modules that
this battery pins.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Test.Program.MaskClaims

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Typed Effect4.Program.Authoring
open Test.Program.MaskContract
open TypeScript (house0)
open TypeScript.Render (expr)

/-! ## The printed form (the note's F5) -/

/-- A mask around one wait, by the surface's builder. -/
def maskAroundWait : Src NativeOp := eff do
  let d ← Deferred.make .nat .never
  uninterruptibleMaskWith fun restore => restore (Deferred.await d)

-- The builder is the program's own expansion: the getter under a `bind`, the body under
-- `uninterruptible`, the restore site with its body at child 0.
#guard buildOf (mk maskAroundWait) = some
  (.bind (.perform (.deferredMakeOf .nat .never) (.lit .unit))
    (.bind (.withFiber .getInterruptible)
      (.uninterruptible (.restore (.var 1) (.perform .deferredAwait (.var 0))))))

-- It prints row by row, in the public API, as F5 shows.
#guard ((buildOf (mk maskAroundWait)).map fun p => (Api.print p).map (expr house0 0)) = some (.ok
  "Effect.flatMap(Deferred.make<number, never>(), (a0) => Effect.flatMap(Effect.uninterruptibleMask((a1) => Effect.succeed(a1)), (a1) => Effect.uninterruptible(pipe(Deferred.await(a0), a1))))")

-- It is readable, and what it prints reads back to it.
#guard (buildOf (mk maskAroundWait)).all fun p =>
  Api.readable p && decide (Api.roundTrip p = .ok p)

-- An annotated position prints the alias's name: the type's target names the prelude's alias
-- for the restore function's type (`harness/truth/prelude.ts`, `MaskRestore`).
#guard ((buildOf (mk s1)).bind fun p => (Api.printModule "main" p).map fun m =>
    String.join (m.decls.map (TypeScript.Render.decl house0))) = some
  "export const main: Effect.Effect<readonly [MaskRestore, MaskRestore], never, never> = Effect.flatMap(Effect.uninterruptibleMask((a0) => Effect.succeed(a0)), (a0) => Effect.flatMap(Effect.uninterruptible(Effect.uninterruptibleMask((a1) => Effect.succeed(a1))), (a1) => Effect.succeed(tuple(a0, a1))))\n"

-- Every scenario of the fixture is readable and reads back: the two rows, in ten programs.
#guard engineRuns.all fun (_, src) => (buildOf (mk src)).all fun p =>
  Api.readable p && decide (Api.roundTrip p = .ok p)

/-! ## A saved state as data (decisions row 246)

A saved state is a value of its own type, so a promise and a cell hold it. Each program below
is built, runs to the image of an interruptible caller's flag, and prints the alias in its
annotated positions. `harness/truth/mask.typecheck.ts` copies the two modules of this section
and the module of `s1` above, and tsgo 7 type-checks them in the truth lane. -/

/-- A saved state kept in a promise and awaited. -/
def keptInPromise : Src NativeOp := eff do
  let p ← Deferred.make Ty.maskRestore .never
  let saved ← flag
  let _ ← Deferred.succeed p saved
  Deferred.await p

/-- A saved state kept in a cell, read back, and applied at a restore site whose body is the
getter. -/
def keptInCell : Src NativeOp := eff do
  let saved ← flag
  let c ← Ref.make saved
  let again ← Ref.get c
  restore again flag

#guard verdict (mk keptInPromise) = "built" && verdict (mk keptInCell) = "built"
#guard [keptInPromise, keptInCell].all fun src => (buildOf (mk src)).all fun p =>
  decide (Api.typeOf p = some ⟨Ty.maskRestore, .never, Env.Requirement.empty⟩)
#guard exitOf keptInPromise = some (.success open_) && exitOf keptInCell = some (.success open_)

-- The two printed modules. Each rendering stays inside its guard, as the header says.
#guard ((buildOf (mk keptInPromise)).bind fun p => (Api.printModule "main" p).map fun m =>
    String.join (m.decls.map (TypeScript.Render.decl house0))) = some
  "export const main: Effect.Effect<MaskRestore, never, never> = Effect.flatMap(Deferred.make<MaskRestore, never>(), (a0) => Effect.flatMap(Effect.uninterruptibleMask((a1) => Effect.succeed(a1)), (a1) => Effect.flatMap(Deferred.succeed(a0, a1), (a2) => Deferred.await(a0))))\n"
#guard ((buildOf (mk keptInCell)).bind fun p => (Api.printModule "main" p).map fun m =>
    String.join (m.decls.map (TypeScript.Render.decl house0))) = some
  "export const main: Effect.Effect<MaskRestore, never, never> = Effect.flatMap(Effect.uninterruptibleMask((a0) => Effect.succeed(a0)), (a0) => Effect.flatMap(Ref.make(a0), (a1) => Effect.flatMap(Ref.get(a1), (a2) => pipe(Effect.uninterruptibleMask((a3) => Effect.succeed(a3)), a2))))\n"

-- The cell's program reads back. The promise's does not: its type argument is a handle type,
-- which is outside the readable types, and the reader refuses it by name. It prints all the same.
#guard (buildOf (mk keptInCell)).all fun p => Api.readable p && decide (Api.roundTrip p = .ok p)
#guard (buildOf (mk keptInPromise)).all fun p => !Api.readable p &&
  decide (Api.roundTrip p = .error (.annotation "Deferred.make type argument"))

-- Red controls. A restore site of a Boolean reads back as well: the equations are about
-- program syntax, and typing is another judgment. A restore site whose saved term is out of
-- scope is not readable.
#guard Api.readable (.restore (.lit (.bool true)) (.succeed (.lit (.nat 1)))) &&
  decide (Api.roundTrip (.restore (.lit (.bool true)) (.succeed (.lit (.nat 1)))) =
    .ok (.restore (.lit (.bool true)) (.succeed (.lit (.nat 1)))))
#guard Api.typeOf (.restore (.lit (.bool true)) (.succeed (.lit (.nat 1)))) [] = none
#guard !Api.readable (.restore (.var 0) (.succeed (.lit (.nat 1))))

/-! ## The claims' statements, read at one input each

Each line reads one field of a top node at a concrete input. They are no new evidence: they
show that the statement is the one the fixture's guards test. -/

-- Membership at the saved state's type is the two images, at the empty world's shape check.
example : Val.hasTy (Val.savedMask true) Ty.maskRestore [] = true :=
  (saved_mask_image_membership.shape [] _).mpr ⟨true, rfl⟩
example (w : Typed.World) : ¬ Fits w (Val.bool true) Ty.maskRestore :=
  saved_mask_image_membership.boolNot w true
example (w : Typed.World) : ¬ Fits w (Val.savedMask false) .bool :=
  saved_mask_image_membership.notBool w false

-- A restore site binds nothing, and its body is child 0.
example (saved : Term) (body : NativeEff) :
    (Node.eff (.restore saved body) : Node NativeOp).child 0 = some (.eff body) :=
  (scoped_body_substitution_boundary.child saved body).1

-- The saved frame returns the flag it holds, on any exit.
example (fr : Effect4.Program.Sched.FFiber) :
    ((Prim.setInterruptible true : NCode).ensure fr).fst.interruptible = true :=
  (saved_mask_restoration.returned true fr).1

-- The derived form is readable exactly when its body is, one level up.
example (body : NativeEff) :
    Readable [] (nativeSignature []) 0 (maskForm body) =
      Readable [] (nativeSignature []) 1 body :=
  Effect4.Program.mask_printed_form_profile.readable [] (nativeSignature []) 0 body

end Test.Program.MaskClaims
