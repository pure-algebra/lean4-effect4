import Effect4.Laws.Program.LoopSound
import Effect4.Laws.Program.LoopAgreement
import Effect4.Laws.Program.Agreement.Loop
import Effect4.Laws.Program.ReferenceTyping
import Effect4.Program.CheckedTyping

/-!
# Soundness, read off the typing certificate

`MeaningSound.lean` and `LoopSound.lean` are stated over `effTy` at the empty environment. What
a caller holds is a `TypedProgram`: the result of the one whole-program checker
(`typeOfProgram`), which resolves layer references first. A program of the loop-bearing
fragment has no layer reference (`Looped.refSites_nil`), so the checker's answer is `effTy`'s
(`typeOfProgram_looped`), and every soundness theorem reads on the certificate.

`TypedProgram.run_sound` is the statement for the machine on the straight fragment, at a fixed
budget. `TypedProgram.run_soundB` is the statement for the whole loop-bearing fragment: when a
certified program's budgeted meaning finishes, its exit has the type, and the machine finishes
with that exit and those stores at every fuel past a bound (`Agreement.loopAgreement`, O12).
`run_sound_of_agreement` is the same statement from the agreement as a premise; it is kept
because it is how the next fragment will be stated before its agreement is proved.
-/

set_option autoImplicit false

namespace Effect4.Program.Denote

open Effect4 Effect4.Machine Effect4.Program

/-- A program of the loop-bearing fragment has no layer reference, at any path. -/
theorem Looped.refSites_nil : ∀ (e : NativeEff) (p : List Nat), Looped e = true →
    e.refSites p = []
  | .iterate _ _ _ _ _ body, p, h => by
    show Eff.refSites _ body = []
    exact Looped.refSites_nil body _ (Looped.iterate h)
  | .suspend b, p, h => by
    show Eff.refSites _ b = []
    exact Looped.refSites_nil b _ (Looped.suspend h)
  | .exit b, p, h => by
    show Eff.refSites _ b = []
    exact Looped.refSites_nil b _ (Looped.exit h)
  | .bind a b, p, h => by
    show Eff.refSites _ a ++ Eff.refSites _ b = []
    rw [Looped.refSites_nil a _ (Looped.bind h).1, Looped.refSites_nil b _ (Looped.bind h).2]
    rfl
  | .select _ _ a b, p, h => by
    show Eff.refSites _ a ++ Eff.refSites _ b = []
    rw [Looped.refSites_nil a _ (Looped.select h).1, Looped.refSites_nil b _ (Looped.select h).2]
    rfl
  | .catchCause a b, p, h => by
    show Eff.refSites _ a ++ Eff.refSites _ b = []
    rw [Looped.refSites_nil a _ (Looped.catchCause h).1,
      Looped.refSites_nil b _ (Looped.catchCause h).2]
    rfl
  | .onExit a b, p, h => by
    show Eff.refSites _ a ++ Eff.refSites _ b = []
    rw [Looped.refSites_nil a _ (Looped.onExit h).1, Looped.refSites_nil b _ (Looped.onExit h).2]
    rfl
  | .matchCause a b c, p, h => by
    show Eff.refSites _ a ++ (Eff.refSites _ b ++ Eff.refSites _ c) = []
    rw [Looped.refSites_nil a _ (Looped.matchCause h).1,
      Looped.refSites_nil b _ (Looped.matchCause h).2.1,
      Looped.refSites_nil c _ (Looped.matchCause h).2.2]
    rfl
  | .succeed _, _, _ | .fail _, _, _ | .failCause _, _, _
  | .sync _, _, _ | .perform _ _, _, _ => rfl
  | .gen _, _, h | .uninterruptible _, _, h | .interruptible _, _, h
  | .yieldNow _, _, h
  | .awaitFiber _ _, _, h | .withFiber _, _, h | .scoped _, _, h
  | .acquireRelease _ _, _, h | .provideLayer _ _ _, _, h | .service _, _, h
  | .provideService _ _ _, _, h | .catchIf _ _ _, _, h => absurd h Bool.false_ne_true

/-- On the loop-bearing fragment the whole-program checker is `effTy` at the empty
environment. -/
theorem typeOfProgram_looped (sig : Signature NativeOp) (e : NativeEff) (hl : Looped e = true) :
    typeOfProgram sig e = effTy sig [] e := by
  have hrefs := Looped.refSites_nil e [] hl
  have hfixed := expandRefs_eq_self_of_refSites_nil e hrefs
  have hwf := layerRefsWF_of_refSites_nil e hrefs
  simp [typeOfProgram, hwf, hfixed, hrefs, typeOf]

/-- **A certified straight program runs to an exit of its type.** -/
theorem TypedProgram.run_sound {e : NativeEff} (tp : TypedProgram nativeSignature e)
    (hs : Straight e = true) (fuel : Nat) (hd : Agreement.depth e ≤ fuel)
    (hfuel : 2 * Agreement.steps e + 6 ≤ fuel) :
    (Api.run e fuel).outcome = Api.Outcome.finished ∧
      ∃ ex, (Api.run e fuel).exit = some ex ∧
        ExitOk tp.ty.answer tp.ty.error (Api.run e fuel).stores ex := by
  have hty : effTy nativeSignature [] e = some tp.ty := by
    rw [← typeOfProgram_looped nativeSignature e (Looped.of_straight e hs)]
    exact tp.typed
  exact run_typed e tp.ty fuel hs hty hd hfuel

/-- **A certified loop-bearing program, given the loop agreement.** When its budgeted meaning
finishes, the machine finishes past some fuel with that exit, and the exit has the type. -/
theorem TypedProgram.run_sound_of_agreement {e : NativeEff}
    (tp : TypedProgram nativeSignature e) (hl : Looped e = true)
    (hagree : Agreement.LoopAgreement e) {k : Nat} {ex : ExitV} {s' : Stores}
    (h : meaningB k e [] Stores.empty = (some ex, s')) :
    ExitOk tp.ty.answer tp.ty.error s' ex ∧
      ∃ bound, ∀ fuel, bound ≤ fuel →
        (Api.run e fuel).outcome = Api.Outcome.finished ∧
          (Api.run e fuel).exit = some ex ∧ (Api.run e fuel).stores = s' := by
  have hty : effTy nativeSignature [] e = some tp.ty := by
    rw [← typeOfProgram_looped nativeSignature e hl]
    exact tp.typed
  exact ⟨meaningB_typed k e tp.ty hl hty h, hagree k ex s' h⟩

/-- **A certified loop-bearing program runs on the machine to an exit of its type.** When its
budgeted meaning finishes, the exit has the program's type, and the machine's ordinary run
finishes with that exit and those stores at every fuel past a bound. -/
theorem TypedProgram.run_soundB {e : NativeEff} (tp : TypedProgram nativeSignature e)
    (hl : Looped e = true) {k : Nat} {ex : ExitV} {s' : Stores}
    (h : meaningB k e [] Stores.empty = (some ex, s')) :
    ExitOk tp.ty.answer tp.ty.error s' ex ∧
      ∃ bound, ∀ fuel, bound ≤ fuel →
        (Api.run e fuel).outcome = Api.Outcome.finished ∧
          (Api.run e fuel).exit = some ex ∧ (Api.run e fuel).stores = s' :=
  TypedProgram.run_sound_of_agreement tp hl (Agreement.loopAgreement e hl) h

end Effect4.Program.Denote
