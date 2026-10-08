import Effect4.Laws.Program.Signature
import Effect4.Laws.Program.LoopSound
import Effect4.Laws.Program.MeaningSound

/-!
# Laws.Program.SoundAnySignature — meaning, loop and run soundness at an application's signature

The soundness theorems state their typing at the built-in signature (`meaning_typed`,
`run_typed`, `meaningB_typed`). R1 asks that every milestone statement take the signature as a
parameter. The model probe proved the corollaries at any table (`ce2ece4f`), and the research
sweep dropped them with it (`f7ccf52e`). This module restores them through the tree's own C3
reflection (`effTy_restrict`) instead of the probe's restriction lemma:

* `nativeSignature_dom_sync`: a synchronous operation is in the built-in domain at every table;
* `looped_sigProgram`: a looped program, and so a straight one, is a program of the built-in
  signature. It performs only synchronous operations and reads no service;
* `native_extends_app`: the built-in signature extends to an application's signature over any
  table, with service declarations at fresh codes (`SigApp.FreshCode`);
* `meaning_typed_app`, `run_typed_app` and `meaningB_typed_app`: the three soundness theorems at
  such a signature, by C3's reflection.

Placement (`AGENTS.md`): concept `residual-program-typing`, claim `sound-at-app-signature`.
Reach: straight and looped programs, an application signature over any table whose service
declarations sit at fresh codes. It does not establish soundness for programs that perform host
rows or read services (they are not straight), nor at declarations that rebind a built-in or an
earlier code. It serves R1 ("every milestone statement takes it") for the meaning and run
soundness.
-/

set_option autoImplicit false

namespace Effect4.Program.Denote

open Effect4 Effect4.Machine Effect4.Program

/-- A synchronous operation is in the built-in signature's domain at every table: only a host
row (`external`) is bounded by the table, an invocation by a block (decisions row 328), and the
kind of both is `.program`. -/
theorem nativeSignature_dom_sync (t : RowTable) (op : NativeOp) (h : op.kind = .sync) :
    (nativeSignature t).dom op = true := by
  cases op with
  | external i => cases h
  | call k => cases h
  | _ => rfl

/-- **A looped program is a program of the built-in signature**: every operation it performs
is synchronous, and it reads no service key. -/
theorem looped_sigProgram : ∀ (e : NativeEff), Looped e = true → SigProgram nativeSignature e
  | .succeed _, _ => trivial
  | .fail _, _ => trivial
  | .failCause _, _ => trivial
  | .sync _, _ => trivial
  | .perform op _, h => by
    cases hk : op.kind with
    | sync => exact nativeSignature_dom_sync [] op hk
    | async => simp only [Looped, hk, Bool.false_eq_true] at h
    | program => simp only [Looped, hk, Bool.false_eq_true] at h
  | .iterate _ _ _ _ _ body, h => looped_sigProgram body h
  | .suspend b, h => looped_sigProgram b h
  | .bind a b, h => by
    simp only [Looped, Bool.and_eq_true] at h
    exact ⟨looped_sigProgram a h.1, looped_sigProgram b h.2⟩
  | .select _ _ a b, h => by
    simp only [Looped, Bool.and_eq_true] at h
    exact ⟨looped_sigProgram a h.1, looped_sigProgram b h.2⟩
  | .exit b, h => looped_sigProgram b h
  | .catchCause b k, h => by
    simp only [Looped, Bool.and_eq_true] at h
    exact ⟨looped_sigProgram b h.1, looped_sigProgram k h.2⟩
  | .matchCause b v c, h => by
    simp only [Looped, Bool.and_eq_true] at h
    exact ⟨looped_sigProgram b h.1.1, looped_sigProgram v h.1.2, looped_sigProgram c h.2⟩
  | .onExit b f, h => by
    simp only [Looped, Bool.and_eq_true] at h
    exact ⟨looped_sigProgram b h.1, looped_sigProgram f h.2⟩
  | .gen _, h | .uninterruptible _, h | .interruptible _, h | .yieldNow _, h
  | .awaitFiber _ _, h | .withFiber _, h | .scoped _, h | .acquireRelease _ _, h
  | .provideLayer _ _ _, h | .service _, h | .provideService _ _ _, h
  | .catchIf _ _ _, h | .restore _ _, h =>
    absurd h Bool.false_ne_true

/-- **The built-in signature extends to an application's signature** over any table, with its
service declarations at codes neither the built-in table nor an earlier declaration types. -/
theorem native_extends_app (t : RowTable) (s : List (ServiceKey × Ty))
    (fresh : ∀ entry ∈ s, SigApp.FreshCode ⟨t, []⟩ entry) :
    SigExtends nativeSignature (SigApp.mk t s).signature :=
  (SigApp.rows_append ⟨[], []⟩ t).trans (SigApp.services_append ⟨t, []⟩ s fresh)

/-- A looped program types at an application's signature exactly as at the built-in one. -/
theorem effTy_app_of_looped (t : RowTable) (s : List (ServiceKey × Ty))
    (fresh : ∀ entry ∈ s, SigApp.FreshCode ⟨t, []⟩ entry) (e : NativeEff) (hl : Looped e = true) :
    effTy (SigApp.mk t s).signature [] e = effTy nativeSignature [] e :=
  effTy_restrict (native_extends_app t s fresh) (looped_sigProgram e hl) []

/-- **`meaning_typed` at an application's signature** (R1). -/
theorem meaning_typed_app (t : RowTable) (s : List (ServiceKey × Ty))
    (fresh : ∀ entry ∈ s, SigApp.FreshCode ⟨t, []⟩ entry) (e : NativeEff) (ty : EffTy)
    (hs : Straight e = true) (hty : effTy (SigApp.mk t s).signature [] e = some ty) :
    ExitHasTy ty.answer ty.error (meaning e [] Stores.empty).2 (meaning e [] Stores.empty).1 :=
  meaning_typed e ty hs
    ((effTy_app_of_looped t s fresh e (Looped.of_straight e hs)) ▸ hty)

/-- **`run_typed` (the machine) at an application's signature** (R1). -/
theorem run_typed_app (t : RowTable) (s : List (ServiceKey × Ty))
    (fresh : ∀ entry ∈ s, SigApp.FreshCode ⟨t, []⟩ entry) (e : NativeEff) (ty : EffTy)
    (fuel : Nat) (hs : Straight e = true) (hty : effTy (SigApp.mk t s).signature [] e = some ty)
    (hd : Agreement.depth e ≤ fuel) (hfuel : 2 * Agreement.steps e + 6 ≤ fuel) :
    (Api.run e fuel).outcome = Api.Outcome.finished ∧
      ∃ ex, (Api.run e fuel).exit = some ex ∧
        ExitHasTy ty.answer ty.error (Api.run e fuel).stores ex :=
  run_typed e ty fuel hs ((effTy_app_of_looped t s fresh e (Looped.of_straight e hs)) ▸ hty) hd hfuel

/-- **`meaningB_typed` (loops, any budget) at an application's signature** (R1). -/
theorem meaningB_typed_app (t : RowTable) (s : List (ServiceKey × Ty))
    (fresh : ∀ entry ∈ s, SigApp.FreshCode ⟨t, []⟩ entry) (k : Nat) (e : NativeEff) (ty : EffTy)
    (hl : Looped e = true) (hty : effTy (SigApp.mk t s).signature [] e = some ty)
    {ex : ExitV} {s' : Stores} (h : meaningB k e [] Stores.empty = (some ex, s')) :
    ExitHasTy ty.answer ty.error s' ex :=
  meaningB_typed k e ty hl ((effTy_app_of_looped t s fresh e hl) ▸ hty) h

end Effect4.Program.Denote
