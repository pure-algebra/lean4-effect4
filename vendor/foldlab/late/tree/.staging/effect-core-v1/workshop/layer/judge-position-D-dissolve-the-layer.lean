import Cas.Backend.Universal
import Cas.Backend.SumAlgebra

/-!
# ADVERSARIAL AUDIT of position D ("dissolve the layer")

Judge's probe. Adds nothing to `Cas`, edits nothing in `library/`.
`cd library/cas && lake env lean ../../.staging/effect-core-v1/workshop/layer/judge-position-D-dissolve-the-layer.lean`
-/

namespace JudgeD

open Cas.Lang

/-! ## ATTACK 1 — D's carrier IS position A's carrier, and `build` is `id`. -/

abbrev Layer (S T : Sig) : Type := Prog T (Handler S (Prog T))

-- propose-D.lean §1, verbatim.
def PosD.build   (L : Layer S T) : Prog T (Handler S (Prog T)) := L
def PosD.andThen (L : Layer S T) (M : Layer T U) : Layer S U :=
  M >>= fun g => interpret g L >>= fun h => pure (h.through g)
def PosD.provide (L : Layer S T) (p : Prog S A) : Prog T A :=
  L >>= fun h => interpret h p

-- propose-A.lean:76 and :93, verbatim.
def PosA.provide (inner : Layer T U) (outer : Layer S T) : Layer S U :=
  inner >>= fun ht => interpret ht outer >>= fun hs => Pure.pure (hs.through ht)
def PosA.run (l : Layer S T) (p : Prog S A) : Prog T A :=
  l >>= fun h => interpret h p

/-- **D's `andThen` IS position A's `provide`.** Not "similar": the same term,
arguments flipped. The two positions share a byte-identical carrier line. -/
theorem D_andThen_is_A_provide (L : Layer S T) (M : Layer T U) :
    PosD.andThen L M = PosA.provide M L := rfl

/-- **D's `provide` IS position A's `run`.** -/
theorem D_provide_is_A_run (L : Layer S T) (p : Prog S A) :
    PosD.provide L p = PosA.run L p := rfl

/-- **D's headline — "`build` is the identity function" — is the `abbrev`
unfolding, not a design finding.** `Layer S T` IS `Prog T (Handler S (Prog T))`
definitionally, so `build` is `@id`. It takes no memo map, no scope, and no
floor, so it is not rc.112's `build` member in any checkable sense. -/
theorem D_build_is_literally_id : @PosD.build S T = @id (Layer S T) := rfl

/-! ## ATTACK 2 — `scope_survives_composition` has no scope in it. -/

def injHandler : Handler S (Prog (S ⊕ₛ T)) where
  handle op := Prog.inl (Prog.op op)

theorem interpret_injHandler (p : Prog S A) :
    interpret (injHandler (S := S) (T := T)) p = Prog.inl p := by
  induction p with
  | pure a => rfl
  | vis op k ih =>
    show Prog.bind (Prog.inl (Prog.op op)) _ = _
    simp only [Prog.op, Prog.inl, Prog.bind]
    exact congrArg (Prog.vis (Sum.inl op)) (funext fun a => ih a)

/-- propose-D.lean's `scope_survives_composition`, verbatim. -/
theorem scope_survives_composition
    (g : Handler B (Prog (Sc ⊕ₛ B'))) (p : Prog Sc A) :
    interpret (Handler.sum (injHandler (S := Sc) (T := B')) g) (Prog.inl p)
      = Prog.inl p := by
  rw [interpret_inl]; exact interpret_injHandler p

inductive ArithE where | add | neg
abbrev ArithE.Ans : ArithE → Type | .add => Nat | .neg => Nat
def ArithSig : Sig := ⟨ArithE, ArithE.Ans⟩

/-- **The lemma holds verbatim with arithmetic in the "scope" slot.** `Sc` is
an unconstrained `Sig`; rename it and nothing changes. It is `interpret_inl`
composed with a passthrough — a naturality fact about `Handler.sum` with zero
scope content. It cannot be "R18's floor question, answered": it mentions no
finalization, no ordering, no acquisition, and no target monad. -/
theorem the_lemma_is_not_about_scope
    (g : Handler B (Prog (ArithSig ⊕ₛ B'))) (p : Prog ArithSig A) :
    interpret (Handler.sum (injHandler (S := ArithSig) (T := B')) g)
        (Prog.inl p) = Prog.inl p :=
  scope_survives_composition g p

/-! ## ATTACK 3 — the lemma's hypothesis excludes every acquiring scoped layer.

`Prog.inl p` is a program in the LEFT summand ALONE (`Prog.lean:39`: it maps
every `vis` to `Sum.inl`). A scoped layer that acquires performs a BASE
operation in its build, so its build is an interleaved `Prog (Sc ⊕ₛ B) _` and
is never of that form. The lemma covers only builds with no base operations —
i.e. exactly not a scoped layer. -/

inductive ScE where | openS | closeS
abbrev ScE.Ans : ScE → Type | .openS => Unit | .closeS => Unit
def ScSig : Sig := ⟨ScE, ScE.Ans⟩

inductive BaseE where | acq | rel
abbrev BaseE.Ans : BaseE → Type | .acq => Unit | .rel => Unit
def BaseSig : Sig := ⟨BaseE, BaseE.Ans⟩

inductive Base'E where | acq' | rel'
abbrev Base'E.Ans : Base'E → Type | .acq' => Unit | .rel' => Unit
def Base'Sig : Sig := ⟨Base'E, Base'E.Ans⟩

inductive UpE where | use
abbrev UpE.Ans : UpE → Type | .use => Unit
def UpSig : Sig := ⟨UpE, UpE.Ans⟩

/-- A genuinely scoped, genuinely acquiring layer: acquire the resource, then
open the scope that owns it, then serve. The build interleaves `Base` and `Sc`
operations. -/
def scopedAcquiringL : Layer UpSig (ScSig ⊕ₛ BaseSig) :=
  .vis (Sum.inr BaseE.acq) (fun _ =>
    .vis (Sum.inl ScE.openS) (fun _ =>
      .pure ⟨fun _ => .vis (Sum.inr BaseE.rel) .pure⟩))

/-- **The shape mismatch, checked.** No `q` puts this layer inside the lemma's
hypothesis: its build's first node is a right-summand operation. -/
theorem the_needed_case_is_outside_the_lemma
    (q : Prog ScSig (Handler UpSig (Prog (ScSig ⊕ₛ BaseSig)))) :
    scopedAcquiringL ≠ Prog.inl q := by
  cases q with
  | pure a => intro h; simp [scopedAcquiringL, Prog.inl] at h
  | vis op k =>
    intro h
    injection h with h1 _
    exact absurd h1 (by simp)

/-- The log target: markers, so the kernel reduction stays cheap.
0=open 1=close 2=acq 3=rel -/
def logH : Handler (ScSig ⊕ₛ Base'Sig) (StateM (List Nat)) where
  handle
    | .inl .openS  => fun l => ((), l ++ [0])
    | .inl .closeS => fun l => ((), l ++ [1])
    | .inr .acq'   => fun l => ((), l ++ [2])
    | .inr .rel'   => fun l => ((), l ++ [3])

/-- A passthrough middle: relabel `Base` to `Base'`, inject `Sc` untouched. -/
def midH : Handler BaseSig (Prog (ScSig ⊕ₛ Base'Sig)) where
  handle
    | .acq => .vis (Sum.inr Base'E.acq') .pure
    | .rel => .vis (Sum.inr Base'E.rel') .pure

def midL : Layer (ScSig ⊕ₛ BaseSig) (ScSig ⊕ₛ Base'Sig) :=
  pure (Handler.sum (injHandler (S := ScSig) (T := Base'Sig)) midH)

def oneUse : Prog UpSig Unit := .vis UpE.use .pure

/-- The composite does preserve the scope operation. This is checked HERE, not
inherited from D's lemma, which does not apply to `scopedAcquiringL`. -/
theorem composite_log :
    (interpret logH (PosD.provide (PosD.andThen scopedAcquiringL midL) oneUse)
      []).2 = [2, 0, 3] := by decide

/-! ## ATTACK 4 — "the tower has ONE floor" does not follow from the lemma.

The lemma says a passthrough does not DELETE scope operations. It says nothing
about a middle layer ADDING them, and one can: `g`'s clauses are
`Prog (Sc ⊕ₛ B')`-valued, so any intermediate layer may open scopes of its
own. "Scope operations reach the bottom handler unchanged" is therefore not a
property of the composite, even with the injection on the left. -/

def scopeInjectingH : Handler BaseSig (Prog (ScSig ⊕ₛ Base'Sig)) where
  handle
    | .acq => .vis (Sum.inl ScE.openS)
                (fun _ => .vis (Sum.inr Base'E.acq') .pure)
    | .rel => .vis (Sum.inl ScE.closeS)
                (fun _ => .vis (Sum.inr Base'E.rel') .pure)

def scopeInjectingL : Layer (ScSig ⊕ₛ BaseSig) (ScSig ⊕ₛ Base'Sig) :=
  pure (Handler.sum (injHandler (S := ScSig) (T := Base'Sig)) scopeInjectingH)

/-- A middle layer meeting every hypothesis of D's lemma on the left summand,
which still rewrites the composite's scope trace. -/
theorem middle_layer_injects_scope_operations :
    (interpret logH (PosD.provide
      (PosD.andThen scopedAcquiringL scopeInjectingL) oneUse) []).2
      = [0, 2, 0, 1, 3] := by decide

theorem scope_trace_is_not_preserved :
    (interpret logH (PosD.provide
      (PosD.andThen scopedAcquiringL scopeInjectingL) oneUse) []).2
      ≠ (interpret logH (PosD.provide
      (PosD.andThen scopedAcquiringL midL) oneUse) []).2 := by decide

/-! ## ATTACK 5 — D's own R18 repair is not wired to D's `Layer`.

In propose-D.lean, `ensT` is applied to `interpret baseH usingThenFail` — a
fully interpreted TARGET value. The file defines no `ScopeSig`, no scope
handler, and no floor: the R18-compliant finalizer never becomes a clause of
anything. -/

abbrev RM := ExceptT String (StateM (List String))

def ensT (body fin : RM A) : RM A := fun l =>
  match body l with
  | (.ok a, l₁) =>
    match fin l₁ with
    | (.ok _, l₂) => (.ok a, l₂)
    | (.error r, l₂) => (.error r, l₂)
  | (.error r, l₁) => (.error r, (fin l₁).2)

/-- **R18 / EC1-CE045 compliance, confirmed generically.** State is OUTSIDE
error, so on the body's refusal the finalizer still runs, its state survives,
and the refusal is reported unchanged. D passes this test. -/
theorem ensT_is_R18_compliant (body fin : RM Nat)
    (r : String) (l l' : List String) (hb : body l = (.error r, l')) :
    ensT body fin l = (.error r, (fin l').2) := by
  simp only [ensT, hb]

/-- The scope clause D's prose requires — a `Handler` whose `ensuring` arm is
`ensT` — is absent from propose-D.lean. It elaborates, so the design is
buildable; it is simply not built. propose-A.lean builds the same object at
`ReaderT Env (ExceptT Refusal (StateM Word))` and checks `LawfulMonad`
synthesizes there. -/
inductive ScopeOpE where | ensuring (body fin : Nat)
abbrev ScopeOpE.Ans : ScopeOpE → Type | .ensuring _ _ => Unit
def ScopeOpSig : Sig := ⟨ScopeOpE, ScopeOpE.Ans⟩

def scopeClause (blocks : Nat → RM Unit) : Handler ScopeOpSig RM where
  handle | .ensuring b f => ensT (blocks b) (blocks f)

example (blocks : Nat → RM Unit) : Handler ScopeOpSig RM := scopeClause blocks

end JudgeD

section Receipts
open JudgeD
#print axioms D_andThen_is_A_provide
#print axioms D_provide_is_A_run
#print axioms D_build_is_literally_id
#print axioms the_lemma_is_not_about_scope
#print axioms the_needed_case_is_outside_the_lemma
#print axioms composite_log
#print axioms middle_layer_injects_scope_operations
#print axioms scope_trace_is_not_preserved
#print axioms ensT_is_R18_compliant
end Receipts
