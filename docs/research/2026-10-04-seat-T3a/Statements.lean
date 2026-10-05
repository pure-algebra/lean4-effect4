import Effect4.Laws.Program.Typed.Denotation
import Effect4.Laws.Program.Template
import Effect4.Codegen.Types

/-! Prototype for seat T3a's design note (phase 1), at the base `b1c80550`. It edits no tree file.

1. The restated `syncRow_typed`, per instantiation, elaborates; at the base, where every row is
   closed, it follows from today's theorem by the closed reduction. T3a's proof reads the match.
2. The restated handle inversions and the read at the instance, proved at the base.
3. The brief's anchored completeness, stated with a scratch `anchored`; refuted for today's match by
   the union counterexample (`Anchored.lean`), by the kernel.
4. Row 183's `bitEntry` at the instance, elaborated.
5. Scratch versions of the formation rule for a deferred's error column and row 155's fold.
6. The face facts T3a's faces rest on: today's spellings are the type projection of the instances.

Replay: `lake env lean docs/research/2026-10-04-seat-T3a/Statements.lean` under the shared lock. -/

open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.Typed (ProgramSource TypedProg RefDeclared PromiseDeclared fits_sub fits_normalize
  fits_subN syncRow_typed typedProg_widen subN_normalize₂)

namespace T3aStatements

/-! ## 1. `syncRow_typed` per instantiation -/

/-- The statement T3a restates: the node's checked instance `t`, read off the row's match at the
request's type, types the store operation. -/
theorem syncRow_typed_at (root : ProgramSource) {w : Typed.World} {req : Env.Requirement}
    (op : NativeOp) (hk : NativeOp.kind op = .sync) {reqTy : Ty} {t : EffTy}
    (hrow : rowTy (NativeOp.row op).normalizeTypes reqTy = some t)
    (v : Val) (hfit : Typed.Fits w v reqTy) :
    ∃ o, NativeOp.syncOpOf op v = some o ∧
      TypedProg root w ⟨t.answer, t.error, req⟩ (.vis (.inl o) fun ans => .pure (.success ans)) := by
  have hc := NativeOp.row_closed op
  obtain ⟨hsub, rfl⟩ := rowTy_closed_some (Ty.closed_normalize _ hc.1)
    (Ty.closed_normalize _ hc.2.1) (Ty.closed_normalize _ hc.2.2) hrow
  have hreq : Typed.Fits w v (NativeOp.row op).request := by
    have h := fits_sub w hsub v ((fits_normalize w reqTy v).mpr hfit)
    exact (fits_normalize w _ v).mp ((fits_normalize w _ v).mp h)
  obtain ⟨o, ho, typed⟩ := syncRow_typed root (req := req) op hk v hreq
  exact ⟨o, ho, typedProg_widen root (subN_normalize₂ (Ty.subN_refl _))
    (subN_normalize₂ (Ty.subN_refl _)) typed⟩

/-! ## 2. The handle inversions at the instance, and the read -/

theorem fits_refOf_inv {w : Typed.World} {v : Val} {A : Ty} (h : Typed.Fits w v (.refOf A)) :
    ∃ k, v = Val.cell k ∧ RefDeclared w k A := by
  simp only [Typed.Fits] at h
  split at h
  · rename_i index
    exact ⟨⟨index⟩, rfl, h⟩
  · exact h.elim

theorem fits_deferredOf_inv {w : Typed.World} {v : Val} {A E : Ty} (h : Typed.Fits w v (.deferredOf A E)) :
    ∃ k, v = Val.promise k ∧ PromiseDeclared w k A E := by
  simp only [Typed.Fits] at h
  split at h
  · rename_i index
    exact ⟨⟨index⟩, rfl, h⟩
  · exact h.elim

/-- `refRead_nat` at the instance: the proof never read `nat`. -/
theorem refRead {w : Typed.World} {key : RefKey} {A ty : Ty} {ans : Val}
    (hdecl : RefDeclared w key A) (hlookup : w.Ρ key = some ty) (hfit : Typed.Fits w ans ty) :
    Typed.Fits w ans A := by
  obtain ⟨t', hlookup', hequiv⟩ := hdecl
  rw [hlookup] at hlookup'
  cases hlookup'
  exact fits_subN w hequiv.1 ans hfit

/-! ## 3. Anchored completeness, and its refutation for today's `infer` -/

/-- A parameter occurrence in `infer`'s order, flagged when it is the direct argument of an
invariant handle. Scratch: records, tuples and applications are not walked. -/
def occ : Ty → List (Nat × Bool)
  | .var i => [(i, false)]
  | .refOf a => (match a with | .var i => [(i, true)] | _ => occ a)
  | .deferredOf a e =>
    (match a with | .var i => [(i, true)] | _ => occ a) ++
      (match e with | .var i => [(i, true)] | _ => occ e)
  | .option t | .list t | .causeOf t => occ t
  | .prod a b | .except a b | .exitOf a b | .fiberOf a b | .union a b | .map a b => occ a ++ occ b
  -- scratch: the nested lists are not walked here; the tree's version is a generated fold
  | _ => []

/-- Every parameter's first occurrence is at an invariant handle argument. -/
def anchored (t : Ty) : Bool :=
  let o := occ t
  (List.range o.length).all fun k =>
    match o[k]? with
    | some (i, inv) => inv || (o.take k).any (·.1 == i)
    | none => true

def setT : Ty := .prod (.refOf (.var 0)) (.var 0)
def setR : Ty := .prod (.refOf .string) (.union (.lit "a") (.lit "b"))

#guard anchored (.refOf (.var 0))
#guard anchored setT
#guard anchored (.deferredOf (.var 0) (.var 1))
#guard anchored (.prod (.deferredOf (.var 0) (.var 1)) (.var 0))
#guard anchored (.prod (.deferredOf (.var 0) (.var 1)) (.var 1))
-- `Ref.make`'s request is a bare parameter: not anchored, and complete by the match's first arm
#guard !anchored (.var 0)
#guard !anchored (.prod (.var 0) (.refOf (.var 0)))

/-- The brief's statement, with the guard as `checkRow` reads it. -/
def CompleteAnchored : Prop :=
  ∀ (t r : Ty) (τ : Ty.Subst), Ty.templateAdmissible t = true → anchored t = true →
    Ty.Normal r → Ty.sub r (t.instantiate τ).normalize = true →
    ∃ σ, Ty.matchTemplate [] t r = some σ

/-- **Refuted for today's `infer`**: the normal request of `Ref.set(cell, x)` with
`x : "a" | "b"` is a union of products, and `infer` binds nothing against a union. -/
theorem completeAnchored_refuted : ¬ CompleteAnchored := by
  intro h
  obtain ⟨σ, hσ⟩ := h setT setR.normalize [(0, .string)] (by decide +kernel) (by decide +kernel)
    (Ty.normal_normalize _) (by decide +kernel)
  have hnone : Ty.matchTemplate [] setT setR.normalize = none := by decide +kernel
  rw [hnone] at hσ
  cases hσ

/-! ## 4. Row 183: `bitEntry` at the row's instance -/

def bitEntryAt (root : ProgramSource) (op : NativeOp) (cert : EffTy) : Prop :=
  root.signature.dom op = true ∧
    ∃ reqTy t, rowTy (root.signature.rowOf op) reqTy = some t ∧
      t.answer.sub cert.answer = true ∧ t.error.sub cert.error = true

/-! ## 5. Scratch: the formation rule for a deferred's error column, and row 155's fold -/

def headFormedAt (template : Bool) : Ty → Bool
  | .deferredOf _ e => admittedErrTy e || (template && !e.closed)
  | t => decide (Formation.HeadFormed template t)

#guard headFormedAt false (.deferredOf .nat .nat)
#guard headFormedAt false (.deferredOf .unit .never)
#guard headFormedAt false (.deferredOf .nat .string)
#guard !headFormedAt false (.deferredOf .nat .bool)
#guard !headFormedAt false (.deferredOf .nat (.var 1))
#guard headFormedAt true (.deferredOf (.var 0) (.var 1))
-- a tagged record payload is an admitted error type (decisions row 120)
#guard headFormedAt false (.deferredOf .unit
  (.record [("_tag", false, .lit "JobFailed"), ("id", false, .nat), ("reason", false, .string)]))

/-- Row 155 (a): a row column reads a parameter as inhabited. -/
def rowInhabitedAlg : TyAlgebra (fun _ => Bool) := { inhabitedAlg with ty_var := fun _ => true }
def admitRowColumn (t : Ty) : Bool := t.normalize == .never || cata_ty rowInhabitedAlg t

#guard admitRowColumn (.var 0)
#guard admitRowColumn (.refOf (.var 0))
#guard !admitRowColumn (.prod (.var 0) .never)
#guard !admitColumn (.var 0)
-- on closed columns the two checks agree
#guard ([Ty.never, .nat, .prod .never .nat, .except .never .never, .list .int, .refOf .nat,
  .union .never .string, .tuple [.nat, .never]] : List Ty).all fun t =>
  admitRowColumn t == admitColumn t

/-! ## 6. The faces: today's spellings are the instances' type projection -/

#guard (Ty.refOf .nat).render == "Ref.Ref<number>"
#guard (Ty.deferredOf .nat .nat).render == "Deferred.Deferred<number, number>"
#guard Codegen.Types.ofTy (.refOf .nat) == Codegen.Types.parseLegacy "Ref.Ref<number>"
#guard Codegen.Types.ofTy (.deferredOf .nat .nat) ==
  Codegen.Types.parseLegacy "Deferred.Deferred<number, number>"
-- the empty spelling has no legacy reading, so a row carrying it is refused by the printer
#guard Codegen.Types.parseLegacy "" == none
-- p3's gate, `Deferred<void>`, projects; T5 prints it as `Deferred.make<void, never>()`
#guard (Codegen.Types.ofTy (.deferredOf .unit .never)).isSome

end T3aStatements

#print axioms T3aStatements.syncRow_typed_at
#print axioms T3aStatements.fits_refOf_inv
#print axioms T3aStatements.fits_deferredOf_inv
#print axioms T3aStatements.refRead
#print axioms T3aStatements.completeAnchored_refuted
