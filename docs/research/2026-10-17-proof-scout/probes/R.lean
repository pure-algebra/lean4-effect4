import Tools.Session
import Effect4.Laws.Program.SourceTable

/-!
# Probe R: rebasing an exact edit past another accepted edit

The coordinator's claim: an exact edit certified at one revision keeps the type at the next when
the focus, the address's signature and the base check are unchanged, and the edit has no
reference dependency that the other edit touched.

Verdict: true, with the reference condition made exact.

* On the raw sketch check (`Sketch.check`) it is `Sketch.check_fill_focusAt` itself, with its
  premises read at the new revision (the `example` below). No new lemma.
* On the check through layer references (`Sketch.sourceCheck`) two premises replace "no
  reference dependency": the new source has no reference fault, and its expansion is the old
  expansion's own fill (the test that `SourceSession.feed` runs). `rebase_source` proves that
  these two suffice; both are decided by one traversal and no check.
* The two controls below show each direction of the review's merge counterexample. In both,
  the focus, the signature and the base type are unchanged, yet the rebased source refuses. The
  second edit is reference-free, so a premise on the candidate's own references is not enough.

Placement of `rebase_source`: concept `initial-algebras-folds`, property `typed-replacement`;
question: a step toward automatic rebasing, which no slice A to E consumes. It is scouted here
and not proposed for landing until a consumer exists (`AGENTS.md`, a lemma needs a consumer).
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace ProofScout.R

open Effect4 Effect4.Program Effect4.Store
open Effect4.Machine.Env (Requirement)

/-- On the raw check the claim is the replacement law at the new revision. -/
example {s1 : Sketch} {app : SigApp} {T : EffTy} {path : List Nat} {f : Focus NativeOp}
    {q : NativeEff} (hs1 : s1.check app = .ok T) (hf1 : s1.focusAt app path = some f)
    (hq : Checker.check (Sketch.sigAt { s1 with holes := s1.holes ++ [] } app path) f.env path q =
      .ok f.ty) :
    ∃ s', Sketch.fillAt { s1 with holes := s1.holes ++ [] } path q = some s' ∧ s'.check app = .ok T :=
  Sketch.check_fill_focusAt s1 app hs1 hf1 [] hq

/-- **The source form.** -/
theorem rebase_source {s1 s1' : Sketch} {app : SigApp} {T : EffTy} {path : List Nat}
    {f : Focus NativeOp} {qx : NativeEff}
    (hs : s1.expand.check app = .ok T) (hf : s1.expand.focusAt app path = some f)
    (hq : Checker.check (s1.expand.sigAt app path) f.env path qx = .ok f.ty)
    (hloc : s1.expand.fillAt path qx = some s1'.expand)
    (hfault : s1'.program.firstRefFault = none) :
    s1'.sourceCheck app = .ok T := by
  have hs0 : ({ s1.expand with holes := s1.expand.holes ++ [] } : Sketch) = s1.expand := by
    cases h : s1.expand
    simp only [List.append_nil]
  obtain ⟨s'', hfill, hcheck⟩ := Sketch.check_fill_focusAt s1.expand app hs hf [] (q' := qx)
    (pq := path) (by rw [hs0]; exact hq)
  rw [hs0, hloc, Option.some.injEq] at hfill
  unfold Sketch.sourceCheck
  rw [hfault]
  rw [hfill]
  exact hcheck

/-! ## Controls: the merge counterexample, both ways -/

def nat1 : NativeEff := .succeed (.lit (.nat 1))
def nat2 : NativeEff := .succeed (.lit (.nat 2))
def nat7 : NativeEff := .succeed (.lit (.nat 7))
def strA : NativeEff := .succeed (.lit (.str "a"))
def natTy : EffTy := .pure .nat
def keyA : ServiceKey := ⟨⟨127⟩, ⟨127⟩⟩
def appA : SigApp := { services := [(keyA, .string)] }
def base : Sketch := { program := .bind (.provideLayer (.effect keyA strA) false nat1) nat2 }
def dropLayer : NativeEff := nat7
def addRef : NativeEff := .provideLayer (.ref [0, 0]) false nat2

def focusAtSource (s : Sketch) (path : List Nat) : Option (TyEnv × EffTy) :=
  (s.expand.focusAt appA path).map fun f => (f.env, f.ty)

-- Each edit is accepted at the base through the references.
#guard (base.fillAt [0] dropLayer).map (·.sourceCheck appA) = some (.ok natTy)
#guard (base.fillAt [1] addRef).map (·.sourceCheck appA) = some (.ok natTy)

-- Forward: after the layer is dropped, the reference's focus, signature and base type are
-- unchanged, and its fill refuses.
def afterDrop : Sketch := (base.fillAt [0] dropLayer).getD base
#guard focusAtSource afterDrop [1] = focusAtSource base [1]
#guard afterDrop.sourceCheck appA = .ok natTy
#guard ((afterDrop.fillAt [1] addRef).map (·.program.firstRefFault.isSome)) = some true
#guard ((afterDrop.fillAt [1] addRef).map fun s => (s.sourceCheck appA).toOption) = some none

-- Backward: after the reference is added, the drop's focus, signature and base type are
-- unchanged and its candidate holds no reference, and its fill refuses: it deletes the target.
def afterRef : Sketch := (base.fillAt [1] addRef).getD base
#guard focusAtSource afterRef [0] = focusAtSource base [0]
#guard afterRef.sourceCheck appA = .ok natTy
#guard dropLayer.refSites [] = []
#guard ((afterRef.fillAt [0] dropLayer).map (·.program.firstRefFault.isSome)) = some true
-- The expansion of the rebased source is not the old expansion's own fill: the second premise
-- of `rebase_source` fails too.
#guard ((afterRef.fillAt [0] dropLayer).map fun s =>
  decide ((afterRef.expand.fillAt [0] dropLayer).map (·.program) = some s.expand.program)) =
  some false

end ProofScout.R
