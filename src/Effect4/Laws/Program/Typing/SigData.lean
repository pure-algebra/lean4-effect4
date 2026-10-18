import Effect4.Program.Typing.Suggest
import Effect4.Laws.Program.Typing.Rebase
import Effect4.Laws.Program.Sketch
import Effect4.Laws.Program.Definitions

/-!
# Signature data at a source address

The retained connectors identify the signature represented by a source part key.
`bodyAt_sig_index` supplies the definition-body case of `sketchSigData_signature`.
Their observation covers successful part selection at an address, under the application's hole table.
They establish no program admission, runtime behavior, or native cache performance.

V1 replaces the former cache laws with certified `Memo` and lawful `HitRule`.
`CheckAgreement` places the complete verdict and extension obligations under initial-algebras-folds and R14.
Source part-key correspondence retains these connectors for the editing laws.
-/

set_option autoImplicit false

namespace Effect4.Program

open Effect4 Effect4.Store
open Conform.Effect4.Typing

/-! ## C0 & C1: the data at an address spells the address's signature -/

/-- **C0**: a body's part is at the declaration that the path's index names.

Placement:
1. Concept: `initial-algebras-folds`, property `focus-function`.
2. Question: helper step C0 of `sketchSigData_signature` (C1) for source part-key correspondence.
3. Reach: `Part.bodyAt` and `bodyIndex` over definition lists and body spines.
4. What it does not establish: typing of the body itself.
5. Consumer: `sketchSigData_signature`. Requirement R14. -/
theorem bodyAt_sig_index (sig : Signature NativeOp) :
    ∀ (decls : List DefDecl) (bodies : Effs NativeOp) (path : List Nat) (part : Part NativeOp)
      (rest : List Nat), Part.bodyAt sig decls bodies path = some (part, rest) →
      ∃ d, ((bodyIndex path).bind fun k => decls[k]?) = some d ∧
        part.sig = sig.withParams d.params
  | [], .nil, _, _, _, h => by cases h
  | [], .cons _ _, _, _, _, h => by cases h
  | _ :: _, .nil, _, _, _, h => by cases h
  | _ :: _, .cons _ _, [], _, _, h => by cases h
  | d :: _, .cons _ _, 0 :: _, _, _, h => by
    cases h
    exact ⟨d, rfl, rfl⟩
  | _ :: ds, .cons _ bodies, 1 :: p, part, rest, h => by
    obtain ⟨d, hd, hs⟩ := bodyAt_sig_index sig ds bodies p part rest h
    refine ⟨d, ?_, hs⟩
    cases hk : bodyIndex p with
    | none =>
      rw [hk] at hd
      cases hd
    | some k =>
      rw [hk] at hd
      simp only [bodyIndex, hk, Option.map_some, Option.bind_some, List.getElem?_cons_succ]
      exact hd
  | _ :: _, .cons _ _, (_ + 2) :: _, _, _, h => by cases h

/-- **C1: the data at an address spells the address's signature**, where the address is in a part
(as at every typed focus).

Placement:
1. Concept: `initial-algebras-folds`, property `focus-function` (the signature half).
2. Question: step C1 of the proposed claim `context-check-cache-agrees` (role compatibility).
3. Reach: every `Sketch`, `SigApp` and `path` inside a part (`Eff.partAt`).
4. What it does not establish: that two different `SigData` spell two different signatures.
5. Consumer: `Suggest.page` and `Test.Program.SuggestControls`. Requirement R14. -/
theorem sketchSigData_signature (s : Sketch) (app : SigApp) (path : List Nat)
    (hpart : (s.program.partAt (app.withHoles s.holes).signature [] path).isSome = true) :
    (sketchSigData s app path).signature = s.sigAt app path := by
  unfold sketchSigData Sketch.sigAt SigData.signature
  cases hp : s.program
  case defs decls bodies main layers =>
    rw [hp] at hpart
    match path, layers, hpart with
    | [], _, hpart => cases hpart
    | 0 :: rest, _, hpart =>
      simp only [Eff.partAt] at hpart ⊢
      cases hb : Part.bodyAt ((app.withHoles s.holes).signature.withDefs decls) decls bodies rest with
      | none =>
        rw [hb] at hpart
        cases hpart
      | some pr =>
        obtain ⟨part, r⟩ := pr
        obtain ⟨d, hd, hs⟩ := bodyAt_sig_index _ decls bodies rest part r hb
        simp only [partSigAt, hd, Option.map_some, Option.getD_some, hs]
    | 1 :: _, _, _ => rfl
    | 2 :: _, .nil, hpart => cases hpart
    | 2 :: _, .cons _ _, _ => rfl
    | (_ + 3) :: _, _, hpart => cases hpart
  all_goals rfl



end Effect4.Program
