import Effect4.Program.Typing.CheckCache
import Effect4.Laws.Program.Typing.Rebase
import Effect4.Laws.Program.Sketch
import Effect4.Laws.Program.Definitions

/-!
# Laws.Program.Typing.CheckCache — signature data agreement, cache soundness, and candidate evidence

Slice C of `docs/research/2026-10-17-proof-scout/README.md` (§7.3) and `probes/C.lean`.

## Placement

* **Concept**: `initial-algebras-folds`, properties `focus-function` (the signature half) and
  `checker-base-natural`.
* **Question**: the proposed claim `context-check-cache-agrees` (role compatibility), whose pointer
  is `CheckCache.lookup_sound`, with steps `bodyAt_sig_index` (C0), `sketchSigData_signature` (C1),
  and `SigData.extends_of_extendsB` (C3).
* **Reach**: `sketchSigData` at every address in a part (`Eff.partAt`), and `CheckCache.lookup`,
  `CheckCache.insert`, and `CheckCache.evaluateCandidate` over caches of computed entries.
* **What it does not establish**: that distinct `SigData` spell distinct signatures, hash
  injectivity (entries compare whole keys), speed, or reuse of a refusal across an extension.
* **Consumer**: `CheckCache.suggest`, `Tools.Session.answer` (`suggest`), and
  `Test.Program.CheckCacheControls`.
* **Requirement**: R14, serving R2.
-/

set_option autoImplicit false

namespace Effect4.Program

open Effect4 Effect4.Store
open Conform.Effect4.Typing

/-! ## C0 & C1: the data at an address spells the address's signature -/

/-- **C0**: a body's part is at the declaration that the path's index names.

Placement:
1. Concept: `initial-algebras-folds`, property `focus-function`.
2. Question: helper step C0 of `sketchSigData_signature` (C1) for the proposed claim
   `context-check-cache-agrees`.
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
5. Consumer: `CheckCache.suggest` and `Test.Program.CheckCacheControls`. Requirement R14. -/
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

/-! ## C3 & C2: prefix extension and cache lookup soundness -/

/-- **C3: the decided prefix extension (`SigData.extendsB`) is a signature extension
(`SigExtends`).**

Placement:
1. Concept: `initial-algebras-folds`, property `checker-base-natural` and signature extension.
2. Question: step C3 of `CheckCache.lookup_sound` (C2) for the proposed claim
   `context-check-cache-agrees`.
3. Reach: `SigData.extendsB` and `SigExtends`.
4. What it does not establish: preservation of refusals across an extension.
5. Consumer: `CheckCache.lookup_sound`. Requirement R14, serving R2. -/
theorem SigData.extends_of_extendsB {a b : SigData} (h : a.extendsB b = true) :
    SigExtends a.signature b.signature := by
  simp only [SigData.extendsB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hs, ht⟩, hp⟩, hpre⟩ := h
  obtain ⟨more, hmore⟩ := List.isPrefixOf_iff_prefix.mp hpre
  have happ : b.app.withHoles b.holes = (a.app.withHoles a.holes).withHoles more := by
    obtain ⟨⟨arows, asvc, atys⟩, aholes, apart⟩ := a
    obtain ⟨⟨brows, bsvc, btys⟩, bholes, bpart⟩ := b
    simp only [SigData.allRows] at hmore hs ht
    simp only [SigApp.withHoles, hs, ht, List.append_assoc, ← hmore]
  have hext : SigExtends (a.app.withHoles a.holes).signature (b.app.withHoles b.holes).signature := by
    rw [happ]
    exact SigApp.withHoles_extends _ more
  unfold SigData.signature
  rw [← hp]
  cases a.part with
  | root => exact hext
  | block decls => exact hext.withDefs decls
  | body decls ps => exact (hext.withDefs decls).withParams ps

namespace CheckCache

/-- An entry the checker computed at the empty path (`[]`). -/
def Entry.Valid (e : Entry) : Prop :=
  e.verdict = Checker.check e.key.sig.signature e.key.env [] e.key.program

/-- A freshly computed entry (`Entry.compute`) is valid.

Placement:
1. Concept: `initial-algebras-folds`, property `checker-base-natural`.
2. Question: helper step for `insert_valid` and `evaluateCandidate_valid_and_sound`.
3. Reach: `Entry.compute` and `Entry.Valid`.
4. What it does not establish: cache lookup at non-empty paths (`lookup_sound` handles that).
5. Consumer: `insert_valid` and `evaluateCandidate_valid_and_sound`. Requirement R14. -/
theorem Entry.compute_valid (key : CheckKey) : (Entry.compute key).Valid := rfl

/-- **C2: every answer of a cache of computed entries is the checker's answer at the asked path.**

Placement:
1. Concept: `initial-algebras-folds`, property `checker-base-natural` and extension.
2. Question: the proposed claim `context-check-cache-agrees` (role compatibility).
3. Reach: `CheckCache.lookup` on any cache whose entries satisfy `Entry.Valid`.
4. What it does not establish: hash injectivity, speed, or reuse of a refusal across an extension.
5. Consumer: `evaluateCandidate_valid_and_sound`, `Tools.Session.answer` (`suggest`), and
   `Test.Program.CheckCacheControls`. Requirement R14, serving R2. -/
theorem lookup_sound {cache : List Entry} (hv : ∀ e ∈ cache, e.Valid) {key : CheckKey}
    {p : List Nat} {r : Except TypeRefusal EffTy} (h : lookup cache key p = some r) :
    r = Checker.check key.sig.signature key.env p key.program := by
  unfold lookup at h
  split at h
  · rename_i e he
    cases h
    have hkey := List.find?_some he
    rw [decide_eq_true_eq] at hkey
    rw [hv e (List.mem_of_find?_eq_some he), hkey]
    have hr := Checker.check_rebase key.sig.signature p key.env [] key.program
    rw [List.append_nil] at hr
    exact hr.symm
  · split at h
    · rename_i e he
      cases h
      have hp := List.find?_some he
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
      obtain ⟨⟨⟨hprog, henv⟩, hext⟩, hok⟩ := hp
      have hval := hv e (List.mem_of_find?_eq_some he)
      unfold Entry.Valid at hval
      cases hver : e.verdict with
      | error x =>
        rw [hver] at hok
        cases hok
      | ok t =>
        rw [hver] at hval
        have hbase := check_ext (SigData.extends_of_extendsB hext) hval.symm
        rw [hprog, henv] at hbase
        have hr := Checker.check_rebase key.sig.signature p key.env [] key.program
        rw [List.append_nil, hbase] at hr
        exact hr.symm
    · cases h

/-- Inserting a computed entry preserves `Entry.Valid` on the cache.

Placement:
1. Concept: `initial-algebras-folds`, property `checker-base-natural`.
2. Question: cache invariant maintenance for `context-check-cache-agrees`.
3. Reach: `CheckCache.insert` and `Entry.Valid`.
4. What it does not establish: eviction or size bounds.
5. Consumer: `Test.Program.CheckCacheControls`. Requirement R14. -/
theorem insert_valid {cache : List Entry} (hv : ∀ e ∈ cache, e.Valid) (key : CheckKey) :
    ∀ e ∈ insert cache key, e.Valid := by
  intro e he
  unfold insert at he
  split at he
  · exact hv e he
  · rcases List.mem_cons.mp he with rfl | hmem
    · exact Entry.compute_valid key
    · exact hv e hmem

/-- **Evaluating a candidate preserves `Entry.Valid` on the cache and produces evidence that agrees
with `Checker.check` at the target context.**

Placement:
1. Concept: `initial-algebras-folds`, property `checker-base-natural`.
2. Question: contextual evidence soundness for `suggest` under `context-check-cache-agrees`.
3. Reach: `CheckCache.evaluateCandidate` on a valid cache.
4. What it does not establish: scope shifting of candidates from a different environment (Slice F).
5. Consumer: `Tools.Session.answer` (`suggest`) and `Test.Program.CheckCacheControls`.
   Requirement R14. -/
theorem evaluateCandidate_valid_and_sound {cache : List Entry} (hv : ∀ e ∈ cache, e.Valid)
    (sig : SigData) (targetEnv : TyEnv) (expected : EffTy) (targetPath : List Nat)
    (sourcePath : Option (List Nat)) (sourceEnv : TyEnv) (prog : NativeEff) :
    let res := evaluateCandidate cache sig targetEnv expected targetPath sourcePath sourceEnv prog
    (∀ e ∈ res.1, e.Valid) ∧
      match res.2.evidence with
      | .exactFit ty _ =>
        Checker.check sig.signature targetEnv targetPath prog = .ok ty ∧ ty = expected
      | .typeMismatch exp act _ =>
        Checker.check sig.signature targetEnv targetPath prog = .ok act ∧ exp = expected
      | .refused why _ =>
        Checker.check sig.signature targetEnv targetPath prog = .error why
      | .differentEnv sEnv tEnv =>
        sEnv = sourceEnv ∧ tEnv = targetEnv ∧ sEnv ≠ tEnv := by
  dsimp only [evaluateCandidate]
  cases hsame : decide (sourceEnv = targetEnv) with
  | false =>
    rw [if_neg Bool.false_ne_true]
    refine ⟨hv, rfl, rfl, ?_⟩
    intro heq
    rw [decide_eq_true heq] at hsame
    cases hsame
  | true =>
    rw [if_pos rfl]
    let key : CheckKey := ⟨prog, sig, targetEnv⟩
    have hbranch :
        let triple :=
          match lookup cache key targetPath with
          | some v => (cache, v, true)
          | none =>
            let e := Entry.compute key
            (e :: cache, e.verdict.mapError (fun (r : TypeRefusal) => (⟨targetPath ++ r.path, r.reason⟩ : TypeRefusal)), false)
        (∀ e ∈ triple.1, e.Valid) ∧
          triple.2.1 = Checker.check sig.signature targetEnv targetPath prog := by
      cases hlk : lookup cache key targetPath with
      | some v =>
        exact ⟨hv, lookup_sound hv hlk⟩
      | none =>
        refine ⟨?_, ?_⟩
        · intro e he
          rcases List.mem_cons.mp he with rfl | hmem
          · exact Entry.compute_valid key
          · exact hv e hmem
        · dsimp only [Entry.compute, key]
          have hr := Checker.check_rebase sig.signature targetPath targetEnv [] prog
          rw [List.append_nil] at hr
          exact hr.symm
    obtain ⟨hcv, hverd⟩ := hbranch
    refine ⟨hcv, ?_⟩
    cases hv_eq :
        (match lookup cache key targetPath with
          | some v => (cache, v, true)
          | none =>
            (Entry.compute key :: cache,
              (Entry.compute key).verdict.mapError (fun (r : TypeRefusal) => (⟨targetPath ++ r.path, r.reason⟩ : TypeRefusal)),
              false)).2.1 with
    | error why =>
      dsimp only
      rw [hv_eq] at hverd
      exact hverd.symm
    | ok ty =>
      dsimp only
      rw [hv_eq] at hverd
      cases hty : decide (ty = expected) with
      | true =>
        rw [if_pos rfl]
        exact ⟨hverd.symm, decide_eq_true_eq.mp hty⟩
      | false =>
        rw [if_neg Bool.false_ne_true]
        exact ⟨hverd.symm, rfl⟩

end CheckCache

end Effect4.Program
