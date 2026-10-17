import Tools.Session
import Effect4.Laws.Program.Typing.Rebase
import Effect4.Laws.Program.Sketch
import Effect4.Laws.Program.Definitions
import Effect4.Program.Scoped

/-!
# Probe C: contextual evidence as data, and a checker-verdict cache

Slice C of the authoring review. The signature of an address is a function, so a cache key
holds the data it is derived from (`SigData`). Two proposed lemmas, and the controls of the
review's findings B and C.

* `sketchSigData_signature`: the data at an address gives the signature that `Sketch.sigAt`
  answers there, at every address in a part. The data is read off the root and the path, so the
  key adds no traversal of a program (decisions row 143). Placement: concept `initial-algebras-folds`, property `focus-function` (the
  address's signature is the focus's other half); question: a step of the proposed claim
  `context-check-cache-agrees`. Reach: every sketch, application and address. It does not
  establish that two different data give different signatures. Consumer: the cache key below and
  slice B's `inspect`, which shows the context as data. Requirement R14.
* `lookup_sound`: every answer of the cache is the checker's answer at the key's signature,
  environment and the asked path. An exact hit rebases its refusal (`Checker.check_rebase`); a
  positive verdict also answers at a prefix extension of its rows (`check_ext`,
  `SigApp.withHoles_extends`, `SigExtends.withDefs`, `SigExtends.withParams`); a refusal is
  reused at equal data only. Placement: concept `initial-algebras-folds`; question: the proposed
  claim `context-check-cache-agrees` (role compatibility), whose pointer this lemma would be.
  Reach: a cache whose entries were each computed by the checker. It does not establish hash
  injectivity (entries compare whole keys), any speed, or reuse of a refusal across an
  extension (control B shows it would be wrong). Consumer: the candidate catalogue (`suggest`)
  and `replace`. Requirement R14, serving R2.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace ProofScout.C

open Effect4 Effect4.Program Effect4.Store
open Effect4.Machine.Env (Requirement)
open Conform.Effect4.Typing

/-! ## The signature at an address, as data -/

/-- Which part of a whole program an address is in, as data. -/
inductive PartSig where
  /-- the application's signature with the hole table -/
  | root
  /-- a block's main program or its module layers: the block's signature -/
  | block (decls : List DefDecl)
  /-- a block's body: the block's signature with the body's parameters -/
  | body (decls : List DefDecl) (params : List ParamDecl)
deriving DecidableEq

/-- The data that the signature at an address is derived from. -/
structure SigData where
  app : SigApp
  holes : RowTable
  part : PartSig

/-- The signature that the data spells. -/
def SigData.signature (d : SigData) : Signature NativeOp :=
  match d.part with
  | .root => (d.app.withHoles d.holes).signature
  | .block decls => (d.app.withHoles d.holes).signature.withDefs decls
  | .body decls ps => ((d.app.withHoles d.holes).signature.withDefs decls).withParams ps

/-- The index of the body that an address inside a block's bodies' spine names: each `1` steps
along the spine, and `0` enters the body. Path arithmetic only: no walk of the program. -/
def bodyIndex : List Nat → Option Nat
  | 0 :: _ => some 0
  | 1 :: rest => (bodyIndex rest).map (· + 1)
  | _ => none

/-- The part of an address, as data, read off the root's declarations and the path: a one-level
case analysis of the root (decisions row 143), no traversal. -/
def partSigAt (p : NativeEff) (path : List Nat) : PartSig :=
  match p, path with
  | .defs decls _ _ _, 0 :: rest =>
    match (bodyIndex rest).bind fun k => decls[k]? with
    | some d => .body decls d.params
    | none => .root
  | .defs decls _ _ _, 1 :: _ => .block decls
  | .defs decls _ _ (.cons _ _), 2 :: _ => .block decls
  | _, _ => .root

/-- The data at an address of a sketch. -/
def sketchSigData (s : Sketch) (app : SigApp) (path : List Nat) : SigData :=
  ⟨app, s.holes, partSigAt s.program path⟩

/-- A step: a body's part is at the declaration that the path's index names. -/
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

/-- **The data at an address spells the address's signature**, where the address is in a part
(as at every typed focus). -/
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

/-! ## The cache -/

deriving instance DecidableEq for SigApp
deriving instance DecidableEq for SigData

/-- A cache key: the program's content, the signature's data and the ordered environment. The
path is not part of it (`Checker.check_rebase`). -/
structure CheckKey where
  program : NativeEff
  sig : SigData
  env : TyEnv
deriving DecidableEq

/-- An entry: a key and the checker's verdict at the empty path. -/
structure Entry where
  key : CheckKey
  verdict : Except TypeRefusal EffTy

/-- An entry the checker computed. -/
def Entry.Valid (e : Entry) : Prop :=
  e.verdict = Checker.check e.key.sig.signature e.key.env [] e.key.program

/-- The rows of the data's sketch signature. -/
def SigData.allRows (d : SigData) : RowTable := d.app.rows ++ d.holes

/-- **A prefix extension, decided**: the same services, named types and part, and rows that
extend the old rows at their end. -/
def SigData.extendsB (a b : SigData) : Bool :=
  decide (a.app.services = b.app.services) && decide (a.app.types = b.app.types) &&
    decide (a.part = b.part) && a.allRows.isPrefixOf b.allRows

/-- The decided prefix extension is a signature extension. -/
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

/-- **A lookup**: an exact hit answers its verdict, its refusal moved below the asked path; a
positive verdict at a prefix extension answers too; anything else is a miss. -/
def lookup (cache : List Entry) (key : CheckKey) (p : List Nat) :
    Option (Except TypeRefusal EffTy) :=
  match cache.find? (fun e => decide (e.key = key)) with
  | some e => some (e.verdict.mapError (TypeRefusal.rebase p))
  | none =>
    match cache.find? (fun e => decide (e.key.program = key.program) &&
        decide (e.key.env = key.env) && e.key.sig.extendsB key.sig && e.verdict.toBool) with
    | some e => some e.verdict
    | none => none

/-- **Every answer of a cache of computed entries is the checker's.** -/
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

/-! ## Controls -/

def rowsSmall : SigApp := { rows := [Row.hole "n" .nat] }
def rowsLarge : SigApp := { rows := [Row.hole "n" .nat, Row.hole "s" .string] }
def call0 : NativeEff := .perform (.external 0) (.lit .unit)
def call1 : NativeEff := .perform (.external 1) (.lit .unit)
def natTy : EffTy := .pure .nat

def dataAt (app : SigApp) : SigData := ⟨app, [], .root⟩
def computed (program : NativeEff) (d : SigData) (env : TyEnv) : Entry :=
  ⟨⟨program, d, env⟩, Checker.check d.signature env [] program⟩

-- The prefix extension is decided as wanted: the larger row table extends the smaller one.
#guard (dataAt rowsSmall).extendsB (dataAt rowsLarge)
#guard !(dataAt rowsLarge).extendsB (dataAt rowsSmall)

-- An exact hit rebases its refusal at the asked path (finding C).
def badVar : NativeEff := .bind (.succeed (.lit (.nat 1))) (.succeed (.var 42))
def cache1 : List Entry := [computed badVar (dataAt rowsSmall) []]
#guard lookup cache1 ⟨badVar, dataAt rowsSmall, []⟩ [8, 4] =
  some (Checker.check rowsSmall.signature [] [8, 4] badVar)
#guard lookup cache1 ⟨badVar, dataAt rowsSmall, []⟩ [8, 4] !=
  some (Checker.check rowsSmall.signature [] [] badVar)

-- A positive verdict answers at a prefix extension (`check_ext`) ...
def cache2 : List Entry := [computed call0 (dataAt rowsSmall) []]
#guard lookup cache2 ⟨call0, dataAt rowsLarge, []⟩ [3] = some (.ok natTy)

-- ... and a refusal does not: the missing row appears, and the program checks (finding B).
def cache3 : List Entry := [computed call1 (dataAt rowsSmall) []]
#guard (Checker.check rowsSmall.signature [] [] call1).toOption.isNone
#guard (Checker.check rowsLarge.signature [] [] call1).toOption = some (.pure .string)
#guard lookup cache3 ⟨call1, dataAt rowsLarge, []⟩ [] = none

-- The key keeps the ordered environment (control C3) and the row table (control C2).
def readVar0 : NativeEff := .succeed (.var 0)
#guard Checker.check (dataAt {}).signature [.nat] [] readVar0 !=
  Checker.check (dataAt {}).signature [.string] [] readVar0
def natApp : SigApp := { rows := [Row.hole "external" .nat] }
def strApp : SigApp := { rows := [Row.hole "external" .string] }
#guard Checker.check (dataAt natApp).signature [] [] call0 != Checker.check (dataAt strApp).signature [] [] call0
#guard !(dataAt natApp).extendsB (dataAt strApp)

-- A program that reads no outside variable still reads its own binders by level, so its bytes
-- type differently one level deeper (control C3), and the cache answers only at its own
-- environment. Moving it needs the shift of slice F (`Eff.weaken`, `effTy_weaken`).
def closedAtRoot : NativeEff := .bind (.succeed (.lit (.nat 7))) (.succeed (.var 0))
#guard closedAtRoot.scopedAt 0
#guard Checker.check (dataAt {}).signature [] [] closedAtRoot = .ok natTy
#guard Checker.check (dataAt {}).signature [.string] [] closedAtRoot = .ok (.pure .string)
def cache4 : List Entry := [computed closedAtRoot (dataAt {}) []]
#guard lookup cache4 ⟨closedAtRoot, dataAt {}, [.string]⟩ [] = none
#guard Checker.check (dataAt {}).signature [.string] [] (Eff.weaken 0 closedAtRoot) = .ok natTy

-- The data at an address inside a block names the body's parameters: a filling inside a body is
-- checked at the block's signature, so a key at the root's signature would be a different key.
def fDecl : DefDecl := { name := "f", request := .unit, answer := .nat }
def blockSketch : Sketch :=
  { program := .defs [fDecl] (.cons (.succeed (.lit (.nat 1))) .nil) (.succeed (.lit (.nat 2))) .nil }
#guard partSigAt blockSketch.program [0, 0] = .body [fDecl] []
#guard partSigAt blockSketch.program [0, 1, 0] = .root
#guard partSigAt blockSketch.program [1] = .block [fDecl]
#guard partSigAt blockSketch.program [] = .root

end ProofScout.C
