import Effect4.Program.Sketch
import Effect4.Laws.Program.Signature
import Effect4.Laws.Program.Typing.Replace
import Effect4.Laws.Program.Typing.Focus
import Effect4.Laws.Program.Typing.Parts
import Effect4.Laws.Auto.Semantics

/-!
# Laws.Program.Sketch — a sketch's language is a conservative extension of the program's

`Program/Sketch.lean` defines a sketch: a program with its hole table, where a hole is a host
row with a declared type and the hole table stands after the application's rows. This module
holds its laws. Each one is an instance of a law of Σ_app that had landed
(`Laws/Program/Signature.lean`, decisions rows 111 to 116): a hole table appended after the rows
is an extension of the application's typing signature (`SigApp.withHoles_extends`), so the
checker's two extension theorems apply.

| Statement | In words | From |
| --- | --- | --- |
| `Sketch.check_program` | a program is a sketch with no hole: its check is the checker's answer | the definition |
| `holes_conservative` (H1) | a program that performs no hole is checked the same with any hole table, refusals included | `check_restrict` |
| `sketch_more_holes` (H2) | a sketch stays admitted, at the same type, when more holes are declared | `check_ext` |
| `sketch_reads_its_holes` (H3) | the checker reads the rows of the holes that the sketch performs, and no later row | `check_restrict` |
| `Sketch.hole_hasTy` | a hole has its declared type, in every environment | `HasTy.perform`, `rowTy_closed` |
| `Sketch.check_fill` | a filling of the focus's type keeps the sketch's type, and the filling alone is checked | `check_replace` |
| `Sketch.check_omit` | an omission keeps the sketch's type, when the hole row declares the focus's type exactly | `check_replace`, `Sketch.hole_hasTy` |
| `Sketch.check_focusAt` | in a sketch that the checker admits, the focus function answers at every address of a program | `check_focusAt` |
| `Sketch.check_fill_focusAt` | a filling of the answered type in the answered environment keeps the sketch's type | `check_replace_focusAt` |
| `Sketch.check_omit_focusAt` | an omission keeps the sketch's type, when the hole row declares the answered type | `Sketch.check_fill_focusAt`, `Sketch.hole_hasTy` |

Each statement is made once, at the typing signature of an application (`SigApp.signature`).
The form at a row table alone is the instance at `⟨table, []⟩`: `SigApp.signature_nil` holds by
definition (`Test/Program/SketchControls.lean` has the instance).

`Sketch.check_fill` and `Sketch.check_omit` are the replacement law of the typing judgment
(`Laws/Program/Typing/Replace.lean`) at the two edits of a sketch, `Sketch.fillAt` and
`Sketch.omitAt`. Their controls are in `Test/Program/ReplaceControls.lean`. In those two the
focus's environment and type are existential. The last three state the same two edits at the
focus that `Sketch.focusAt` computes (`Program/Typing/Focus.lean`,
`Laws/Program/Typing/Focus.lean`), so a tool has every premise in hand. Their controls are in
`Test/Program/FocusControls.lean`.

## Placement

Concept `initial-algebras-folds`: the checker is one fold of the program, and each law reads
that fold at two signatures. Requirement R14, under decisions rows 282 and 288.

- **`sketch-conservative`** (claim, role compatibility; pointer `holes_conservative`).
  Reach: every application, every hole table, every environment and path, for a program that
  performs only the application's operations and reads only service keys with a carrier
  (`SigProgram`). It does not establish anything of a program that performs a hole, any
  behaviour, or that a hole table is lawful. Consumer: a sketch whose holes are all filled is an
  ordinary program, and the checker decides it.
- **`sketch-weakening`** (claim, role weakening; pointer `sketch_weakening`, which is H2
  and H3 as one statement). Reach: the same, with H3's premise at the extended signature. It
  does not establish an omission or a filling: those are the replacement law's. Consumer:
  declaring a hole, and composing two sketches.
- **`hole-rule`** (claim, role compatibility; pointer `Sketch.hole_hasTy`). Reach: a
  hole row with a unit request, closed columns and formed columns, at any position of any hole
  table, in every environment. It does not establish a rule for a request that reads the
  environment, or a run. Consumer: the replacement law, for an omission.

- **`typed-replacement`** (claim, role substitution; its pointer is
  `NodeHasTy.replace`, in `Laws/Program/Typing/Replace.lean`). `Sketch.check_fill` and
  `Sketch.check_omit` are its two consumers on a sketch. Reach: a sketch that the checker admits,
  and an address of a program in it. A filling has the focus's type exactly, and it may declare
  more holes. An omission asks four things of the focus's type: closed columns, an answer and an
  error in normal form, formed columns, and the requirement as its own key list. They do not
  establish any behaviour, or a filling or an omission at a type that is equal only after
  normalization: the checker gives a node the raw type of its term, and it reads a hole row in
  normal form. The focus's environment and type are existential in these two.
- **`focus-function`** (claim, role inversion; its pointer is
  `NodeHasTy.replace_envAt`, in `Laws/Program/Typing/Replace.lean`). `Sketch.check_focusAt`,
  `Sketch.check_fill_focusAt` and `Sketch.check_omit_focusAt` are its consumers on a sketch.
  Reach: the same sketches and addresses, with the focus as `Sketch.focusAt` answers it. The
  omission's premises are on the answered type, so a tool can decide each. They do not establish
  a focus after a sibling that the checker refuses, any behaviour, or an omission at a type that
  is equal only after normalization.

No statement here names a gap, a term hole or a run. The host boundary stays where
`docs/core/host-boundary.md` puts it.
-/

set_option autoImplicit false

namespace Effect4.Program

open Effect4 (ServiceKey)
open Effect4.Machine.Env (Requirement)
open Conform.Effect4.Typing

/-! ## The hole table is an extension -/

/-- A hole table appended after an application's rows extends its typing signature: every
operation that the application admits is admitted at the same row, and every key keeps its
carrier. It is `SigApp.rows_append` at the hole table. Every law of a sketch rests on it. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem SigApp.withHoles_extends (app : SigApp) (holes : RowTable) :
    SigExtends app.signature (app.withHoles holes).signature :=
  app.rows_append holes

/-- Declaring more holes is appending to the hole table. A step of `sketch_weakening`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem SigApp.withHoles_withHoles (app : SigApp) (holes more : RowTable) :
    (app.withHoles holes).withHoles more = app.withHoles (holes ++ more) := by
  simp only [SigApp.withHoles, List.append_assoc]

/-- An empty hole table changes nothing. A step of `Sketch.check_program`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem SigApp.withHoles_nil (app : SigApp) : app.withHoles [] = app := by
  simp only [SigApp.withHoles, List.append_nil]

/-- The row that the extended signature gives hole `k`: the hole table's row at `k`, with its
three type columns in normal form. A step of `Sketch.hole_hasTy`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem SigApp.withHoles_rowOf (app : SigApp) (holes : RowTable) (k : Nat) (row : Row)
    (hk : holes[k]? = some row) :
    (app.withHoles holes).signature.rowOf (.external (app.rows.length + k)) =
      row.normalizeTypes := by
  show (nativeRowOf (app.rows ++ holes) (.external (app.rows.length + k))).normalizeTypes = _
  simp only [nativeRowOf, List.getElem?_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left, hk, Option.getD_some]

/-! ## A program is a sketch with no hole -/

/-- **A program is a sketch with no hole**: the check of a program as a sketch is the module
check's answer on it, refusals included. On a program with no block the module check is the
checker's (`checkModule_eq_check`). -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Sketch.check_program (app : SigApp) (e : NativeEff) :
    Sketch.check (e : Sketch) app = Checker.checkModule app.signature e := by
  show Checker.checkModule (app.withHoles []).signature e = _
  rw [SigApp.withHoles_nil]

/-! ## H1: conservative -/

/-- **H1, the claim `sketch-conservative`**: a program that performs no hole is checked the
same with any hole table, refusals included, at every environment and path. The premise is
`SigProgram` at the application's signature: every operation that the program performs is one of
the application's, and every service key that it reads has a carrier. It is C3's reflection
(`check_restrict`) at the hole table. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem holes_conservative (app : SigApp) (holes : RowTable) {e : NativeEff}
    (hp : SigProgram app.signature e) (env : TyEnv) (p : List Nat) :
    Checker.check (app.withHoles holes).signature env p e = Checker.check app.signature env p e :=
  check_restrict (app.withHoles_extends holes) hp env p

/-- H1 on a sketch: a sketch whose program performs no hole and holds no block is checked as
its program. So a sketch with every hole filled is an ordinary program, and the checker decides
it. A program with a block is the whole-program form's (`Sketch.check_filled_module`). -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Sketch.check_filled (s : Sketch) (app : SigApp)
    (hp : SigProgram app.signature s.program)
    (hnb : ∀ decls bodies main, s.program ≠ .defs decls bodies main) :
    s.check app = Checker.check app.signature [] [] s.program := by
  show Checker.checkModule _ s.program = _
  rw [checkModule_eq_check _ hnb]
  exact holes_conservative app s.holes hp [] []

/-! ## H1 on a whole program -/

/-- **A whole program performs only the signature's operations**: at a definition block, each
body and the main program at the block's signature, as the module check reads them; otherwise
the program at the signature (`SigProgram`). -/
def ModuleSigProgram {Op : Type} (s : Signature Op) : Eff Op → Prop
  | .defs decls bodies main =>
    (∀ b ∈ bodies.toList, SigProgram (s.withDefs decls) b) ∧ SigProgram (s.withDefs decls) main
  | e => SigProgram s e

/-- The bodies' check is unchanged under an extension of the signature, when each body performs
only the smaller signature's operations. A step of `module-holes-conservative`. Its consumer is
`checkModule_restrict`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem checkBodies_restrict {Op : Type} {s s' : Signature Op} (h : SigExtends s s')
    (p : List Nat) (decls : List DefDecl) (bodies : Effs Op)
    (hb : ∀ b ∈ bodies.toList, SigProgram s b) :
    Checker.checkBodies s' p decls bodies = Checker.checkBodies s p decls bodies := by
  match decls, bodies with
  | d :: ds, .cons body rest =>
    have hbody : SigProgram s body := hb body (List.mem_cons.mpr (Or.inl rfl))
    have hrest : ∀ b ∈ rest.toList, SigProgram s b := fun b hm => hb b (List.mem_cons.mpr (Or.inr hm))
    simp only [Checker.checkBodies, check_restrict h hbody,
      checkBodies_restrict h (p ++ [1]) ds rest hrest]
  | [], _ => rfl
  | _ :: _, .nil => rfl

/-- **The module check is unchanged under an extension of the signature**, for a whole program
that performs only the smaller signature's operations: C3's restriction half (`check_restrict`)
at the module check, definition blocks included. A step of `module-holes-conservative`. Its
consumer is `Sketch.check_filled_module`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem checkModule_restrict {Op : Type} {s s' : Signature Op} (h : SigExtends s s') {e : Eff Op}
    (hp : ModuleSigProgram s e) : Checker.checkModule s' e = Checker.checkModule s e := by
  cases e
  case defs decls bodies main =>
    obtain ⟨hb, hm⟩ := hp
    simp only [Checker.checkModule]
    rw [checkBodies_restrict (h.withDefs decls) [0] decls bodies hb,
      check_restrict (h.withDefs decls) hm [] [1]]
  all_goals exact check_restrict h hp [] []

/-- **H1 on a whole program**: a sketch whose program performs no hole is checked as its program by
the module check, definition block included. So a sketch with every hole filled is an ordinary
module. The pointer of `module-holes-conservative`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Sketch.check_filled_module (s : Sketch) (app : SigApp)
    (hp : ModuleSigProgram app.signature s.program) :
    s.check app = Checker.checkModule app.signature s.program :=
  checkModule_restrict (app.withHoles_extends s.holes) hp

/-! ## H2 and H3: weakening -/

/-- **H2**: a sketch that the checker admits stays admitted, at the same type, when more holes
are declared after its own. It is C3's monotone half (`check_ext`) at the longer hole table. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem sketch_more_holes (app : SigApp) (holes more : RowTable) {e : NativeEff} {env : TyEnv}
    {p : List Nat} {t : EffTy}
    (h : Checker.check (app.withHoles holes).signature env p e = .ok t) :
    Checker.check (app.withHoles (holes ++ more)).signature env p e = .ok t := by
  rw [← SigApp.withHoles_withHoles]
  exact check_ext ((app.withHoles holes).withHoles_extends more) h

/-- **H3**: the checker reads the rows of the holes that the sketch performs, and no later row.
A program that performs only the application's operations and the holes of `holes` is checked
the same when more holes are declared, refusals included. So a filled hole's row can stay in
the table: the checker no longer reads it. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem sketch_reads_its_holes (app : SigApp) (holes more : RowTable) {e : NativeEff}
    (hp : SigProgram (app.withHoles holes).signature e) (env : TyEnv) (p : List Nat) :
    Checker.check (app.withHoles (holes ++ more)).signature env p e =
      Checker.check (app.withHoles holes).signature env p e := by
  rw [← SigApp.withHoles_withHoles]
  exact check_restrict ((app.withHoles holes).withHoles_extends more) hp env p

/-- **The claim `sketch-weakening`, as one statement**: H2 and H3 for one application and two
hole tables. It is the pointer that the claim's row needs, and it adds nothing to its two
parts. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem sketch_weakening (app : SigApp) (holes more : RowTable) :
    (∀ {e : NativeEff} {env : TyEnv} {p : List Nat} {t : EffTy},
      Checker.check (app.withHoles holes).signature env p e = .ok t →
        Checker.check (app.withHoles (holes ++ more)).signature env p e = .ok t) ∧
    (∀ {e : NativeEff}, SigProgram (app.withHoles holes).signature e →
      ∀ (env : TyEnv) (p : List Nat),
        Checker.check (app.withHoles (holes ++ more)).signature env p e =
          Checker.check (app.withHoles holes).signature env p e) :=
  ⟨sketch_more_holes app holes more, sketch_reads_its_holes app holes more⟩

/-- H2 on a sketch: declaring more holes keeps the sketch admitted modulo its holes, at the
same type. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Sketch.check_more_holes (s : Sketch) (app : SigApp) (more : RowTable) {t : EffTy}
    (h : s.check app = .ok t) :
    Sketch.check { s with holes := s.holes ++ more } app = .ok t := by
  show Checker.checkModule (app.withHoles (s.holes ++ more)).signature s.program = .ok t
  rw [← SigApp.withHoles_withHoles]
  exact checkModule_ext ((app.withHoles s.holes).withHoles_extends more) h

/-! ## The hole's rule -/

/-- **The hole's rule, the claim `hole-rule`**: hole `k` has the type that its row declares, in
every environment. The row is a hole row with closed columns that pass strict formation, the
check that the row check runs at each use (`checkRow`). The answer and the error are read in
normal form, as the checker gives every type.

No rule is added to the typing judgment: this is `HasTy.perform` at a closed row
(`rowTy_closed`). The row has no parameter, and its request is a unit, which the literal has in
any environment. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Sketch.hole_hasTy (app : SigApp) (holes : RowTable) (k : Nat) {name : String}
    {answer error : Ty} {requires : List ServiceKey} (env : TyEnv)
    (hk : holes[k]? = some (Row.hole name answer error requires))
    (hans : answer.closed = true) (herr : error.closed = true)
    (formed : Formation.Formed
      (Formation.instantiatedSites (Row.hole name answer error requires).normalizeTypes [])) :
    HasTy (app.withHoles holes).signature env (Sketch.hole app k)
      ⟨answer.normalize, error.normalize, Requirement.ofList requires⟩ := by
  have hlt : k < holes.length := by
    cases hlen : holes[k]? with
    | none => rw [hlen] at hk; exact nomatch hk
    | some _ => exact (List.getElem?_eq_some_iff.mp hlen).1
  refine HasTy.perform (requestTy := .unit) ?_ ?_ ?_
  · show decide (app.rows.length + k < (app.rows ++ holes).length) = true
    rw [List.length_append]
    exact decide_eq_true (Nat.add_lt_add_left hlt _)
  · rfl
  · show rowTy ((app.withHoles holes).signature.rowOf (.external (app.rows.length + k)))
        Ty.unit none = _
    rw [SigApp.withHoles_rowOf app holes k _ hk,
      rowTy_closed _ _ (by rfl) (Ty.closed_normalize _ hans) (Ty.closed_normalize _ herr) formed]
    have hunit : Ty.sub Ty.unit.normalize Ty.unit.normalize.normalize = true := by decide +kernel
    have hsub : Ty.sub Ty.unit.normalize
        (Row.hole name answer error requires).normalizeTypes.request.normalize = true := hunit
    rw [if_pos hsub]
    show some (⟨answer.normalize.normalize, error.normalize.normalize,
      Requirement.ofList requires⟩ : EffTy) = _
    rw [Ty.normalize_idem, Ty.normalize_idem]

/-! ## The signature at an address -/

/-- **An application's signature extends its block's**: a block adds rows to invocations only,
and an application's signature keeps every invocation outside its domain. A step of
`Sketch.sigAt_extends`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Signature.extends_withDefs {Op : Type} (sig : Signature Op)
    (h : ∀ op k, sig.callOf op = some k → sig.dom op = false) (decls : List DefDecl) :
    SigExtends sig (sig.withDefs decls) := by
  refine ⟨rfl, rfl, rfl, fun op hd => ?_, fun _ _ hs => hs, rfl, rfl⟩
  cases hc : sig.callOf op with
  | none =>
    exact ⟨by rw [sig.withDefs_dom_of_none decls hc]; exact hd,
      sig.withDefs_rowOf_of_none decls hc⟩
  | some k =>
    rw [h op k hc] at hd
    cases hd

/-- **The signature at an address extends the sketch's**: it is the sketch's, or its block's. A
hole keeps its declared type there, so an omission inside a block keeps the sketch's type. A
step of `Sketch.check_omit_focusAt`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Sketch.sigAt_extends (s : Sketch) (app : SigApp) (path : List Nat) :
    SigExtends (app.withHoles s.holes).signature (s.sigAt app path) := by
  unfold Sketch.sigAt
  cases hpart : s.program.partAt (app.withHoles s.holes).signature [] path with
  | none => exact SigExtends.refl _
  | some pr =>
    obtain ⟨part, rest⟩ := pr
    show SigExtends _ part.sig
    unfold Eff.partAt at hpart
    split at hpart
    · split at hpart
      · rw [Part.bodyAt_sig hpart]
        exact Signature.extends_withDefs _ (SigApp.signature_callsOutside _) _
      · cases hpart
        exact Signature.extends_withDefs _ (SigApp.signature_callsOutside _) _
      · cases hpart
    · cases hpart
      exact SigExtends.refl _

/-- **At the root the signature is the sketch's.** A step of `Sketch.check_fill_focusAt`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Sketch.sigAt_nil (s : Sketch) (app : SigApp) :
    s.sigAt app [] = (app.withHoles s.holes).signature := by
  unfold Sketch.sigAt Eff.partAt
  split <;> rfl

/-- **Inside a part the signature is the part's.** A step of `Sketch.check_fill_focusAt`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Sketch.sigAt_part {s : Sketch} {app : SigApp} {path : List Nat} {part : Part NativeOp}
    {rest : List Nat}
    (h : s.program.partAt (app.withHoles s.holes).signature [] path = some (part, rest)) :
    s.sigAt app path = part.sig := by
  unfold Sketch.sigAt
  rw [h]
  rfl

/-- The focus at the root is the whole program at the sketch's type. A step of
`Sketch.check_fill_focusAt`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Sketch.focusAt_nil {s : Sketch} {app : SigApp} {T : EffTy} (hs : s.check app = .ok T) :
    s.focusAt app [] = some ⟨s.program, [], T⟩ := by
  show (s.check app).toOption.map _ = _
  rw [hs]
  rfl

/-! ## Filling and omitting at the focus: the replacement law at a sketch -/

/-- The fill at an address where the program's replacement exists: the sketch with the
replaced program. A step of `typed-replacement`: `Sketch.check_fill_focusAt` reads it. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Sketch.fillAt_of_replaceAt {s : Sketch} {path : List Nat} {q program : NativeEff}
    (h : (Node.eff s.program).replaceAt path (.eff q) = some (.eff program)) :
    s.fillAt path q = some { s with program := program } := by
  simp only [Sketch.fillAt, h, Option.bind_some, Node.eff?, Option.map_some]

/-- **The focus function answers at every address of a program** of a sketch that the checker
admits: the sub-program there, with an environment and a type. At the root it is the whole
program; inside a definition block it is the focus in the part that holds the address
(`checkModule_programFocusAt`). A consumer of `focus-function`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Sketch.check_focusAt (s : Sketch) (app : SigApp) {T : EffTy} {path : List Nat}
    {q : NativeEff} (hs : s.check app = .ok T)
    (hat : (Node.eff s.program).at_ path = some (.eff q)) :
    ∃ (env : TyEnv) (t : EffTy), s.focusAt app path = some ⟨q, env, t⟩ := by
  cases path with
  | nil =>
    cases hat
    exact ⟨[], T, Sketch.focusAt_nil hs⟩
  | cons i r =>
    have hsm : Checker.checkModule (app.withHoles s.holes).signature s.program = .ok T := hs
    exact checkModule_programFocusAt hsm hat

/-- **Filling at the answered focus keeps the type.** In a sketch that the checker admits, take
the focus that `Sketch.focusAt` answers at an address. Every program that the checker admits at
the focus's type, in the focus's environment and at the address's signature (`Sketch.sigAt`),
fills the address, and the checker admits the filled sketch at the same type. Inside a
definition block the address's signature is the block's, so the filling may invoke the block's
definitions. The filling may declare more holes: `more` is appended to the hole table. Nothing is
existential: a tool computes the focus and checks its filling against it. A consumer of
`focus-function`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Sketch.check_fill_focusAt (s : Sketch) (app : SigApp) {T : EffTy} {path : List Nat}
    {f : Focus NativeOp} (hs : s.check app = .ok T) (hf : s.focusAt app path = some f)
    (more : RowTable) {q' : NativeEff} {pq : List Nat}
    (hq' : Checker.check (Sketch.sigAt { s with holes := s.holes ++ more } app path) f.env pq q' =
      .ok f.ty) :
    ∃ s', Sketch.fillAt { s with holes := s.holes ++ more } path q' = some s' ∧
      s'.check app = .ok T := by
  have hext : SigExtends (app.withHoles s.holes).signature
      (app.withHoles (s.holes ++ more)).signature := by
    rw [← SigApp.withHoles_withHoles]
    exact (app.withHoles s.holes).withHoles_extends more
  cases path with
  | nil =>
    rw [Sketch.focusAt_nil hs] at hf
    cases hf
    rw [Sketch.sigAt_nil] at hq'
    have hd := check_sound _ q' [] pq T hq'
    have hnb : ∀ decls bodies main, q' ≠ .defs decls bodies main := fun _ _ _ heq => by
      subst heq
      cases hd
    have hrep : (Node.eff s.program).replaceAt [] (.eff q') = some (.eff q') := by
      rw [Node.replaceAt]
      exact if_pos (rfl : (Node.eff q').ctorIdx = (Node.eff s.program).ctorIdx)
    refine ⟨_, Sketch.fillAt_of_replaceAt (s := { s with holes := s.holes ++ more }) hrep, ?_⟩
    show Checker.checkModule _ q' = _
    rw [checkModule_eq_check _ hnb]
    exact check_complete _ q' [] T hd []
  | cons i r =>
    have hsm : Checker.checkModule (app.withHoles s.holes).signature s.program = .ok T := hs
    have hfp : programFocusAt (app.withHoles s.holes).signature [] s.program (i :: r) = some f :=
      hf
    have hfb := hfp
    unfold programFocusAt at hfb
    obtain ⟨⟨part, rest⟩, hpart, -⟩ := Option.bind_eq_some_iff.mp hfb
    obtain ⟨part', hpart'⟩ :=
      Eff.partAt_resig (s' := (app.withHoles (s.holes ++ more)).signature) hpart
    rw [Sketch.sigAt_part (s := { s with holes := s.holes ++ more }) hpart'] at hq'
    obtain ⟨p', hrep, hp'⟩ := checkModule_replace_programFocusAt hsm hfp hext hpart' hq'
    exact ⟨_, Sketch.fillAt_of_replaceAt (s := { s with holes := s.holes ++ more }) hrep, hp'⟩

/-- **Omitting at the answered focus keeps the type.** In a sketch that the checker admits, take
the focus that `Sketch.focusAt` answers at an address. When its type has closed columns, an
answer and an error in normal form, and formed columns, the omission with the hole row that
declares that type exists, and the checker admits it at the same type. Each premise is on the
answered type, so a tool can decide it. The hole has its declared type at the address's
signature too (`Sketch.sigAt_extends`). A consumer of `focus-function`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Sketch.check_omit_focusAt (s : Sketch) (app : SigApp) {T : EffTy} {path : List Nat}
    {f : Focus NativeOp} (hs : s.check app = .ok T) (hf : s.focusAt app path = some f)
    (name : String) (hans : f.ty.answer.closed = true) (herr : f.ty.error.closed = true)
    (hansN : f.ty.answer.normalize = f.ty.answer) (herrN : f.ty.error.normalize = f.ty.error)
    (formed : Formation.Formed (Formation.instantiatedSites
      (Row.hole name f.ty.answer f.ty.error f.ty.requires.elems).normalizeTypes [])) :
    ∃ s', s.omitAt app path (Row.hole name f.ty.answer f.ty.error f.ty.requires.elems) = some s' ∧
      s'.check app = .ok T := by
  have hhole := Sketch.hole_hasTy app
    (s.holes ++ [Row.hole name f.ty.answer f.ty.error f.ty.requires.elems]) s.holes.length f.env
    List.getElem?_concat_length hans herr formed
  have hreq : Requirement.ofList f.ty.requires.elems = f.ty.requires :=
    Row.normalize_of_ascending f.ty.requires.elems f.ty.requires.ascending
  rw [hansN, herrN, hreq] at hhole
  exact Sketch.check_fill_focusAt s app hs hf
    [Row.hole name f.ty.answer f.ty.error f.ty.requires.elems] (pq := [])
    (check_complete _ _ f.env f.ty (hasTy_ext (Sketch.sigAt_extends
      { s with holes := s.holes ++ [Row.hole name f.ty.answer f.ty.error f.ty.requires.elems] }
      app path) hhole) [])

/-! ## Filling and omitting at an address -/

/-- **Filling keeps the type, and the filling alone is checked.** A sketch that the checker
admits splits at an address of a program into an environment and a type of the focus, at the
address's signature (`Sketch.sigAt`). Every program that the checker admits at that type in that
environment fills the address, and the checker admits the filled sketch at the same type. The
filling may declare more holes: `more` is appended to the hole table. The root of a definition
block is no such address: the checker refuses a block as a sub-program, so the premise `hroot`
leaves it out. A consumer of `typed-replacement`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Sketch.check_fill (s : Sketch) (app : SigApp) {T : EffTy} {path : List Nat}
    {q : NativeEff} (hs : s.check app = .ok T)
    (hat : (Node.eff s.program).at_ path = some (.eff q))
    (hroot : path = [] → ∀ decls bodies main, s.program ≠ .defs decls bodies main) :
    ∃ (env : TyEnv) (t : EffTy),
      (∀ pq, Checker.check (s.sigAt app path) env pq q = .ok t) ∧
      ∀ (more : RowTable) {q' : NativeEff} {pq : List Nat},
        Checker.check (Sketch.sigAt { s with holes := s.holes ++ more } app path) env pq q' =
          .ok t →
        ∃ s', Sketch.fillAt { s with holes := s.holes ++ more } path q' = some s' ∧
          s'.check app = .ok T := by
  obtain ⟨env, t, hf⟩ := Sketch.check_focusAt s app hs hat
  refine ⟨env, t, fun pq => ?_, fun more {q' pq} hq' => Sketch.check_fill_focusAt s app hs hf more hq'⟩
  cases path with
  | nil =>
    cases hat
    rw [Sketch.focusAt_nil hs] at hf
    cases hf
    rw [Sketch.sigAt_nil]
    have hsm : Checker.checkModule (app.withHoles s.holes).signature s.program = .ok T := hs
    rw [checkModule_eq_check _ (hroot rfl)] at hsm
    exact check_complete _ _ [] T (check_sound _ _ [] [] T hsm) pq
  | cons i r =>
    have hfp : programFocusAt (app.withHoles s.holes).signature [] s.program (i :: r) =
        some ⟨q, env, t⟩ := hf
    unfold programFocusAt at hfp
    obtain ⟨⟨part, rest⟩, hpart, hfoc⟩ := Option.bind_eq_some_iff.mp hfp
    rw [Sketch.sigAt_part hpart]
    exact check_complete _ _ env t (focusAt_typed hfoc).2 pq

/-- **Omitting keeps the type, where a hole row declares the focus's type exactly.** A sketch
that the checker admits splits at an address of a program into an environment and a type `t` of
the focus. When `t` has closed columns, an answer and an error in normal form, and formed
columns, the omission with the hole row that declares `t` exists, and the checker admits it at
the same type. The premises are the hole's rule's (`Sketch.hole_hasTy`), and the two on normal
form: a hole row is read in normal form, and the checker gives a node the raw type of its term.
The root of a definition block is left out, as in `Sketch.check_fill`. A consumer of
`typed-replacement`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Sketch.check_omit (s : Sketch) (app : SigApp) {T : EffTy} {path : List Nat}
    {q : NativeEff} (hs : s.check app = .ok T)
    (hat : (Node.eff s.program).at_ path = some (.eff q))
    (hroot : path = [] → ∀ decls bodies main, s.program ≠ .defs decls bodies main) :
    ∃ (env : TyEnv) (t : EffTy),
      (∀ pq, Checker.check (s.sigAt app path) env pq q = .ok t) ∧
      ∀ (name : String), t.answer.closed = true → t.error.closed = true →
        t.answer.normalize = t.answer → t.error.normalize = t.error →
        Formation.Formed (Formation.instantiatedSites
          (Row.hole name t.answer t.error t.requires.elems).normalizeTypes []) →
        ∃ s', s.omitAt app path (Row.hole name t.answer t.error t.requires.elems) = some s' ∧
          s'.check app = .ok T := by
  obtain ⟨env, t, hq, hfill⟩ := Sketch.check_fill s app hs hat hroot
  refine ⟨env, t, hq, fun name hans herr hansN herrN formed => ?_⟩
  have hhole := Sketch.hole_hasTy app
    (s.holes ++ [Row.hole name t.answer t.error t.requires.elems]) s.holes.length env
    List.getElem?_concat_length hans herr formed
  have hreq : Requirement.ofList t.requires.elems = t.requires :=
    Row.normalize_of_ascending t.requires.elems t.requires.ascending
  rw [hansN, herrN, hreq] at hhole
  exact hfill [Row.hole name t.answer t.error t.requires.elems] (pq := [])
    (check_complete _ _ env t (hasTy_ext (Sketch.sigAt_extends
      { s with holes := s.holes ++ [Row.hole name t.answer t.error t.requires.elems] }
      app path) hhole) [])

/-! ## The address table and the refusals of a whole program (cutover slice S1b)

Placement. Concept `initial-algebras-folds`, requirement R14; the proposed claim
`module-address-table`, role completeness, with the pointer `Sketch.refusals_nil_iff`: the list
of refusals of a sketch is empty exactly when the sketch checks, block included. It is
`refusals_nil_iff` (`Laws/Program/Typing/Table.lean`) for the module check. Reach: every sketch
and every application. Not established: the order of the refusals after the head, and agreement
with the program's table off a block (the table of a program with no block is entrywise the
program's, and no law states it yet). Consumer: the query tool's refusals and table. -/

/-- The root's entry is first, and it holds the sketch's check. A step of
`Sketch.refusals_head`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Sketch.table_head (s : Sketch) (app : SigApp) :
    ∃ rest, s.table app = ⟨[], some (.env []), some (s.check app)⟩ :: rest := by
  obtain ⟨rest, h⟩ := addresses_eff_head s.program
  unfold Sketch.table
  rw [h]
  exact ⟨_, rfl⟩

/-- On a sketch that checks no entry of its table holds a refusal: each part is typed, so the
checker answers a type at every address of a program inside it. A step of
`Sketch.refusals_of_check`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Sketch.table_result_refusal_none {s : Sketch} {app : SigApp} {T : EffTy}
    (hs : s.check app = .ok T) {e : Table.Entry} (he : e ∈ s.table app) :
    e.result.bind Checker.refusal = none := by
  have hsm : Checker.checkModule (app.withHoles s.holes).signature s.program = .ok T := hs
  unfold Sketch.table at he
  simp only [List.mem_map] at he
  obtain ⟨a, -, rfl⟩ := he
  cases a with
  | nil =>
    show (some (s.check app)).bind Checker.refusal = none
    rw [hs]
    rfl
  | cons i r =>
    simp only [Sketch.tableEntry]
    split
    · rename_i part rest hpart
      obtain ⟨_, hty⟩ := moduleHasTy_partAt_typed (checkModule_sound _ _ T hsm) hpart
      dsimp only
      split
      · rename_i q tys hat henv
        obtain ⟨env, t, hf⟩ := hasTy_focusAt hty hat
        obtain ⟨-, henv', hfty⟩ := focusAt_eq_some.mp hf
        have hsame : env = tys := by
          injection henv'.symm.trans henv with h1
          injection h1
        subst hsame
        rw [check_complete _ q env t (effTy_sound _ q env t hfty) (i :: r)]
        rfl
      · rfl
    · rfl

/-- On a sketch that checks the list of refusals is empty. A step of `Sketch.refusals_head` and
`Sketch.refusals_nil_iff`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Sketch.refusals_of_check {s : Sketch} {app : SigApp} {T : EffTy}
    (hs : s.check app = .ok T) : s.refusals app = [] := by
  unfold Sketch.refusals
  have hnil : (s.table app).filterMap (fun e => e.result.bind Checker.refusal) = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro e he
    exact Sketch.table_result_refusal_none hs he
  rw [hnil]
  rfl

/-- **The head of a sketch's refusals is its check's refusal.** The root's entry is first. It
says nothing of the order after the head. A step of `Sketch.refusals_nil_iff`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Sketch.refusals_head (s : Sketch) (app : SigApp) :
    (s.refusals app).head? = Checker.refusal (s.check app) := by
  cases h : s.check app with
  | ok T =>
    rw [Sketch.refusals_of_check h]
    rfl
  | error ref =>
    unfold Sketch.refusals
    obtain ⟨rest, htable⟩ := Sketch.table_head s app
    rw [htable, h]
    simp only [List.filterMap_cons, Option.bind_some]
    have href : Checker.refusal (.error ref : Except TypeRefusal EffTy) = some ref := rfl
    rw [href, List.eraseDups_cons]
    rfl

/-- **The list of refusals of a sketch is empty exactly when the sketch checks**, block
included: the proposed claim `module-address-table`. Its consumer is the query tool's refusals. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Sketch.refusals_nil_iff (s : Sketch) (app : SigApp) :
    s.refusals app = [] ↔ (s.check app).toOption.isSome = true := by
  constructor
  · intro h
    have hhead : (s.refusals app).head? = none := by rw [h]; rfl
    rw [Sketch.refusals_head] at hhead
    cases hc : s.check app with
    | ok _ => rfl
    | error _ =>
      rw [hc] at hhead
      cases hhead
  · intro h
    cases hc : s.check app with
    | ok _ => exact Sketch.refusals_of_check hc
    | error _ =>
      rw [hc] at h
      cases h

end Effect4.Program
