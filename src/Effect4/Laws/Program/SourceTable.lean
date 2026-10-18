import Effect4.Program.Typing.SourceDocument
import Effect4.Laws.Program.CheckAgreement
import Effect4.Program.Typing.SourceSession
import Effect4.Laws.Program.ExpansionAddresses
import Effect4.Laws.Program.Edit
import Effect4.Laws.Auto.Semantics

/-!
# Laws.Program.SourceTable — the table at the source's addresses is the expansion's

`Program/Typing/Source.lean` checks a sketch through its layer references, as program admission
checks a program, and shows the expansion's table at the source's addresses.
`Program/Typing/SourceSession.lean` keeps that table under edits. This module holds their laws.

| Statement | In words | From |
| --- | --- | --- |
| `Sketch.sourceAnnotate_eq_sourceTable` | one traversal of the expansion, at the source's addresses, is the table: at each source address the expansion's entry, at the root the check through the references | `Eff.addresses_expandRefs`, `Sketch.annotate_eq_table` |
| `Sketch.sourceTable_find`, `Sketch.sourceTable_typedAt` | below the root, the entry at a source address is the expansion's entry there | the address map |
| `Sketch.sourceTable_focus` | where the table holds a type below the root, it is the expansion's focus there | `Table.typedAt_table` |
| `Sketch.sourceCheck_toOption` | the check at the root is admission's typing | `typeOfProgram`'s definition |
| `Sketch.sourceRefusals_head`, `Sketch.sourceRefusals_nil_iff` | the refusals start with the check's, and are empty exactly when it succeeds | `Sketch.table_result_refusal_none` at the expansion |
| `SourceSession.reached_view` | every sealed document shows its source table, refusals, and root type | the placed `Doc.coherent` goal |
| `SourceSession.replay_drafts_view` | every old application, sketch, and edit list retains its exact observation through canonical draft replay | placed transport goal |
| `SourceSession.feed_undo` | an edit, then the edit that puts back the old sub-program as written, restores the session | `EditSession.Coherent.ext` |

## Placement

Concept `initial-algebras-folds`; property: the address table is a fold (`annotate-table`), and
the expansion keeps every address of the program in its order (`Eff.addresses_expandRefs`), so
the expansion's table at the source's addresses is a table of the source. Requirement R14
(program as data, through layer references), under decisions row 373 (7) and (10).

- **`source-annotation-agrees`** (proposed claim, role compatibility; pointer
  `Sketch.sourceAnnotate_eq_sourceTable`). Reach: every sketch and application, refused ones
  included; references well formed or not, an ill-formed one refused at the root at its site.
  The check at the root is admission's typing (`Sketch.sourceCheck_toOption`). Not established:
  an address of a copy maps to no source address; a refusal located inside a copy keeps the
  expansion's address; a run; the cost. Consumers: `SourceSession.table_eq`, and the session
  tool (`tools/Tools/Session.lean`).
- **`source-session-coherent`** (role preservation; pointer `SourceSession.reached_view`).
  Reach: every sealed document, without a separate coherence premise; exact source table, refusals, and root type.
  The proof uses the placed `Doc.coherent` goal.
  `SourceSession.replay_drafts_view` retains every old application, initial sketch, and edit list through canonical replay.
  Its exact observation remains a placed goal.
  Neither claim establishes reference splicing, execution, progress, or cost.
  Consumer: the session tool.
- Every other statement is a step of these two, and names its consumer.
-/

set_option autoImplicit false

namespace Effect4.Program

/-! ## The address list -/

/-- **An address list has the root first and no other root.** A step of
`source-annotation-agrees`. Its consumer is `Sketch.sourceAnnotate_eq_sourceTable`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Node.addresses_root {Op : Type} (n : Node Op) :
    ∃ rest, Node.addresses n = [] :: rest ∧ ∀ a ∈ rest, a ≠ [] := by
  refine ⟨_, Node.addresses_eq_cons n, ?_⟩
  intro a ha
  simp only [List.mem_append] at ha
  rcases ha with h | h | h <;> obtain ⟨b, rfl⟩ := Node.mem_childAddresses h <;>
    exact List.cons_ne_nil _ _

/-- **The first entry at an address of a list of entries each at its own address.** A step of
`source-annotation-agrees`. Its consumer is `Sketch.sourceTable_find`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Table.find?_map_at {f : List Nat → Table.Entry} (hf : ∀ x, (f x).path = x)
    {xs : List (List Nat)} {a : List Nat} (ha : a ∈ xs) :
    (xs.map f).find? (fun e => decide (e.path = a)) = some (f a) := by
  rw [List.find?_map]
  have hcomp : ((fun e => decide (e.path = a)) ∘ f) = fun x => decide (x = a) := by
    funext x
    simp only [Function.comp_apply, hf]
  rw [hcomp]
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp
    ((List.find?_isSome (p := fun x => decide (x = a))).mpr ⟨a, ha, decide_eq_true rfl⟩)
  have hya := List.find?_some hy
  rw [decide_eq_true_eq] at hya
  subst hya
  rw [hy]
  rfl

/-! ## The table at the source's addresses -/

/-- An entry at a source address stands at that address. A step of `source-annotation-agrees`.
Its consumer is `Sketch.sourceTable_find`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Sketch.sourceEntry_path (s : Sketch) (app : SigApp) (x : List Nat) :
    (s.sourceEntry app x).path = x := by
  cases x with
  | nil => rfl
  | cons i r => exact Sketch.tableEntry_path s.expand app (i :: r)

/-- **The expansion's table, its copies dropped**, is the expansion's entry at each address of
the source, in the source's order: the address map (`Eff.addresses_expandRefs`) under the
table's entries. A step of `source-annotation-agrees`. Its consumer is
`Sketch.sourceAnnotate_eq_sourceTable`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Sketch.expand_table_filter (s : Sketch) (app : SigApp) :
    (s.expand.table app).filter (fun e => !Table.belowSite s.sites e.path) =
      (Node.addresses (.eff s.program)).map (s.expand.tableEntry app) := by
  unfold Sketch.table
  rw [List.filter_map]
  have hcomp : ((fun e : Table.Entry => !Table.belowSite s.sites e.path) ∘
      s.expand.tableEntry app) = fun a => !Table.belowSite s.sites a := by
    funext a
    simp only [Function.comp_apply, Sketch.tableEntry_path]
  rw [hcomp]
  exact congrArg (List.map _) (Eff.addresses_expandRefs s.program)

/-- **The table at the source's addresses, in one traversal of the expansion, is its
specification**: one entry for each address of the sketch as written, in its order. At the
root it holds the check through the references, and at every other address the expansion's
entry there. The pointer of the proposed claim `source-annotation-agrees`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Sketch.sourceAnnotate_eq_sourceTable (s : Sketch) (app : SigApp) :
    s.sourceAnnotate app = s.sourceTable app := by
  unfold Sketch.sourceAnnotate Table.atSource Sketch.sourceTable
  rw [Sketch.annotate_eq_table, Sketch.expand_table_filter]
  obtain ⟨rest, hrest, hne⟩ := Node.addresses_root (.eff s.program)
  rw [hrest, List.map_cons, List.map_cons]
  have htail : rest.map (s.expand.tableEntry app) = rest.map (s.sourceEntry app) := by
    refine List.map_congr_left fun a ha => ?_
    obtain ⟨i, r, rfl⟩ := List.exists_cons_of_ne_nil (hne a ha)
    rfl
  cases hf : s.program.firstRefFault with
  | some f =>
    obtain ⟨site, target, why⟩ := f
    simp only [Sketch.sourceEntry, Sketch.sourceCheck, hf, htail]
  | none =>
    simp only [Sketch.sourceEntry, Sketch.sourceCheck, hf, htail, Sketch.tableEntry]

/-- **Below the root, the entry at a source address is the expansion's entry there.** A step of
`source-annotation-agrees`. Its consumer is `Sketch.sourceTable_typedAt`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Sketch.sourceTable_find (s : Sketch) (app : SigApp) {a : List Nat}
    (ha : a ∈ Node.addresses (.eff s.program)) (hne : a ≠ []) :
    (s.sourceTable app).find? (fun e => decide (e.path = a)) =
      (s.expand.table app).find? (fun e => decide (e.path = a)) := by
  unfold Sketch.sourceTable Sketch.table
  rw [Table.find?_map_at (Sketch.sourceEntry_path s app) ha,
    Table.find?_map_at (xs := Node.addresses (.eff s.expand.program))
      (Sketch.tableEntry_path s.expand app) (Eff.mem_addresses_expandRefs s.program ha)]
  obtain ⟨i, r, rfl⟩ := List.exists_cons_of_ne_nil hne
  rfl

/-- **Below the root, the type at a source address is the expansion's type there.** A step of
`source-annotation-agrees`. Its consumer is `Sketch.sourceTable_focus`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Sketch.sourceTable_typedAt (s : Sketch) (app : SigApp) {a : List Nat}
    (ha : a ∈ Node.addresses (.eff s.program)) (hne : a ≠ []) :
    Table.typedAt (s.sourceTable app) a = Table.typedAt (s.expand.table app) a := by
  unfold Table.typedAt
  rw [Sketch.sourceTable_find s app ha hne]

/-- An entry of the table at the source's addresses stands at a source address. A step of
`source-annotation-agrees`. Its consumer is `Sketch.sourceTable_focus`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Sketch.mem_sourceTable {s : Sketch} {app : SigApp} {e : Table.Entry}
    (he : e ∈ s.sourceTable app) : e.path ∈ Node.addresses (.eff s.program) := by
  unfold Sketch.sourceTable at he
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
  rw [Sketch.sourceEntry_path]
  exact hx

/-- **Where the table at the source's addresses holds a type below the root, it is the
expansion's focus there**: the environment and the type that the expansion gives its sub-program
at that address. A step of `source-annotation-agrees`. Its consumer is
`SourceSession.focusAt_typed`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Sketch.sourceTable_focus {s : Sketch} {app : SigApp} {a : List Nat} {tys : TyEnv}
    {ty : EffTy} (h : Table.typedAt (s.sourceTable app) a = some (tys, ty)) (hne : a ≠ []) :
    ∃ q, s.expand.focusAt app a = some ⟨q, tys, ty⟩ := by
  have ha : a ∈ Node.addresses (.eff s.program) := by
    unfold Table.typedAt at h
    split at h
    next path _ _ hfind =>
      have hpath := List.find?_some hfind
      rw [decide_eq_true_eq] at hpath
      subst hpath
      exact Sketch.mem_sourceTable (List.mem_of_find?_eq_some hfind)
    next => cases h
  rw [Sketch.sourceTable_typedAt s app ha hne] at h
  exact Table.typedAt_table h hne

/-! ## The check at the root -/

/-- **The check through the references is admission's typing**: its success is `typeOfProgram`
at the application's signature extended by the hole table. A step of
`source-annotation-agrees`. Its consumer is the session tool's type at the root. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Sketch.sourceCheck_toOption (s : Sketch) (app : SigApp) :
    (s.sourceCheck app).toOption = typeOfProgram (app.withHoles s.holes).signature s.program := by
  unfold Sketch.sourceCheck typeOfProgram
  cases hf : s.program.firstRefFault with
  | some f =>
    have hwf : s.program.layerRefsWF = false := by
      cases hw : s.program.layerRefsWF with
      | false => rfl
      | true =>
        rw [(Eff.firstRefFault_eq_none s.program).mpr hw] at hf
        cases hf
    rw [hwf]
    rfl
  | none =>
    rw [if_pos ((Eff.firstRefFault_eq_none s.program).mp hf)]
    rfl

/-- A check through the references that succeeds has no ill-formed reference, and the
expansion's check succeeds at the same type. A step of `source-annotation-agrees`. Its consumer
is `Sketch.sourceTable_result_refusal_none`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Sketch.sourceCheck_ok {s : Sketch} {app : SigApp} {T : EffTy}
    (hs : s.sourceCheck app = .ok T) :
    s.program.firstRefFault = none ∧ s.expand.check app = .ok T := by
  unfold Sketch.sourceCheck at hs
  cases hf : s.program.firstRefFault with
  | some f =>
    obtain ⟨site, target, why⟩ := f
    rw [hf] at hs
    cases hs
  | none =>
    rw [hf] at hs
    exact ⟨rfl, hs⟩

/-- The table at the source's addresses starts with the root's entry, which holds the check
through the references. A step of `source-annotation-agrees`. Its consumers are
`Sketch.sourceRefusals_head` and `SourceSession.view_type`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Sketch.sourceTable_head (s : Sketch) (app : SigApp) :
    ∃ rest, s.sourceTable app = ⟨[], some (.env []), some (s.sourceCheck app)⟩ :: rest := by
  obtain ⟨rest, h⟩ := addresses_eff_head s.program
  unfold Sketch.sourceTable
  rw [h]
  exact ⟨_, rfl⟩

/-! ## The refusals -/

/-- Where the check through the references succeeds, no entry of the table holds a refusal: the
expansion's table holds none (`Sketch.table_result_refusal_none`). A step of
`source-annotation-agrees`. Its consumer is `Sketch.sourceRefusals_of_ok`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Sketch.sourceTable_result_refusal_none {s : Sketch} {app : SigApp} {T : EffTy}
    (hs : s.sourceCheck app = .ok T) {e : Table.Entry} (he : e ∈ s.sourceTable app) :
    e.result.bind Checker.refusal = none := by
  obtain ⟨-, hx⟩ := Sketch.sourceCheck_ok hs
  unfold Sketch.sourceTable at he
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
  cases a with
  | nil =>
    show (some (s.sourceCheck app)).bind Checker.refusal = none
    rw [hs]
    rfl
  | cons i r =>
    exact Sketch.table_result_refusal_none hx
      (List.mem_map.mpr ⟨i :: r, Eff.mem_addresses_expandRefs s.program ha, rfl⟩)

/-- Where the check through the references succeeds, the list of refusals is empty. A step of
`source-annotation-agrees`. Its consumers are `Sketch.sourceRefusals_head` and
`Sketch.sourceRefusals_nil_iff`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Sketch.sourceRefusals_of_ok {s : Sketch} {app : SigApp} {T : EffTy}
    (hs : s.sourceCheck app = .ok T) : s.sourceRefusals app = [] := by
  unfold Sketch.sourceRefusals
  have hnil : (s.sourceTable app).filterMap (fun e => e.result.bind Checker.refusal) = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro e he
    exact Sketch.sourceTable_result_refusal_none hs he
  rw [hnil]
  rfl

/-- **The head of the refusals is the check's refusal through the references.** A step of
`source-annotation-agrees`. Its consumer is `Sketch.sourceRefusals_nil_iff`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Sketch.sourceRefusals_head (s : Sketch) (app : SigApp) :
    (s.sourceRefusals app).head? = Checker.refusal (s.sourceCheck app) := by
  cases h : s.sourceCheck app with
  | ok T =>
    rw [Sketch.sourceRefusals_of_ok h]
    rfl
  | error ref =>
    unfold Sketch.sourceRefusals
    obtain ⟨rest, htable⟩ := Sketch.sourceTable_head s app
    rw [htable, h]
    simp only [List.filterMap_cons, Option.bind_some]
    have href : Checker.refusal (.error ref : Except TypeRefusal EffTy) = some ref := rfl
    rw [href, List.eraseDups_cons]
    rfl

/-- **The refusals are empty exactly when the check through the references succeeds.** A step
of `source-annotation-agrees`. Its consumer is the session tool's refusals. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Sketch.sourceRefusals_nil_iff (s : Sketch) (app : SigApp) :
    s.sourceRefusals app = [] ↔ (s.sourceCheck app).toOption.isSome = true := by
  constructor
  · intro h
    have hhead : (s.sourceRefusals app).head? = none := by rw [h]; rfl
    rw [Sketch.sourceRefusals_head] at hhead
    cases hc : s.sourceCheck app with
    | ok _ => rfl
    | error _ =>
      rw [hc] at hhead
      cases hhead
  · intro h
    cases hc : s.sourceCheck app with
    | ok _ => exact Sketch.sourceRefusals_of_ok hc
    | error _ =>
      rw [hc] at h
      cases h

/-! ## An edit session's edit -/

/-- **An edit session's omission holds the omitted sketch.** A step of `source-session-coherent`.
Its consumer is `EditSession.feed_edit`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem EditSession.feed_omit_sketch {l : EditSession} {a : List Nat} {row : Row} {s' : Sketch}
    (h : l.sketch.omitAt l.app a row = some s') : (l.feed (.omitAt a row)).1.sketch = s' := by
  simp only [EditSession.feed, h]
  split
  next =>
    split
    next => rfl
    next => rfl
  next => rfl

/-- **An edit session's edit holds the edited sketch** (`Sketch.edit`). A step of
`source-session-coherent`. Its consumer is `SourceSession.feed_coherent`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem EditSession.feed_edit {l : EditSession} {e : Edit} {s' : Sketch}
    (h : l.sketch.edit l.app e = some s') : (l.feed e).1.sketch = s' := by
  cases e with
  | fill a q => exact (EditSession.feed_keeps l (.fill a q)).2 a q s' rfl h
  | omitAt a row => exact EditSession.feed_omit_sketch h


/-!
Placement: initial-algebras-folds; source-session-coherent and typed-replacement, R14.
Question: source-session-coherent names reached_view; feed_coherent serves that claim.
Reach: coherent source tables and the exact feed policy; the root and local observations remain distinct.
Exclusions: admission, progress, arbitrary reference splicing, and native execution.
Consumers: Doc.step, FillSet.add, and the tool's edit and observation wrappers.
-/
namespace SourceSession
open _root_.Effect4.Program.Check

@[semantics "initial-algebras-folds" (requirement := R14)]
theorem open_coherent (o : Oracle) (app : SigApp) (s : Sketch) :
    (SourceSession.«open» o app s).value.Coherent := by
  change (Checked.ask o (.module app s.holes s.program)).value.table = s.sourceTable app
  rw [Checked.ask_value]
  exact Sketch.sourceAnnotate_eq_sourceTable s app

@[semantics "initial-algebras-folds" (requirement := R14)]
proof_goal feed_coherent {o : Oracle} {policy : FeedPolicy} {s next : SourceSession}
    {e : Edit} {step : Edit.Step} (hc : s.Coherent)
    (h : (s.feed o policy e).value = .ok (next,step)) : next.Coherent

@[semantics "initial-algebras-folds" (requirement := R14)]
proof_goal feed_keeps {o : Oracle} {policy : FeedPolicy} {s next : SourceSession}
    {e : Edit} {step : Edit.Step}
    (h : (s.feed o policy e).value = .ok (next,step)) :
    next.app = s.app ∧ step.edit = e ∧
      (s.sketch.edit s.app e = none → next = s) ∧
      (∀ candidate, s.sketch.edit s.app e = some candidate → next.sketch = candidate)

@[semantics "initial-algebras-folds" (requirement := R14)]
theorem table_eq {s : SourceSession} (hc : s.Coherent) : s.table = s.sketch.sourceTable s.app := hc

/-- **A coherent session shows its sketch's refusals through the references.** A step of
`source-session-coherent`. Its consumer is `reached_view`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem view_refusals {l : SourceSession} (h : l.Coherent) :
    l.view.refusals = l.sketch.sourceRefusals l.app := by
  unfold view shown EditSession.view
  rw [table_eq h]
  rfl

/-- **A coherent session shows its sketch's type through the references.** A step of
`source-session-coherent`. Its consumer is `reached_view`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem view_type {l : SourceSession} (h : l.Coherent) :
    l.view.type = (l.sketch.sourceCheck l.app).toOption := by
  unfold view shown EditSession.view
  rw [table_eq h]
  obtain ⟨rest, ht⟩ := Sketch.sourceTable_head l.sketch l.app
  rw [ht]
  cases l.sketch.sourceCheck l.app <;> rfl

/-- **The focus at a source address is the sub-program as written, at the expansion's focus.**
On a coherent session, below the root, the environment and the type that `focusAt` answers are
the expansion's focus there. A step of `source-session-coherent`. Its consumer is the session
tool's view at an address and its omission. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem focusAt_typed {l : SourceSession} (h : l.Coherent) {a : List Nat} {f : Focus NativeOp}
    (hf : l.focusAt a = some f) (hne : a ≠ []) :
    (Node.eff l.sketch.program).at_ a = some (.eff f.program) ∧
      ∃ q, l.sketch.expand.focusAt l.app a = some ⟨q, f.env, f.ty⟩ := by
  unfold focusAt at hf
  split at hf
  next q tys ty hat htyped =>
    cases hf
    rw [table_eq h] at htyped
    exact ⟨hat, Sketch.sourceTable_focus htyped hne⟩
  next => cases hf


@[semantics "initial-algebras-folds" (requirement := R14)]
theorem view_eq {s : SourceSession} (hc : s.Coherent) :
    s.view.table = s.sketch.sourceTable s.app ∧
    s.view.refusals = s.sketch.sourceRefusals s.app ∧
    s.view.type = (s.sketch.sourceCheck s.app).toOption :=
  ⟨table_eq hc,view_refusals hc,view_type hc⟩

@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Coherent.ext {a b : SourceSession} (ha : a.Coherent) (hb : b.Coherent)
    (happ : a.app = b.app) (hsketch : a.sketch = b.sketch) : a = b := by
  have htable : a.table = b.table := by rw [ha,hb,happ,hsketch]
  cases a
  cases b
  cases happ
  cases hsketch
  cases htable
  rfl

/-- Exact old feedStep observations through the existing expansion edit engine.
The expression uses EditSession.feed as its reference; it defines no second edit interpreter.
Reach: coherent source sessions, every edit, and certified oracles.
Consumer: replay_drafts_view and transport of source-session-coherent. R14. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
proof_goal feed_draft (o : Oracle) (s : SourceSession) (hc : s.Coherent) (e : Edit) :
    ∃ next step, (s.feed o .draft e).value = .ok (next,step) ∧
      step.edit = e ∧
      step.replaced = (match (Node.eff s.sketch.program).at_ e.path with
        | some (.eff old) => some old | _ => none) ∧
      (match s.sketch.edit s.app e with
       | none => next = s ∧ step.delta = .unchanged
       | some candidate =>
         next.app = s.app ∧ next.sketch = candidate ∧
         let expanded := EditSession.open s.app s.sketch.expand
         let reference := match Edit.expanded candidate.expand e with
           | some edit =>
             if s.expandedEditAgrees candidate e then expanded.feed edit
             else (EditSession.open s.app candidate.expand,Edit.Delta.rechecked)
           | none => (EditSession.open s.app candidate.expand,Edit.Delta.rechecked)
         next.table = Table.atSource candidate.sites candidate.program.firstRefFault reference.1.table ∧
           step.delta = reference.2.atSource candidate.sites)

@[semantics "initial-algebras-folds" (requirement := R14)]
proof_goal feed_keepExact {o : Oracle} {s next : SourceSession} {e : Edit} {step : Edit.Step}
    (hc : s.Coherent) (hne : e.path ≠ [])
    (h : (s.feed o .keepExact e).value = .ok (next,step)) :
    next.view.type = s.view.type ∧
      Table.typedAt next.table e.path = Table.typedAt s.table e.path ∧
      (s.expandedEditAgrees next.sketch e = true → step.delta = .spliced [e.path]) ∧
      (s.expandedEditAgrees next.sketch e = false → step.delta = .rechecked)

/-- The root feed is exactly the module recheck route, including its actual part trace. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
proof_goal feed_root (o : Oracle) (policy : FeedPolicy) (s : SourceSession)
    (e : Edit) (candidate : Sketch) (hp : e.path = [])
    (hedit : s.sketch.edit s.app e = some candidate) :
    s.feed o policy e = s.recheck o policy candidate e s.sketch.program

@[semantics "initial-algebras-folds" (requirement := R14)]
proof_goal feed_undo {o : Oracle} {s next : SourceSession} {a : List Nat} {q old : NativeEff}
    {candidate : Sketch} {step : Edit.Step} (hc : s.Coherent)
    (hat : (Node.eff s.sketch.program).at_ a = some (.eff old))
    (hfill : s.sketch.fillAt a q = some candidate)
    (hnext : (s.feed o .draft (.fill a q)).value = .ok (next,step)) :
    ∃ back, (next.feed o .draft (.fill a old)).value = .ok (s,back)

end SourceSession

/-- Placement: initial-algebras-folds; source-session-coherent's reachable-state obligation, R14.
The sealed replay witnesses every accepted action history, including revert.
Consumer: SourceSession.reached_view. This establishes no admission or progress claim. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
proof_goal Doc.coherent (d : Doc) : d.session.Coherent

namespace SourceSession
/-- The old draft-list reach, stated through the sole document replay.
Placement: source-session-coherent, initial-algebras-folds, R14.
This retains every old application, initial sketch, and edit list without a coherence premise.
Consumer: the draft case of Doc.coherent and transport of the old reached_view observation.
It establishes no admission, progress, or native behavior. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
proof_goal replay_drafts_view (app : SigApp) (initial : Sketch) (edits : List Edit) (id : DocId) :
    ∃ session, replayDoc ⟨id,app,initial⟩ (edits.map DocAction.draft) = .ok session ∧
      session.app = app ∧
      session.sketch = edits.foldl (fun s e => (s.edit app e).getD s) initial ∧
      session.view.table = session.sketch.sourceTable app ∧
      session.view.refusals = session.sketch.sourceRefusals app ∧
      session.view.type = (session.sketch.sourceCheck app).toOption

/-- Every sealed document exposes the exact source table, refusals, and root observation. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem reached_view (d : Doc) :
    d.session.view.table = d.session.sketch.sourceTable d.session.app ∧
    d.session.view.refusals = d.session.sketch.sourceRefusals d.session.app ∧
    d.session.view.type = (d.session.sketch.sourceCheck d.session.app).toOption :=
  view_eq (Doc.coherent d)
end SourceSession
end Effect4.Program
