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
| `SourceSession.reached_view` | after an open and any edits, a session shows the table at the source's addresses, its refusals and the type through the references | `EditSession.feed_coherent` at the expansion |
| `SourceSession.feed_undo` | an edit, then the edit that puts back the old sub-program as written, restores the session | `EditSession.Coherent.ext` |
| `SourceSession.open_shown_of_refSites_nil` | on a sketch with no reference, an open shows the edit session's own open | `expandRefs_eq_self_of_refSites_nil` |

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
- **`source-session-coherent`** (proposed claim, role preservation; pointer
  `SourceSession.reached_view`). Reach: one application; every sketch; every list of edits. An
  edit splices where the expansion of the edited sketch is the expansion's own edit at the same
  address; any other edit opens the expansion's edit session again. Not established: that an
  edit inside a referenced layer splices; a run; the cost. Consumer: the session tool.
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

namespace SourceSession

/-! ## Coherence -/

/-- **An open session is coherent**: it holds the edit session of the sketch's expansion. A step
of `source-session-coherent`. Its consumer is `reached_coherent`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem open_coherent (app : SigApp) (s : Sketch) : (SourceSession.open app s).Coherent :=
  ⟨rfl, EditSession.open_coherent app s.expand⟩

/-- **An edit keeps the application, and one that applies holds the edited sketch.** A step of
`source-session-coherent` and of `source-session-undo`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem feed_keeps (l : SourceSession) (e : Edit) :
    (l.feed e).1.app = l.app ∧ ∀ s', l.sketch.edit l.app e = some s' → (l.feed e).1.sketch = s' := by
  unfold feed
  cases hs : l.sketch.edit l.app e with
  | none =>
    refine ⟨rfl, fun s' h => ?_⟩
    cases h
  | some s' =>
    refine ⟨?_, fun s'' h => ?_⟩
    · dsimp only
      split
      next =>
        split
        next => exact (EditSession.feed_keeps _ _).1
        next => rfl
      next => rfl
    · cases h
      dsimp only
      split
      next =>
        split
        next => rfl
        next => rfl
      next => rfl

/-- **An edit keeps a session coherent.** Where the expansion's own edit gives the new
expansion, the edit session of the expansion takes it (`EditSession.feed_coherent`); every other
edit opens that edit session again. A step of `source-session-coherent`. Its consumers are
`run_coherent` and `feed_undo`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem feed_coherent {l : SourceSession} (h : l.Coherent) (e : Edit) : (l.feed e).1.Coherent := by
  unfold feed
  cases hs : l.sketch.edit l.app e with
  | none => exact h
  | some s' =>
    dsimp only
    split
    next e' he =>
      split
      next hcond =>
        obtain ⟨y, hy, hpair⟩ := Option.map_eq_some_iff.mp hcond
        have hyx : y = s'.expand := by
          obtain ⟨yp, yh⟩ := y
          simp only [Prod.mk.injEq] at hpair
          obtain ⟨rfl, rfl⟩ := hpair
          rfl
        subst hyx
        exact ⟨EditSession.feed_edit hy, EditSession.feed_coherent h.2 e'⟩
      next => exact open_coherent _ _
    next => exact open_coherent _ _

/-- **A run of edits keeps a session coherent.** A step of `source-session-coherent`. Its
consumer is `reached_coherent`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem run_coherent {l : SourceSession} (h : l.Coherent) (edits : List Edit) :
    (l.run edits).Coherent := by
  induction edits generalizing l with
  | nil => exact h
  | cons e edits ih => exact ih (feed_coherent h e)

/-- **A run of edits keeps the application.** A step of `source-session-coherent`. Its consumer
is `reached_view`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem run_keeps (l : SourceSession) (edits : List Edit) : (l.run edits).app = l.app := by
  induction edits generalizing l with
  | nil => rfl
  | cons e edits ih => exact (ih (l.feed e).1).trans (feed_keeps l e).1

/-- **Every session reached by an open and edits is coherent.** A step of
`source-session-coherent`. Its consumer is `reached_view`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem reached_coherent (app : SigApp) (s : Sketch) (edits : List Edit) :
    ((SourceSession.open app s).run edits).Coherent :=
  run_coherent (open_coherent app s) edits

/-! ## The view -/

/-- **A coherent session's table is its sketch's table at the source's addresses**
(`source-annotation-agrees`). A step of `source-session-coherent`. Its consumers are the view's
laws. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem table_eq {l : SourceSession} (h : l.Coherent) : l.table = l.sketch.sourceTable l.app := by
  unfold table
  rw [h.2, h.1, ← Sketch.annotate_eq_table]
  exact Sketch.sourceAnnotate_eq_sourceTable l.sketch l.app

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

/-- **What a session shows, after an open and any run of edits**: the table at the source's
addresses, its refusals, whose head is the check's and which are empty exactly when it succeeds,
and the type through the references, which is admission's typing. The pointer of the proposed
claim `source-session-coherent`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem reached_view (app : SigApp) (s : Sketch) (edits : List Edit) :
    ((SourceSession.open app s).run edits).view.table =
        ((SourceSession.open app s).run edits).sketch.sourceTable app ∧
      ((SourceSession.open app s).run edits).view.refusals =
        ((SourceSession.open app s).run edits).sketch.sourceRefusals app ∧
      ((SourceSession.open app s).run edits).view.type =
        (((SourceSession.open app s).run edits).sketch.sourceCheck app).toOption := by
  have happ : ((SourceSession.open app s).run edits).app = app := run_keeps _ edits
  have h := reached_coherent app s edits
  have h₀ := table_eq h
  have h₁ := view_refusals h
  have h₂ := view_type h
  rw [happ] at h₀ h₁ h₂
  exact ⟨h₀, h₁, h₂⟩

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

/-! ## Undo -/

/-- **Two coherent sessions of one application and one sketch are one session.** A step of
`source-session-undo`. Its consumer is `feed_undo`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Coherent.ext {l₁ l₂ : SourceSession} (h₁ : l₁.Coherent) (h₂ : l₂.Coherent)
    (ha : l₁.app = l₂.app) (hs : l₁.sketch = l₂.sketch) : l₁ = l₂ := by
  obtain ⟨s₁, x₁⟩ := l₁
  obtain ⟨s₂, x₂⟩ := l₂
  simp only at hs
  subst hs
  have hx : x₁ = x₂ := EditSession.Coherent.ext h₁.2 h₂.2 ha (h₁.1.trans h₂.1.symm)
  subst hx
  rfl

/-- **Undo**: an edit that applies, then the edit that puts back the old sub-program as
written, restores a coherent session exactly. The path lens's get-put (`replaceAt_spec`)
restores the sketch, and coherence the edit session of its expansion. The pointer of the
proposed claim `source-session-undo`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem feed_undo {l : SourceSession} (h : l.Coherent) {a : List Nat} {q old : NativeEff}
    {s' : Sketch} (hat : (Node.eff l.sketch.program).at_ a = some (.eff old))
    (hfill : l.sketch.fillAt a q = some s') :
    ((l.feed (.fill a q)).1.feed (.fill a old)).1 = l := by
  obtain ⟨p', hrep, rfl⟩ := Sketch.fillAt_some hfill
  have hs1 := (feed_keeps l (.fill a q)).2 _ hfill
  have hback : ((l.feed (.fill a q)).1.sketch).fillAt a old = some l.sketch := by
    rw [hs1, Sketch.fillAt_of_replaceAt ((Node.replaceAt_spec hrep).2.2 _ hat)]
  have hs2 := (feed_keeps _ (.fill a old)).2 _ hback
  exact Coherent.ext (feed_coherent (feed_coherent h _) _) h
    (((feed_keeps _ _).1).trans (feed_keeps _ _).1) hs2

/-! ## The connector to the edit session -/

/-- **On a sketch with no layer reference, an open shows the edit session's own open**: the
expansion is the sketch (`expandRefs_eq_self_of_refSites_nil`), no address is dropped, and no
reference is ill formed. The connector of the session through references to the edit session
(`AGENTS.md`, a second representation beside the old one). Its consumer is the session tool. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem open_shown_of_refSites_nil (app : SigApp) {s : Sketch} (h : s.program.refSites [] = []) :
    (SourceSession.open app s).shown = EditSession.open app s := by
  have hx : s.expand = s := by
    unfold Sketch.expand
    rw [expandRefs_eq_self_of_refSites_nil s.program h]
  have hf : s.program.firstRefFault = none := by
    unfold Eff.firstRefFault
    rw [h]
    rfl
  have hsites : s.sites = [] := by
    unfold Sketch.sites
    rw [h]
    rfl
  unfold shown table SourceSession.open SourceSession.app Table.atSource
  rw [hf, hsites, hx]
  dsimp only
  rw [(List.filter_eq_self (p := fun e : Table.Entry => !Table.belowSite [] e.path)).mpr
    fun _ _ => rfl]
  rfl

end SourceSession

end Effect4.Program
