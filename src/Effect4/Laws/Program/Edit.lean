import Effect4.Program.Edit
import Effect4.Laws.Program.Typing.PartsTable
import Effect4.Laws.Auto.Semantics

/-!
# Laws.Program.Edit — an edit session keeps its table, and an edit can be undone

`Program/Edit.lean` defines the edit session: a sketch with its address table, fed one edit at a
time. This module holds its laws.

| Statement | In words | From |
| --- | --- | --- |
| `Table.typedAt_table` | where a sketch's table holds a type below the root, that is the focus there | the table's definition, `effTy_of_check` |
| `Table.typedAt_table_nil` | the type the table holds at the root is the sketch's check's | `Sketch.table_head` |
| `EditSession.open_coherent` | an open session is coherent | `Sketch.annotate_eq_table` |
| `EditSession.feed_coherent` | an edit keeps a session coherent | `Sketch.table_fill` where the edit splices |
| `EditSession.run_coherent` | so does a run of edits | the fold |
| `EditSession.reached_view` | after an open and any edits, the view shows the sketch's refusals and type | coherence, `run_keeps` |
| `EditSession.feed_repaint` | a spliced edit shows again exactly the new subtree's addresses, and keeps every other entry | `Annotate.check_eq`, `Table.mem_splice` |
| `EditSession.feed_undo` | an edit, then the edit that puts back the old sub-program, restores a coherent session | `replaceAt_spec`, coherence |

## Placement

Concept `initial-algebras-folds`; property: the address table is a fold of the program, and an
edit is a lens update, so a cache of the table stays the fold of its sketch under edits.
Requirement R14 (program as data: regions, the focus, holes), under decisions row 334.

- **`edit-session-coherent`** (claim, role preservation; pointer `EditSession.reached_view`).
  Reach: one application; every sketch, definition block and holes included; every list of edits
  `fill`. The splice is taken only below the root, where the table types the root and the address
  and the checker gives the new sub-program the old type at the part's signature; every other
  edit computes the table again. Not established: an edit of the hole table; a run; the cost,
  which no theorem counts. Consumers: a tool's view of a sketch under edits.
- **`edit-session-undo`** (claim, role compatibility; pointer `EditSession.feed_undo`). Reach: a
  coherent session, and an edit that applied. Not established: that two edits at disjoint
  addresses commute; an undo of a run. Consumer: a tool's undo, as one more edit.
- **`edit-repaint-set`** (claim, role preservation; pointer `EditSession.feed_repaint`). Reach:
  an edit that spliced. Not established: a page drawn from the table. Consumer: the view's repaint
  set.
- Every other statement is a step of these three, and names its consumer.
-/

set_option autoImplicit false

namespace Effect4.Program

open Conform.Effect4.Typing

/-! ## The table answers the focus -/

/-- **The table answers the focus.** Where a sketch's table holds an environment of variables and
a type at an address below the root, the focus there is that environment and that type, at the
sub-program the address holds. So a tool reads a focus off a table it keeps, with no check. A
step of `edit-session-coherent`. Its consumer is `EditSession.feed_coherent`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Table.typedAt_table {s : Sketch} {app : SigApp} {a : List Nat} {tys : TyEnv} {ty : EffTy}
    (h : Table.typedAt (s.table app) a = some (tys, ty)) (ha : a ≠ []) :
    ∃ q, s.focusAt app a = some ⟨q, tys, ty⟩ := by
  unfold Table.typedAt at h
  split at h
  next path tys' ty' hfind =>
    cases h
    have hpath := List.find?_some hfind
    rw [decide_eq_true_eq] at hpath
    subst hpath
    obtain ⟨a', -, he⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hfind)
    cases a' with
    | nil => exact absurd (congrArg Table.Entry.path he).symm ha
    | cons i r =>
      simp only [Sketch.tableEntry] at he
      cases hp : s.program.partAt (app.withHoles s.holes).signature [] (i :: r) with
      | none =>
        rw [hp] at he
        cases he
      | some pr =>
        obtain ⟨part, rest⟩ := pr
        rw [hp] at he
        simp only [Table.Entry.mk.injEq] at he
        obtain ⟨rfl, henv, hres⟩ := he
        rw [henv] at hres
        split at hres
        next q tys'' hat henv' =>
          cases henv'
          refine ⟨q, ?_⟩
          show (s.program.partAt (app.withHoles s.holes).signature [] (i :: r)).bind
            (fun pr => focusAt pr.1.sig pr.1.env pr.1.program pr.2) = _
          rw [hp, Option.bind_some]
          exact focusAt_eq_some.mpr ⟨hat, henv,
            by rw [effTy_of_check (Option.some.inj hres)]; rfl⟩
        next => cases hres
  next => cases h

/-- **The table's root holds the sketch's check.** The type a sketch's table holds at the root is
its check's answer. A step of `edit-session-coherent`. Its consumers are
`EditSession.feed_coherent` and `EditSession.view_type`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Table.typedAt_table_nil (s : Sketch) (app : SigApp) :
    (Table.typedAt (s.table app) []).map (·.2) = (s.check app).toOption := by
  obtain ⟨rest, ht⟩ := Sketch.table_head s app
  rw [ht]
  cases s.check app <;> rfl

/-! ## An omission: planned -/

/-- **A typed sketch's table stays under a grown hole table.** Every entry of a typed sketch is
typed, and a typed sub-program keeps its environment and its answer at an extension of the
signature (`check_ext`). A step of `omit-splices-table`. Its consumer is `Sketch.table_omit`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
proof_goal Sketch.table_more_holes {s : Sketch} {app : SigApp} {T : EffTy}
    (hs : s.check app = .ok T) (more : RowTable) :
    ({ s with holes := s.holes ++ more } : Sketch).table app = s.table app

/-- **An omission at the focus's type splices the table**: the hole row declares the focus's
three columns, and the table is the old one with the subtree's segment replaced by the hole's one
entry. Its proof is `Sketch.table_more_holes`, then `Sketch.table_fill` at the grown sketch with
the hole as the filling (`Sketch.hole_hasTy`). The pointer of `omit-splices-table`; the edit
session's `omitAt` splices once it is proved. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
proof_goal Sketch.table_omit {s s' : Sketch} {app : SigApp} {T : EffTy} {path : List Nat}
    {f : Focus NativeOp} (name : String) (hs : s.check app = .ok T) (hnil : path ≠ [])
    (hf : s.focusAt app path = some f) (hans : f.ty.answer.closed = true)
    (herr : f.ty.error.closed = true) (hansN : f.ty.answer.normalize = f.ty.answer)
    (herrN : f.ty.error.normalize = f.ty.error)
    (homit : s.omitAt app path (Row.hole name f.ty.answer f.ty.error f.ty.requires.elems) = some s') :
    s'.table app = Table.splice (s.table app) path
      [⟨path, some (.env f.env), some (.ok f.ty)⟩]

namespace EditSession

/-! ## Coherence -/

/-- **An open session is coherent**: the table part by part is the table. A step of
`edit-session-coherent`. Its consumer is `reached_coherent`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem open_coherent (app : SigApp) (s : Sketch) : (EditSession.open app s).Coherent :=
  Sketch.annotate_eq_table s app

/-- **An edit keeps a session coherent.** Where the edit splices, the table read the focus and the
root's type, and the checker gave the new sub-program the focus's type at the part's signature,
so the splice over a whole program's parts (`Sketch.table_fill`) gives the edited sketch's table.
Every other edit computes the table again, or changes nothing. A step of
`edit-session-coherent`. Its consumers are `run_coherent` and `feed_undo`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem feed_coherent {l : EditSession} (h : l.Coherent) (e : Edit) : (l.feed e).1.Coherent := by
  cases e with
  | fill a q =>
    simp only [feed]
    split
    next s' hfill =>
      split
      next i r root tys ty hroot hat =>
        split
        next sub ty' hcheck =>
          split
          next hty =>
            subst hty
            rw [h] at hroot hat
            obtain ⟨_, T⟩ := root
            have hs : l.sketch.check l.app = .ok T := by
              have h0 := Table.typedAt_table_nil l.sketch l.app
              rw [hroot] at h0
              cases hc : l.sketch.check l.app with
              | ok t =>
                rw [hc] at h0
                cases h0
                rfl
              | error e =>
                rw [hc] at h0
                cases h0
            obtain ⟨_, hf⟩ := Table.typedAt_table hat (List.cons_ne_nil i r)
            rw [Annotate.check_eq] at hcheck
            obtain ⟨hsub, hq⟩ := Prod.mk.inj hcheck
            have hq' : HasTy (l.sketch.sigAt l.app (i :: r)) tys q ty' :=
              effTy_sound _ q tys ty' (by rw [effTy_of_check hq]; rfl)
            show Table.splice l.table (i :: r) sub = s'.table l.app
            rw [h, ← hsub]
            exact (Sketch.table_fill hs (List.cons_ne_nil i r) hf hq' hfill).symm
          next => exact Sketch.annotate_eq_table s' l.app
        next => exact Sketch.annotate_eq_table s' l.app
      next => exact Sketch.annotate_eq_table s' l.app
    next => exact h
  | omitAt a row =>
    simp only [feed]
    split
    next s' _ => exact Sketch.annotate_eq_table s' l.app
    next => exact h

/-- **A run of edits keeps a session coherent**: the fold of `feed_coherent`. A step of
`edit-session-coherent`. Its consumer is `reached_coherent`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem run_coherent {l : EditSession} (h : l.Coherent) (edits : List Edit) :
    (l.run edits).Coherent := by
  induction edits generalizing l with
  | nil => exact h
  | cons e edits ih => exact ih (feed_coherent h e)

/-- **Every session reached by an open and edits is coherent.** A step of
`edit-session-coherent`. Its consumer is `reached_view`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem reached_coherent (app : SigApp) (s : Sketch) (edits : List Edit) :
    ((EditSession.open app s).run edits).Coherent :=
  run_coherent (open_coherent app s) edits

/-! ## What an edit keeps -/

/-- **An edit keeps the application, and one that applies holds the filled sketch.** A step of
`edit-session-coherent` and of `edit-session-undo`. Its consumers are `run_keeps` and
`feed_undo`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem feed_keeps (l : EditSession) (e : Edit) :
    (l.feed e).1.app = l.app ∧
      ∀ a q s', e = .fill a q → l.sketch.fillAt a q = some s' → (l.feed e).1.sketch = s' := by
  cases e with
  | fill a q =>
    simp only [feed]
    split
    next s' hfill =>
      refine ⟨?_, fun a' q' s'' he hf => ?_⟩
      · split
        next =>
          split
          next => split <;> rfl
          next => rfl
        next => rfl
      · cases he
        rw [hfill, Option.some.injEq] at hf
        subst hf
        split
        next =>
          split
          next => split <;> rfl
          next => rfl
        next => rfl
    next hnone =>
      refine ⟨rfl, fun a' q' s'' he hf => ?_⟩
      cases he
      rw [hnone] at hf
      cases hf
  | omitAt a row =>
    refine ⟨?_, fun a' q' s'' he _ => by cases he⟩
    simp only [feed]
    split <;> rfl

/-- **A run of edits keeps the application.** A step of `edit-session-coherent`. Its consumer is
`reached_view`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem run_keeps (l : EditSession) (edits : List Edit) : (l.run edits).app = l.app := by
  induction edits generalizing l with
  | nil => rfl
  | cons e edits ih => exact (ih (l.feed e).1).trans (feed_keeps l e).1

/-! ## The view -/

/-- **A coherent session shows its sketch's refusals**: the head is the sketch's check's refusal,
and the list is empty exactly when the sketch checks (`Sketch.refusals_nil_iff`). A step of
`edit-session-coherent`. Its consumer is `reached_view`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem view_refusals {l : EditSession} (h : l.Coherent) :
    l.view.refusals = l.sketch.refusals l.app := by
  unfold view
  rw [h]
  rfl

/-- **A coherent session shows its sketch's type**, its check's answer, with no check. A step of
`edit-session-coherent`. Its consumer is `reached_view`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem view_type {l : EditSession} (h : l.Coherent) :
    l.view.type = (l.sketch.check l.app).toOption := by
  unfold view
  rw [h]
  exact Table.typedAt_table_nil l.sketch l.app

/-- **What a session shows is the checker's answer on its sketch**, after an open and any run of
edits: the sketch's refusals, whose head is the check's and which are empty exactly when the
sketch checks, and the sketch's type. The session checks only what its edits changed. The pointer
of `edit-session-coherent`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem reached_view (app : SigApp) (s : Sketch) (edits : List Edit) :
    ((EditSession.open app s).run edits).view.refusals =
        ((EditSession.open app s).run edits).sketch.refusals app ∧
      ((EditSession.open app s).run edits).view.type =
        (((EditSession.open app s).run edits).sketch.check app).toOption := by
  have happ : ((EditSession.open app s).run edits).app = app := run_keeps _ edits
  have h₁ := view_refusals (reached_coherent app s edits)
  have h₂ := view_type (reached_coherent app s edits)
  rw [happ] at h₁ h₂
  exact ⟨h₁, h₂⟩

/-! ## The repaint set -/

/-- **The addresses a spliced edit shows again are the new subtree's**, at the edited address. A
step of `edit-repaint-set`. Its consumer is `feed_repaint`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem feed_shown {l : EditSession} {a : List Nat} {q : NativeEff}
    {shown : List (List Nat)} (h : (l.feed (.fill a q)).2 = .spliced shown) :
    shown = (Node.addresses (.eff q)).map (a ++ ·) := by
  simp only [feed] at h
  split at h
  next =>
    split at h
    next =>
      split at h
      next sub ty' hcheck =>
        split at h
        next =>
          cases h
          rw [Annotate.check_eq] at hcheck
          obtain ⟨hsub, -⟩ := Prod.mk.inj hcheck
          rw [← hsub, tableAt, List.map_map]
          rfl
        next => cases h
      next => cases h
    next => cases h
  next => cases h

/-- **A spliced edit's table is a splice of the old one**, and the addresses it shows are the
spliced segment's. A step of `edit-repaint-set`. Its consumer is `feed_repaint`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem feed_spliced {l : EditSession} {a : List Nat} {q : NativeEff}
    {shown : List (List Nat)} (h : (l.feed (.fill a q)).2 = .spliced shown) :
    ∃ sub, (l.feed (.fill a q)).1.table = Table.splice l.table a sub ∧
      shown = sub.map (·.path) := by
  revert h
  simp only [feed]
  split
  next =>
    split
    next =>
      split
      next sub _ _ =>
        split
        next => intro h; cases h; exact ⟨sub, rfl, rfl⟩
        next => intro h; cases h
      next => intro h; cases h
    next => intro h; cases h
  next => intro h; cases h

/-- **A spliced edit repaints its subtree and nothing else**: the addresses it shows again are the
new subtree's, and every entry of the new table at another address is an entry of the old table.
The pointer of `edit-repaint-set`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem feed_repaint {l : EditSession} {a : List Nat} {q : NativeEff}
    {shown : List (List Nat)} (h : (l.feed (.fill a q)).2 = .spliced shown) :
    shown = (Node.addresses (.eff q)).map (a ++ ·) ∧
      ∀ x ∈ (l.feed (.fill a q)).1.table, x.path ∉ shown → x ∈ l.table := by
  refine ⟨feed_shown h, ?_⟩
  obtain ⟨sub, ht, hs⟩ := feed_spliced h
  intro x hx hout
  rw [ht] at hx
  rcases Table.mem_splice hx with hx | hx
  · exact absurd (by rw [hs]; exact List.mem_map_of_mem hx) hout
  · exact hx

/-! ## Undo -/

/-- **Two coherent sessions of one application and one sketch are one session**: the table is the
sketch's. A step of `edit-session-undo`. Its consumer is `feed_undo`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Coherent.ext {l₁ l₂ : EditSession} (h₁ : l₁.Coherent) (h₂ : l₂.Coherent)
    (ha : l₁.app = l₂.app) (hs : l₁.sketch = l₂.sketch) : l₁ = l₂ := by
  obtain ⟨a₁, s₁, t₁⟩ := l₁
  obtain ⟨a₂, s₂, t₂⟩ := l₂
  unfold Coherent at h₁ h₂
  simp only at ha hs h₁ h₂
  subst ha hs
  rw [h₁, h₂]

/-- **Undo**: an edit that applies, then the edit that puts back the old sub-program, restores a
coherent session exactly, its table included. The path lens's get-put (`replaceAt_spec`) restores
the sketch, and coherence restores the table. The pointer of `edit-session-undo`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem feed_undo {l : EditSession} (h : l.Coherent) {a : List Nat} {q old : NativeEff}
    {s' : Sketch} (hat : (Node.eff l.sketch.program).at_ a = some (.eff old))
    (hfill : l.sketch.fillAt a q = some s') :
    ((l.feed (.fill a q)).1.feed (.fill a old)).1 = l := by
  obtain ⟨p', hrep, rfl⟩ := Sketch.fillAt_some hfill
  have hs1 := (feed_keeps l (.fill a q)).2 a q _ rfl hfill
  have hback : ((l.feed (.fill a q)).1.sketch).fillAt a old = some l.sketch := by
    rw [hs1, Sketch.fillAt_of_replaceAt ((Node.replaceAt_spec hrep).2.2 _ hat)]
  have hs2 := (feed_keeps _ (.fill a old)).2 a old _ rfl hback
  exact Coherent.ext (feed_coherent (feed_coherent h _) _) h
    (((feed_keeps _ _).1).trans (feed_keeps _ _).1) hs2

end EditSession

end Effect4.Program
