import Effect4.Program.Edit
import Effect4.Laws.Program.Typing.Splice
import Effect4.Laws.Program.References
import Effect4.Laws.Auto.Semantics

/-!
# Laws.Program.Edit — an edit session keeps its table, and an edit can be undone

`Program/Edit.lean` defines the edit session: a program with its address table, fed one edit at a
time. This module holds its laws.

| Statement | In words | From |
| --- | --- | --- |
| `Table.typedAt_table` | where a program's table holds a type at an address, that is the focus there | the table's definition, `effTy_of_check` |
| `Table.typedAt_table_nil` | where it holds one at the root, the program has that type | `Table.typedAt_table`, `focusAt_nil` |
| `EditSession.open_coherent` | an open session is coherent | `annotate_eq_table` |
| `EditSession.feed_coherent` | an edit keeps a session coherent | `table_splice` where the edit splices |
| `EditSession.run_coherent` | so does a run of edits | the fold |
| `EditSession.view_refusals` | a coherent session shows its program's refusals | the definition |
| `EditSession.view_type` | a coherent session shows its program's type | `table_head`, `effTy_of_check` |
| `EditSession.feed_shown` | a spliced edit shows again exactly the new subtree's addresses | `Annotate.check_eq` |
| `EditSession.feed_undo` | an edit, then the edit that puts back the old sub-program, restores a coherent session | `replaceAt_spec`, coherence |

## Placement

Concept `initial-algebras-folds`; property: the address table is a fold of the program, and an
edit is a lens update, so a cache of the table stays the fold of its program under edits.
Requirement R14 (program as data: regions, the focus, holes), under decisions row 334.

- **`edit-session-coherent`** (claim, role preservation; pointer `EditSession.run_coherent`).
  Reach: one signature and one root environment; a program of the structural checker; every list
  of edits `replace`. The splice is taken only where the table types the root and the address,
  and the checker gives the new sub-program the old type; every other edit computes the table
  again. Not established: a program with a definition block (the splice over a whole program's
  parts is the next slice); holes; a run; the cost, which no theorem counts. Consumers: the view's
  readings (`view_refusals`, `view_type`), the undo law, and the native view's repaint set.
- **`edit-session-undo`** (claim, role compatibility; pointer `EditSession.feed_undo`). Reach: a
  coherent session, and an edit that applied. Not established: that two edits at disjoint
  addresses commute; an undo of a run. Consumer: a tool's undo, as one more edit.
- The helpers `Table.typedAt_table`, `Table.typedAt_table_nil` and `EditSession.feed_replace`
  are steps of `edit-session-coherent` and `edit-session-undo`. `feed_shown` is a step of the
  repaint set, which the view's slice consumes.
-/

set_option autoImplicit false

namespace Effect4.Program

open Conform.Effect4.Typing

variable {Op : Type}

/-! ## The table answers the focus -/

/-- **The table answers the focus.** Where a program's table holds an environment of variables and
a type at an address, the focus there is that environment and that type, at the sub-program the
address holds. So a tool reads a focus off a table it keeps, with no check. A step of
`edit-session-coherent`. Its consumers are `Table.typedAt_table_nil` and
`EditSession.feed_coherent`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Table.typedAt_table {s : Signature Op} {env0 : TyEnv} {p : Eff Op} {a : List Nat}
    {tys : TyEnv} {ty : EffTy} (h : Table.typedAt (table s env0 p) a = some (tys, ty)) :
    ∃ q, focusAt s env0 p a = some ⟨q, tys, ty⟩ := by
  unfold Table.typedAt at h
  split at h
  next path tys' ty' hfind =>
    cases h
    have hpath := List.find?_some hfind
    rw [decide_eq_true_eq] at hpath
    subst hpath
    obtain ⟨a', -, he⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hfind)
    simp only [Table.Entry.mk.injEq] at he
    obtain ⟨rfl, henv, hres⟩ := he
    rw [henv] at hres
    split at hres
    next q tys'' hat henv' =>
      cases henv'
      exact ⟨q, focusAt_eq_some.mpr ⟨hat, henv, by rw [effTy_of_check (Option.some.inj hres)]; rfl⟩⟩
    next => cases hres
  next => cases h

/-- **The table's root types the program.** Where a program's table holds a type at the root,
the program has that type in the root's environment. A step of `edit-session-coherent`. Its
consumer is `EditSession.feed_coherent`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Table.typedAt_table_nil {s : Signature Op} {env0 : TyEnv} {p : Eff Op}
    {tys : TyEnv} {ty : EffTy} (h : Table.typedAt (table s env0 p) [] = some (tys, ty)) :
    HasTy s env0 p ty := by
  obtain ⟨q, hf⟩ := Table.typedAt_table h
  rw [focusAt_nil] at hf
  cases ht : effTy s env0 p with
  | none =>
    rw [ht] at hf
    cases hf
  | some t =>
    rw [ht] at hf
    cases hf
    exact effTy_sound s p env0 _ ht

namespace EditSession

/-! ## Coherence -/

/-- **An open session is coherent**: `annotate` is the table. A step of
`edit-session-coherent`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem open_coherent (s : Signature Op) (env : TyEnv) (p : Eff Op) :
    (EditSession.open s env p).Coherent :=
  annotate_eq_table s env p

/-- **An edit keeps a session coherent.** Where the edit splices, the table read the focus and the
root's type, and the checker gave the new sub-program the focus's type, so the splice law
(`table_splice`) gives the edited program's table. Every other edit computes the table again, or
changes nothing. A step of `edit-session-coherent`. Its consumers are `run_coherent` and
`feed_undo`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem feed_coherent {l : EditSession Op} (h : l.Coherent) (e : Edit Op) :
    (l.feed e).1.Coherent := by
  cases e with
  | replace a q =>
    simp only [feed]
    split
    next p' hrep =>
      split
      next r tys ty hroot hat =>
        split
        next sub ty' hcheck =>
          split
          next hty =>
            subst hty
            rw [h] at hroot hat
            obtain ⟨_, hf⟩ := Table.typedAt_table hat
            obtain ⟨_, T⟩ := r
            have hp := Table.typedAt_table_nil hroot
            rw [Annotate.check_eq] at hcheck
            obtain ⟨hsub, hq⟩ := Prod.mk.inj hcheck
            have hq' : HasTy l.sig tys q ty' :=
              effTy_sound l.sig q tys ty' (by rw [effTy_of_check hq]; rfl)
            show Table.splice l.table a sub = Program.table l.sig l.env p'
            rw [h, ← hsub]
            exact (table_splice hp hf hq' hrep).symm
          next => exact annotate_eq_table l.sig l.env p'
        next => exact annotate_eq_table l.sig l.env p'
      next => exact annotate_eq_table l.sig l.env p'
    next => exact h

/-- **A run of edits keeps a session coherent**: the fold of `feed_coherent`. With
`open_coherent`, the table of every session reached by an open and edits is its program's table.
The pointer of `edit-session-coherent`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem run_coherent {l : EditSession Op} (h : l.Coherent) (edits : List (Edit Op)) :
    (l.run edits).Coherent := by
  induction edits generalizing l with
  | nil => exact h
  | cons e edits ih => exact ih (feed_coherent h e)

/-! ## The view -/

/-- **A coherent session shows its program's refusals**: the head is `explain`'s located refusal
(`refusals_head`), and the list is empty exactly when the checker admits the program
(`refusals_nil_iff`). A step of `edit-session-coherent`'s consumers. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem view_refusals {l : EditSession Op} (h : l.Coherent) :
    l.view.refusals = refusals l.sig l.env l.program := by
  unfold view
  rw [h]
  rfl

/-- **A coherent session shows its program's type**, the checker's answer at the root, with no
check. A step of `edit-session-coherent`'s consumers. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem view_type {l : EditSession Op} (h : l.Coherent) :
    l.view.type = effTy l.sig l.env l.program := by
  unfold view
  rw [h]
  obtain ⟨rest, ht⟩ := table_head l.sig l.env l.program
  rw [ht]
  cases hc : Checker.check l.sig l.env [] l.program with
  | ok t => rw [effTy_of_check hc]; rfl
  | error e => rw [effTy_of_check hc]; rfl

/-- **The addresses a spliced edit shows again are the new subtree's**, at the edited address.
A step of the repaint set (the live authoring note, §3). -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem feed_shown {l : EditSession Op} {a : List Nat} {q : Eff Op}
    {shown : List (List Nat)} (h : (l.feed (.replace a q)).2 = .spliced shown) :
    shown = (Node.addresses (.eff q)).map (a ++ ·) := by
  simp only [feed] at h
  split at h
  next p' hrep =>
    split at h
    next r tys ty hroot hat =>
      split at h
      next sub ty' hcheck =>
        split at h
        next hty =>
          cases h
          rw [Annotate.check_eq] at hcheck
          obtain ⟨hsub, -⟩ := Prod.mk.inj hcheck
          rw [← hsub, tableAt, List.map_map]
          rfl
        next => cases h
      next => cases h
    next => cases h
  next => cases h

/-! ## What an edit keeps -/

/-- **An edit keeps the signature and the root's environment.** A step of
`edit-session-coherent`. Its consumer is `run_keeps`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem feed_keeps (l : EditSession Op) (e : Edit Op) :
    (l.feed e).1.sig = l.sig ∧ (l.feed e).1.env = l.env := by
  cases e with
  | replace a q =>
    simp only [feed]
    split
    next =>
      split
      next =>
        split
        next => split <;> exact ⟨rfl, rfl⟩
        next => exact ⟨rfl, rfl⟩
      next => exact ⟨rfl, rfl⟩
    next => exact ⟨rfl, rfl⟩

/-- **A run of edits keeps the signature and the root's environment.** A step of
`edit-session-coherent`. Its consumer is `reached_view`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem run_keeps (l : EditSession Op) (edits : List (Edit Op)) :
    (l.run edits).sig = l.sig ∧ (l.run edits).env = l.env := by
  induction edits generalizing l with
  | nil => exact ⟨rfl, rfl⟩
  | cons e edits ih =>
    obtain ⟨hs, he⟩ := ih (l.feed e).1
    obtain ⟨hs', he'⟩ := feed_keeps l e
    exact ⟨hs.trans hs', he.trans he'⟩

/-- **A spliced edit's table is a splice of the old one**, and the addresses it shows are the
spliced segment's. A step of `edit-repaint-set`. Its consumer is `feed_repaint`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem feed_spliced {l : EditSession Op} {a : List Nat} {q : Eff Op}
    {shown : List (List Nat)} (h : (l.feed (.replace a q)).2 = .spliced shown) :
    ∃ sub, (l.feed (.replace a q)).1.table = Table.splice l.table a sub ∧
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

/-! ## A session reached by edits -/

/-- **Every session reached by an open and edits is coherent.** A step of
`edit-session-coherent`. Its consumer is `reached_view`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem reached_coherent (s : Signature Op) (env : TyEnv) (p : Eff Op) (edits : List (Edit Op)) :
    ((EditSession.open s env p).run edits).Coherent :=
  run_coherent (open_coherent s env p) edits

/-- **What a session shows is the checker's answer on its program**, after an open and any run of
edits: the program's refusals, whose head is `explain`'s and which are empty exactly when the
checker admits it, and the program's type. The session checks only what its edits changed. The
pointer of `edit-session-coherent`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem reached_view (s : Signature Op) (env : TyEnv) (p : Eff Op) (edits : List (Edit Op)) :
    ((EditSession.open s env p).run edits).view.refusals =
        refusals s env ((EditSession.open s env p).run edits).program ∧
      ((EditSession.open s env p).run edits).view.type =
        effTy s env ((EditSession.open s env p).run edits).program := by
  obtain ⟨hs, he⟩ := run_keeps (EditSession.open s env p) edits
  have h₁ := view_refusals (reached_coherent s env p edits)
  have h₂ := view_type (reached_coherent s env p edits)
  rw [hs, he] at h₁ h₂
  exact ⟨h₁, h₂⟩

/-- **A spliced edit repaints its subtree and nothing else**: the addresses it shows again are the
new subtree's, and every entry of the new table at another address is an entry of the old table.
The pointer of `edit-repaint-set`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem feed_repaint {l : EditSession Op} {a : List Nat} {q : Eff Op}
    {shown : List (List Nat)} (h : (l.feed (.replace a q)).2 = .spliced shown) :
    shown = (Node.addresses (.eff q)).map (a ++ ·) ∧
      ∀ x ∈ (l.feed (.replace a q)).1.table, x.path ∉ shown → x ∈ l.table := by
  refine ⟨feed_shown h, ?_⟩
  obtain ⟨sub, ht, hs⟩ := feed_spliced h
  intro x hx hout
  rw [ht] at hx
  rcases Table.mem_splice hx with hx | hx
  · exact absurd (by rw [hs]; exact List.mem_map_of_mem hx) hout
  · exact hx

/-! ## Undo -/

/-- **An edit that applies replaces the program and keeps the signature and the root's
environment.** A step of `edit-session-undo`. Its consumer is `feed_undo`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem feed_replace {l : EditSession Op} {a : List Nat} {q p' : Eff Op}
    (hrep : (Node.eff l.program).replaceAt a (.eff q) = some (.eff p')) :
    (l.feed (.replace a q)).1.sig = l.sig ∧ (l.feed (.replace a q)).1.env = l.env ∧
      (l.feed (.replace a q)).1.program = p' := by
  simp only [feed, hrep]
  split
  next =>
    split
    next => split <;> exact ⟨rfl, rfl, rfl⟩
    next => exact ⟨rfl, rfl, rfl⟩
  next => exact ⟨rfl, rfl, rfl⟩

/-- **Two coherent sessions of one program are one session**: the table is the program's. A
step of `edit-session-undo`. Its consumer is `feed_undo`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Coherent.ext {l₁ l₂ : EditSession Op} (h₁ : l₁.Coherent) (h₂ : l₂.Coherent)
    (hs : l₁.sig = l₂.sig) (he : l₁.env = l₂.env) (hp : l₁.program = l₂.program) : l₁ = l₂ := by
  obtain ⟨s₁, e₁, p₁, t₁⟩ := l₁
  obtain ⟨s₂, e₂, p₂, t₂⟩ := l₂
  unfold Coherent at h₁ h₂
  simp only at hs he hp h₁ h₂
  subst hs he hp
  rw [h₁, h₂]

/-- **Undo**: an edit that applies, then the edit that puts back the old sub-program, restores a
coherent session exactly, its table included. The path lens's get-put (`replaceAt_spec`) restores
the program, and coherence restores the table. The pointer of `edit-session-undo`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem feed_undo {l : EditSession Op} (h : l.Coherent) {a : List Nat} {q old p' : Eff Op}
    (hat : (Node.eff l.program).at_ a = some (.eff old))
    (hrep : (Node.eff l.program).replaceAt a (.eff q) = some (.eff p')) :
    ((l.feed (.replace a q)).1.feed (.replace a old)).1 = l := by
  obtain ⟨hs1, he1, hp1⟩ := feed_replace hrep
  have hback : (Node.eff (l.feed (.replace a q)).1.program).replaceAt a (.eff old) =
      some (.eff l.program) := by
    rw [hp1]
    exact (Node.replaceAt_spec hrep).2.2 _ hat
  obtain ⟨hs2, he2, hp2⟩ := feed_replace hback
  exact Coherent.ext (feed_coherent (feed_coherent h _) _) h (hs2.trans hs1) (he2.trans he1) hp2

end EditSession

end Effect4.Program
