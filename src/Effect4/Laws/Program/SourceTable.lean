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
  tool (`Effect4.Tool.serve`, `src/Effect4/Tool/Serve.lean`).
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

/-- **A program stands where an edit of a program applies**: the replacement checks the sort of
the node it replaces. A step of `source-feed-edit`. Its consumer is `Sketch.edit_at`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Node.at_of_replaceAt_eff {n n' : Node NativeOp} {path : List Nat} {q : NativeEff}
    (h : n.replaceAt path (.eff q) = some n') : ∃ old, n.at_ path = some (.eff old) := by
  have happ := Node.replaceAt_append n path [] (.eff q)
  rw [List.append_nil, h] at happ
  cases hat : n.at_ path with
  | none =>
    rw [hat] at happ
    cases happ
  | some m =>
    rw [hat, Option.bind_some] at happ
    cases m with
    | eff old => exact ⟨old, rfl⟩
    | _ => cases happ

/-- **An edit that applies stands at a program**: a filling or an omission replaces a program. A
step of `source-feed-edit`. Its consumer is `SourceSession.feed_ok_cases`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Sketch.edit_at {s c : Sketch} {app : SigApp} {e : Edit} (h : s.edit app e = some c) :
    ∃ old, (Node.eff s.program).at_ e.path = some (.eff old) := by
  cases e with
  | fill a q =>
    obtain ⟨p', hrep, -⟩ := Sketch.fillAt_some h
    exact Node.at_of_replaceAt_eff hrep
  | omitAt a row =>
    obtain ⟨p', hrep, -⟩ := Sketch.fillAt_some h
    exact Node.at_of_replaceAt_eff hrep


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

/-! ## What a feed answers

`feed_ok_cases` reads every accepted feed off the definition: an edit that does not apply under
`draft` leaves the session, and an edit that applies either rechecks the module or splices a part
check's table. The statements below are steps of the claims `source-feed-edit`,
`source-feed-root` and `kept-fill-reference`, and each names its consumer. -/

/-- **A finished feed answers its next session and step.** A step of `source-feed-edit`. Its
consumer is `recheck_ok`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem finish_ok {policy : FeedPolicy} {s n : SourceSession} {e : Edit} {st : Edit.Step}
    {v : Verdict} {r : SourceSession × Edit.Step} (h : finish policy s n e st v = .ok r) :
    r = (n, st) := by
  unfold finish at h
  split at h
  · cases h
    rfl
  · cases h
  · cases h
    rfl
  · split at h
    · cases h
    · split at h
      · cases h
      · cases h
        rfl

/-- **An accepted recheck holds the candidate and the module check's table**, and records a
rechecked step. A step of `source-feed-edit`. Its consumer is `feed_ok_cases`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem recheck_ok {o : Oracle} {policy : FeedPolicy} {s : SourceSession} {c : Sketch} {e : Edit}
    {old : NativeEff} {r : SourceSession × Edit.Step}
    (h : (s.recheck o policy c e old).value = .ok r) :
    r = (⟨s.app, c, (run (.module s.app c.holes c.program)).table⟩, ⟨e, some old, .rechecked⟩) := by
  unfold recheck at h
  rw [Checked.bind_value, Checked.pure_value, Checked.ask_value] at h
  exact finish_ok h

/-- **Every accepted feed, by its route.** An edit that does not apply is accepted only by
`draft`, which leaves the session. An edit that applies either rechecks the module, or splices
the part check's table below the root at a typed focus, where the part keeps the focus's type and
the expansion moved only at the address; a draft splice also needs `draftOmitAllows` and a typed
root. A step of `source-feed-edit`. Its consumers are `feed_keeps` and the feed's coherence. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem feed_ok_cases {o : Oracle} {policy : FeedPolicy} {s : SourceSession} {e : Edit}
    {r : SourceSession × Edit.Step} (h : (s.feed o policy e).value = .ok r) :
    (s.sketch.edit s.app e = none ∧ policy = .draft ∧ r = (s, ⟨e, none, .unchanged⟩)) ∨
    ∃ old c, (Node.eff s.sketch.program).at_ e.path = some (.eff old) ∧
      s.sketch.edit s.app e = some c ∧
      (r = (⟨s.app, c, (run (.module s.app c.holes c.program)).table⟩, ⟨e, some old, .rechecked⟩) ∨
       ∃ key focus, e.path ≠ [] ∧ s.focusAt e.path = some focus ∧
         s.candidatePartKey e.path c = some key ∧ (run key).result = .ok focus.ty ∧
         s.expandedEditAgrees c e = true ∧
         (policy = .draft → draftOmitAllows e focus.ty = true ∧ s.view.type.isSome = true) ∧
         r = s.splice c e old (run key)) := by
  unfold feed at h
  split at h
  · rename_i old c hat hedit
    refine Or.inr ⟨old, c, hat, hedit, ?_⟩
    split at h
    · exact Or.inl (recheck_ok h)
    · rename_i i rest hpath
      have hne : e.path ≠ [] := by
        rw [hpath]
        exact List.cons_ne_nil i rest
      cases policy with
      | recheck => exact Or.inl (recheck_ok h)
      | draft =>
        dsimp only at h
        split at h
        · rename_i focus ty hfocus hview
          split at h
          · exact Or.inl (recheck_ok h)
          · rename_i hcond
            simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false] at hcond
            split at h
            · exact Or.inl (recheck_ok h)
            · rename_i key hkey
              rw [Checked.bind_value, Checked.ask_value] at h
              split at h
              · rename_i ty' hres
                split at h
                · rename_i hty
                  rw [Checked.pure_value] at h
                  cases h
                  refine Or.inr ⟨key, focus, hne, hfocus, hkey, ?_, hcond.1,
                    fun _ => ⟨hcond.2, ?_⟩, rfl⟩
                  · rw [hres, hty]
                  · rw [hview]
                    rfl
                · exact Or.inl (recheck_ok h)
              · exact Or.inl (recheck_ok h)
        · exact Or.inl (recheck_ok h)
      | keepExact =>
        dsimp only at h
        split at h
        · cases h
        · rename_i focus hfocus
          split at h
          · cases h
          · rename_i key hkey
            rw [Checked.bind_value, Checked.ask_value] at h
            split at h
            · cases h
            · rename_i ty' hres
              split at h
              · cases h
              · rename_i hty
                split at h
                · rename_i hagree
                  rw [Checked.pure_value] at h
                  cases h
                  refine Or.inr ⟨key, focus, hne, hfocus, hkey, ?_, hagree, (fun hd => nomatch hd),
                    rfl⟩
                  rw [hres]
                  simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hty
                  rw [hty]
                · exact Or.inl (recheck_ok h)
  · rename_i hnone
    left
    have hedit : s.sketch.edit s.app e = none := by
      cases hc : s.sketch.edit s.app e with
      | none => rfl
      | some c =>
        obtain ⟨old, hat⟩ := Sketch.edit_at hc
        exact (hnone old c hat hc).elim
    cases policy with
    | draft =>
      rw [Checked.pure_value] at h
      cases h
      exact ⟨hedit, rfl, rfl⟩
    | keepExact => cases h
    | recheck => cases h

/-- **An accepted `keepExact` feed below the root passed the focus and the part check**, and it
spliced exactly where the expanded edit agrees. A step of `kept-fill-reference`. Its consumer is
`kept_eq_certified` (`Laws/Program/FillSet.lean`). -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem feed_keepExact_ok {o : Oracle} {s : SourceSession} {e : Edit}
    {r : SourceSession × Edit.Step} (hne : e.path ≠ [])
    (h : (s.feed o .keepExact e).value = .ok r) :
    ∃ old c key focus, (Node.eff s.sketch.program).at_ e.path = some (.eff old) ∧
      s.sketch.edit s.app e = some c ∧ s.focusAt e.path = some focus ∧
      s.candidatePartKey e.path c = some key ∧ (run key).result = .ok focus.ty ∧
      (s.expandedEditAgrees c e = true → r = s.splice c e old (run key)) ∧
      (s.expandedEditAgrees c e = false → (s.recheck o .keepExact c e old).value = .ok r) := by
  unfold feed at h
  split at h
  · rename_i old c hat hedit
    split at h
    · rename_i h0
      exact absurd h0 hne
    · dsimp only at h
      split at h
      · cases h
      · rename_i focus hfocus
        split at h
        · cases h
        · rename_i key hkey
          rw [Checked.bind_value, Checked.ask_value] at h
          split at h
          · cases h
          · rename_i ty hres
            split at h
            · cases h
            · rename_i hty
              have hty' : ty = focus.ty := by
                simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hty
                exact hty
              refine ⟨old, c, key, focus, hat, hedit, hfocus, hkey, by rw [hres, hty'], ?_, ?_⟩
              · intro hagree
                rw [if_pos hagree, Checked.pure_value] at h
                cases h
                rfl
              · intro hagree
                rw [if_neg (by rw [hagree]; exact Bool.false_ne_true)] at h
                exact h
  · cases h

/-- **A `keepExact` feed below the root splices** where the focus is typed, the part keeps the
focus's type and the expanded edit agrees. A step of `kept-fill-reference`. Its consumer is
`kept_eq_certified`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem feed_keepExact_of {o : Oracle} {s : SourceSession} {e : Edit} {old : NativeEff}
    {c : Sketch} {key : CheckInput} {focus : Focus NativeOp} (hne : e.path ≠ [])
    (hat : (Node.eff s.sketch.program).at_ e.path = some (.eff old))
    (hedit : s.sketch.edit s.app e = some c) (hfocus : s.focusAt e.path = some focus)
    (hkey : s.candidatePartKey e.path c = some key) (hres : (run key).result = .ok focus.ty)
    (hagree : s.expandedEditAgrees c e = true) :
    (s.feed o .keepExact e).value = .ok (s.splice c e old (run key)) := by
  obtain ⟨i, rest, hpath⟩ := List.exists_cons_of_ne_nil hne
  unfold feed
  simp only [hat, hedit]
  split
  · rename_i h0
    rw [hpath] at h0
    cases h0
  · simp only [hfocus, hkey, Checked.bind_value, Checked.ask_value, hres, bne_self_eq_false,
      Bool.false_eq_true, ↓reduceIte, hagree, Checked.pure_value]

/-- **An accepted `keepExact` feed applies its edit**: the next sketch is the edited one. A step
of `pending-fill-publication`. Its consumer is `batch_keepExact_fills`
(`Laws/Program/FillSet.lean`). -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem feed_keepExact_sketch {o : Oracle} {s next : SourceSession} {e : Edit}
    {step : Edit.Step} (h : (s.feed o .keepExact e).value = .ok (next, step)) :
    s.sketch.edit s.app e = some next.sketch := by
  rcases feed_ok_cases h with ⟨-, hpol, -⟩ | ⟨old, c, -, hedit, hr | ⟨key, focus, -, -, -, -, -, -, hr⟩⟩
  · cases hpol
  · rw [hedit]
    obtain ⟨rfl, -⟩ := Prod.mk.inj hr
    rfl
  · rw [hedit]
    obtain ⟨rfl, -⟩ := Prod.mk.inj hr
    rfl

/-- **An accepted feed keeps a coherent session coherent.** The pointer of `source-feed-coherent`.
It is false at head (`FeedCounterexample.feed_coherent_refuted`): `SourceSession.splice` places
the part's table through `Table.atSource` with the candidate's ill-formed reference, which puts a
second root entry in place of the entry at the edited address, and a splice keeps the old root
entry where the edit adds or removes an ill-formed reference. The statement is the
specification. It holds once the feed splices only where neither the session's sketch nor the
candidate holds an ill-formed reference (the seat's receipt, option A). -/
@[semantics "initial-algebras-folds" (requirement := R14)]
proof_goal feed_coherent {o : Oracle} {policy : FeedPolicy} {s next : SourceSession}
    {e : Edit} {step : Edit.Step} (hc : s.Coherent)
    (h : (s.feed o policy e).value = .ok (next,step)) : next.Coherent

/-- **An accepted feed keeps the application and the edit, leaves the session where the edit does
not apply, and holds the edited sketch where it does.** Read off `feed_ok_cases`. The pointer of
`source-feed-edit`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem feed_keeps {o : Oracle} {policy : FeedPolicy} {s next : SourceSession}
    {e : Edit} {step : Edit.Step}
    (h : (s.feed o policy e).value = .ok (next,step)) :
    next.app = s.app ∧ step.edit = e ∧
      (s.sketch.edit s.app e = none → next = s) ∧
      (∀ candidate, s.sketch.edit s.app e = some candidate → next.sketch = candidate) := by
  rcases feed_ok_cases h with
    ⟨hnone, -, hr⟩ | ⟨old, c, -, hedit, hr | ⟨key, focus, -, -, -, -, -, -, hr⟩⟩
  · cases hr
    refine ⟨rfl, rfl, fun _ => rfl, fun c hc => ?_⟩
    rw [hnone] at hc
    cases hc
  · cases hr
    refine ⟨rfl, rfl, fun hn => ?_, fun c' hc' => ?_⟩
    · rw [hedit] at hn
      cases hn
    · rw [hedit] at hc'
      cases hc'
      rfl
  · cases hr
    refine ⟨rfl, rfl, fun hn => ?_, fun c' hc' => ?_⟩
    · rw [hedit] at hn
      cases hn
    · rw [hedit] at hc'
      cases hc'
      rfl

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
Reach: coherent source sessions whose sketch and candidate hold no ill-formed reference, every
edit, and certified oracles. The first form had no such premise and is false: on a sketch with
an ill-formed reference the draft refuses to splice, since its root is refused, while the
expansion's edit session splices (`FeedCounterexample.feed_draft_refuted`); and a candidate
with one spliced wrongly (`FeedCounterexample.feed_coherent_refuted`).
Consumer: replay_drafts_view and transport of source-session-coherent. R14. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
proof_goal feed_draft (o : Oracle) (s : SourceSession) (hc : s.Coherent) (e : Edit)
    (hfault : s.sketch.program.firstRefFault = none)
    (hcand : ∀ c, s.sketch.edit s.app e = some c → c.program.firstRefFault = none) :
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

/-- **A kept-exact feed below the root keeps the root's and the address's types, and splices
exactly where the expanded edit agrees.** The pointer of `source-feed-keep-exact`. The first
form said a splice shows `[e.path]` alone; a splice shows every address of the new subtree
(`FeedCounterexample.feed_keepExact_delta_refuted`), so the conjunct now names a splice. It is
false at head where the candidate holds an ill-formed reference
(`FeedCounterexample.feed_keepExact_refuted`), by the splice of `feed_coherent`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
proof_goal feed_keepExact {o : Oracle} {s next : SourceSession} {e : Edit} {step : Edit.Step}
    (hc : s.Coherent) (hne : e.path ≠ [])
    (h : (s.feed o .keepExact e).value = .ok (next,step)) :
    next.view.type = s.view.type ∧
      Table.typedAt next.table e.path = Table.typedAt s.table e.path ∧
      (s.expandedEditAgrees next.sketch e = true → ∃ shown, step.delta = .spliced shown) ∧
      (s.expandedEditAgrees next.sketch e = false → step.delta = .rechecked)

/-- **The root feed is exactly the module recheck route**, including its actual part trace: the
root holds the whole program, and every policy asks the module key there. The pointer of
`source-feed-root`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem feed_root (o : Oracle) (policy : FeedPolicy) (s : SourceSession)
    (e : Edit) (candidate : Sketch) (hp : e.path = [])
    (hedit : s.sketch.edit s.app e = some candidate) :
    s.feed o policy e = s.recheck o policy candidate e s.sketch.program := by
  unfold feed
  simp only [hp, hedit, Node.at_]

@[semantics "initial-algebras-folds" (requirement := R14)]
proof_goal feed_undo {o : Oracle} {s next : SourceSession} {a : List Nat} {q old : NativeEff}
    {candidate : Sketch} {step : Edit.Step} (hc : s.Coherent)
    (hat : (Node.eff s.sketch.program).at_ a = some (.eff old))
    (hfill : s.sketch.fillAt a q = some candidate)
    (hnext : (s.feed o .draft (.fill a q)).value = .ok (next,step)) :
    ∃ back, (next.feed o .draft (.fill a old)).value = .ok (s,back)

end SourceSession

/-- **An accepted document step**: the snapshot is current, the sole interpreter answered a fresh
state, and the next document holds that state's session after one more action. A step of
`source-document-step` and of `pending-fill-publication`. Its consumer is
`FillSet.publish_eq_materialize` (`Laws/Program/FillSet.lean`). -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Doc.step_ok {o : Check.Oracle} {d next : Doc} {at_ : Snap} {action : DocAction}
    {receipt : Receipt} (h : (d.step o at_ action).value = .ok (next, receipt)) :
    d.check at_ = .ok () ∧ ∃ fresh, (DocInternal.apply o d.runtime action).value = .ok fresh ∧
      next.origin = d.origin ∧ next.history = d.history ++ [action] ∧
      next.session = fresh.session ∧ receipt = fresh.receipt := by
  unfold Doc.step at h
  split at h
  · cases h
  · rename_i hcheck
    refine ⟨hcheck, ?_⟩
    dsimp only [Check.Checked.bind', Check.Checked.pure_value] at h
    split at h
    · cases h
    · rename_i fresh hfresh
      cases h
      exact ⟨fresh, hfresh, rfl, rfl, rfl, rfl⟩

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

/-! ## Counterexamples at head

`SourceSession.splice` places a part check's table through `Table.atSource` with the candidate's
first ill-formed reference. Where the candidate has one, `Table.atSource` replaces the head of
the part's table, the entry at the edited address, by a root entry. The spliced table then holds
two root entries and no entry at the edited address. A splice also keeps the old root entry,
which is wrong where the edit adds or removes an ill-formed reference.

The base below has no reference. Its filling `late` names the layer at `[1, 0]`, which follows
the site `[0, 0]` in program order (`RefFault.notBefore`). The expansion still expands the
reference, so the part check keeps the focus's type and both `draft` and `keepExact` splice.

Each statement below is a control, kernel-checked by evaluation (`decide`): it shows where a
planned goal stops at head. Its placement names the concept and no requirement. They will
fail to elaborate once the feed splices only inputs with no ill-formed reference, and then they
go. -/

namespace FeedCounterexample
open _root_.Effect4.Program.Check

/-- The literal program `7`. -/
def seven : NativeEff := .succeed (.lit (.nat 7))
/-- The literal program `1`. -/
def one : NativeEff := .succeed (.lit (.nat 1))
/-- A base with no layer reference: a layer at `[1, 0]`, after the edited address `[0]`. -/
def base : Sketch := ⟨.bind seven (.provideLayer (.effectDiscard one) false one), []⟩
/-- A filling of `[0]` whose reference targets the later layer. -/
def late : NativeEff := .provideLayer (.ref [1, 0]) false seven
/-- A filling of `[0]` with children, of the focus's type, with no reference. -/
def wide : NativeEff := .bind one seven
/-- The base with `late` at `[0]`: one ill-formed reference, at `[0, 0]`. -/
def faulty : Sketch := ⟨.bind late (.provideLayer (.effectDiscard one) false one), []⟩
/-- The faulty base with `7` at `[1, 1]`. -/
def faultyFilled : Sketch := ⟨.bind late (.provideLayer (.effectDiscard one) false seven), []⟩

/-- The session the base opens. -/
def opened : SourceSession := (SourceSession.open Oracle.uncached {} base).value
/-- The session the faulty base opens. -/
def faultyOpened : SourceSession := (SourceSession.open Oracle.uncached {} faulty).value

/-- The draft of `late` is accepted and its next session is incoherent. -/
def draftLate : Bool :=
  match (opened.feed Oracle.uncached .draft (.fill [0] late)).value with
  | .ok (next, _) => !decide (next.table = next.sketch.sourceTable next.app)
  | .error _ => false

/-- The kept-exact fill of `late` is accepted and loses the typed entry at `[0]`. -/
def keepLate : Bool :=
  match (opened.feed Oracle.uncached .keepExact (.fill [0] late)).value with
  | .ok (next, _) => !decide (Table.typedAt next.table [0] = Table.typedAt opened.table [0])
  | .error _ => false

/-- The kept-exact fill of `wide` splices its whole subtree, so its delta lists three addresses. -/
def keepWide : Bool :=
  match (opened.feed Oracle.uncached .keepExact (.fill [0] wide)).value with
  | .ok (next, step) => !decide (step.delta = .spliced [[0]]) &&
      opened.expandedEditAgrees next.sketch (.fill [0] wide)
  | .error _ => false

/-- A document that drafts `late` is incoherent. -/
def docLate : Bool :=
  match ((Doc.open_ ⟨{}, {}, base⟩).value.step Oracle.uncached (Doc.open_ ⟨{}, {}, base⟩).value.snap
      (.draft (.fill [0] late))).value with
  | .ok (d, _) => !decide (d.session.table = d.session.sketch.sourceTable d.session.app)
  | .error _ => false

/-- Replaying the draft of `late` shows a table that is not the source table. -/
def replayLate : Bool :=
  match replayDoc ⟨{}, {}, base⟩ [.draft (.fill [0] late)] with
  | .ok session => !decide (session.table = session.sketch.sourceTable {})
  | .error _ => false

/-- From the faulty base, drafting `7` at `[0]` and then putting `late` back does not restore the
session: the second feed splices a candidate with an ill-formed reference. -/
def undoFaulty : Bool :=
  match (faultyOpened.feed Oracle.uncached .draft (.fill [0] seven)).value with
  | .ok (next, _) =>
    match (next.feed Oracle.uncached .draft (.fill [0] late)).value with
    | .ok (back, _) => !decide (back.table = faultyOpened.table)
    | .error _ => false
  | .error _ => false

/-- On the faulty base, a draft away from the reference rechecks: its root is refused. -/
def draftFaultyRechecks : Bool :=
  match (faultyOpened.feed Oracle.uncached .draft (.fill [1, 1] seven)).value with
  | .ok (_, step) => decide (step.delta = .rechecked)
  | .error _ => false

set_option maxRecDepth 100000 in
/-- The evaluation of the seven verdicts. -/
theorem verdicts : draftLate = true ∧ keepLate = true ∧ keepWide = true ∧ docLate = true ∧
    replayLate = true ∧ undoFaulty = true ∧ draftFaultyRechecks = true := by
  decide

end FeedCounterexample

open _root_.Effect4.Program.Check in
/-- **`SourceSession.feed_coherent` is false at head**: the draft of `late` from the coherent
session of `FeedCounterexample.base` answers an incoherent session. A control of the claim
`source-feed-coherent`; its register entry is proposed in the seat's receipt. -/
@[semantics "initial-algebras-folds"]
theorem FeedCounterexample.feed_coherent_refuted :
    ¬ ∀ (o : Oracle) (policy : FeedPolicy) (s next : SourceSession) (e : Edit) (step : Edit.Step),
      s.Coherent → (s.feed o policy e).value = .ok (next, step) → next.Coherent := by
  intro h
  have hv := FeedCounterexample.verdicts.1
  unfold FeedCounterexample.draftLate at hv
  split at hv
  · rename_i next step heq
    have hcoh := h _ _ _ _ _ _ (SourceSession.open_coherent _ _ _) heq
    rw [Bool.not_eq_true', decide_eq_false_iff_not] at hv
    exact hv hcoh
  · cases hv

/-- **`Doc.coherent` is false at head**, and with it `SourceSession.reached_view`, the pointer of
`source-session-coherent`: a document that drafts `late` holds an incoherent session. A control
of the claims `source-document-coherent` and `source-session-coherent`. -/
@[semantics "initial-algebras-folds"]
theorem FeedCounterexample.doc_coherent_refuted : ¬ ∀ d : Doc, d.session.Coherent := by
  intro h
  have hv := FeedCounterexample.verdicts.2.2.2.1
  unfold FeedCounterexample.docLate at hv
  split at hv
  · rename_i d r heq
    rw [Bool.not_eq_true', decide_eq_false_iff_not] at hv
    exact hv (h d)
  · cases hv

/-- **`SourceSession.replay_drafts_view` is false at head**: the replay of the draft of `late`
shows a table that is not the source table. A control of the claim
`source-session-draft-transport`. -/
@[semantics "initial-algebras-folds"]
theorem FeedCounterexample.replay_drafts_view_refuted :
    ¬ ∀ (app : SigApp) (initial : Sketch) (edits : List Edit) (id : DocId),
      ∃ session, replayDoc ⟨id,app,initial⟩ (edits.map DocAction.draft) = .ok session ∧
        session.app = app ∧
        session.sketch = edits.foldl (fun s e => (s.edit app e).getD s) initial ∧
        session.view.table = session.sketch.sourceTable app ∧
        session.view.refusals = session.sketch.sourceRefusals app ∧
        session.view.type = (session.sketch.sourceCheck app).toOption := by
  intro h
  obtain ⟨session, hreplay, -, -, htable, -, -⟩ :=
    h {} FeedCounterexample.base [.fill [0] FeedCounterexample.late] {}
  have hv := FeedCounterexample.verdicts.2.2.2.2.1
  unfold FeedCounterexample.replayLate at hv
  simp only [List.map_cons, List.map_nil] at hreplay
  rw [hreplay] at hv
  rw [Bool.not_eq_true', decide_eq_false_iff_not] at hv
  exact hv htable

open _root_.Effect4.Program.Check in
/-- **`SourceSession.feed_undo` is false at head**: from the coherent session of the faulty
base, drafting `7` at `[0]` and then putting `late` back answers another session. Its implicit
arguments are explicit here. A control of the claim `source-session-undo`, which the base
`774ddc3d7` proved over the feed of that time. -/
@[semantics "initial-algebras-folds"]
theorem FeedCounterexample.feed_undo_refuted :
    ¬ ∀ (o : Oracle) (s next : SourceSession) (a : List Nat) (q old : NativeEff)
      (candidate : Sketch) (step : Edit.Step), s.Coherent →
      (Node.eff s.sketch.program).at_ a = some (.eff old) →
      s.sketch.fillAt a q = some candidate →
      (s.feed o .draft (.fill a q)).value = .ok (next, step) →
      ∃ back, (next.feed o .draft (.fill a old)).value = .ok (s, back) := by
  intro h
  have hv := FeedCounterexample.verdicts.2.2.2.2.2.1
  unfold FeedCounterexample.undoFaulty at hv
  split at hv
  · rename_i next step heq
    split at hv
    · rename_i back bstep heq2
      have hfill : FeedCounterexample.faulty.fillAt [0] FeedCounterexample.seven =
          some ⟨.bind FeedCounterexample.seven (.provideLayer (.effectDiscard FeedCounterexample.one)
            false FeedCounterexample.one), []⟩ := rfl
      have hat : (Node.eff FeedCounterexample.faulty.program).at_ [0] =
          some (.eff FeedCounterexample.late) := rfl
      obtain ⟨back', hback⟩ := h Oracle.uncached FeedCounterexample.faultyOpened next [0]
        FeedCounterexample.seven FeedCounterexample.late _ step
        (SourceSession.open_coherent _ _ _) hat hfill heq
      rw [hback] at heq2
      cases heq2
      rw [Bool.not_eq_true', decide_eq_false_iff_not] at hv
      exact hv rfl
    · cases hv
  · cases hv

open _root_.Effect4.Program.Check in
/-- **The first form of `SourceSession.feed_draft`, with no premise on ill-formed references, is
false**: on the faulty base, a draft of `7` at `[1, 1]`, away from the reference, rechecks since
the root is refused, while the expansion's edit session splices. A control of the claim
`source-feed-draft`. -/
@[semantics "initial-algebras-folds"]
theorem FeedCounterexample.feed_draft_refuted :
    ¬ ∀ (o : Oracle) (s : SourceSession) (_ : s.Coherent) (e : Edit),
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
           next.table = Table.atSource candidate.sites candidate.program.firstRefFault
             reference.1.table ∧
             step.delta = reference.2.atSource candidate.sites) := by
  intro h
  obtain ⟨next, step, hfeed, -, -, hmatch⟩ := h Oracle.uncached FeedCounterexample.faultyOpened
    (SourceSession.open_coherent _ _ _) (.fill [1, 1] FeedCounterexample.seven)
  have hedit : FeedCounterexample.faultyOpened.sketch.edit FeedCounterexample.faultyOpened.app
      (.fill [1, 1] FeedCounterexample.seven) = some FeedCounterexample.faultyFilled := rfl
  rw [hedit] at hmatch
  dsimp only at hmatch
  obtain ⟨-, -, -, hdelta⟩ := hmatch
  have hv := FeedCounterexample.verdicts.2.2.2.2.2.2
  unfold FeedCounterexample.draftFaultyRechecks at hv
  rw [hfeed] at hv
  rw [of_decide_eq_true hv] at hdelta
  exact absurd hdelta (by decide)

open _root_.Effect4.Program.Check in
/-- **The first form of `SourceSession.feed_keepExact` was false for any filling with
children**: the kept fill of `wide` splices the whole new subtree, so its delta lists every
address of the subtree, not the edited address alone. A control of the claim
`source-feed-keep-exact`. -/
@[semantics "initial-algebras-folds"]
theorem FeedCounterexample.feed_keepExact_delta_refuted :
    ¬ ∀ (o : Oracle) (s next : SourceSession) (e : Edit) (step : Edit.Step),
      s.Coherent → e.path ≠ [] → (s.feed o .keepExact e).value = .ok (next, step) →
      (s.expandedEditAgrees next.sketch e = true → step.delta = .spliced [e.path]) := by
  intro h
  have hv := FeedCounterexample.verdicts.2.2.1
  unfold FeedCounterexample.keepWide at hv
  split at hv
  · rename_i next step heq
    rw [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hv
    exact hv.1 (h _ _ _ (.fill [0] FeedCounterexample.wide) _ (SourceSession.open_coherent _ _ _)
      (List.cons_ne_nil 0 []) heq hv.2)
  · cases hv

open _root_.Effect4.Program.Check in
/-- **`SourceSession.feed_keepExact` is false at head**: the kept fill of `late` loses the typed
entry at the edited address. A control of the claim `source-feed-keep-exact`. -/
@[semantics "initial-algebras-folds"]
theorem FeedCounterexample.feed_keepExact_refuted :
    ¬ ∀ (o : Oracle) (s next : SourceSession) (e : Edit) (step : Edit.Step),
      s.Coherent → e.path ≠ [] → (s.feed o .keepExact e).value = .ok (next, step) →
      Table.typedAt next.table e.path = Table.typedAt s.table e.path := by
  intro h
  have hv := FeedCounterexample.verdicts.2.1
  unfold FeedCounterexample.keepLate at hv
  split at hv
  · rename_i next step heq
    rw [Bool.not_eq_true', decide_eq_false_iff_not] at hv
    exact hv (h _ _ _ (.fill [0] FeedCounterexample.late) _ (SourceSession.open_coherent _ _ _)
      (List.cons_ne_nil 0 []) heq)
  · cases hv

end Effect4.Program
