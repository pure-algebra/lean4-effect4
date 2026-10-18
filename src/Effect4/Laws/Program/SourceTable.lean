import Effect4.Program.Typing.SourceDocument
import Effect4.Laws.Program.CheckAgreement
import Effect4.Program.Typing.SourceSession
import Effect4.Laws.Program.ExpansionAddresses
import Effect4.Laws.Program.Edit
import Effect4.Laws.Program.AddressMove
import Effect4.Laws.Program.Typing.SigData
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
| `SourceSession.feed_draft` | a draft whose sketch and candidate hold no ill-formed reference is the expansion's edit session at the source's addresses | `draft_conditions_of_reference`, `draft_reference_spliced` |
| `SourceSession.reached_view` | every sealed document shows its source table, refusals, and root type | `Doc.coherent`, modulo the goal `feed_coherent` |
| `SourceSession.replay_drafts_view` | every old application, sketch, and edit list retains its exact observation through canonical draft replay | the replay fold, modulo `feed_coherent` |
| `SourceSession.feed_undo` | an edit, then the edit that puts back the old sub-program as written, restores the session | `EditSession.Coherent.ext`, modulo `feed_coherent` |

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
  The proof rests on `Doc.coherent`, which rests on the planned goal `feed_coherent`.
  That goal is false at head: a kept-exact omission at a refused root keeps the refused root
  entry (`FeedCounterexample.keep_omit_refused`). `feed_coherent_of_faultFree` proves it where
  the candidate holds no ill-formed reference and a kept-exact splice stands at a typed root.
  `SourceSession.replay_drafts_view` retains every old application, initial sketch, and edit list through canonical replay.
  It rests on `feed_coherent` too.
  Neither claim establishes reference splicing, execution, progress, or cost.
  Consumer: the session tool.
- Every other statement is a step of these two, and names its consumer.
-/

set_option autoImplicit false

namespace Effect4.Program
open Conform.Effect4.Typing (HasTy effTy_sound check_complete)

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

/-! ## D3: a fill below the root keeps the signature of every address

Moved here from `Laws/Program/FillSet.lean`, where D1–D9 are listed: the feed's splice law reads
it too. -/

/-- An edit inside a spine of bodies keeps each body's signature. -/
theorem bodyAt_sig_replaceAt (sig : Signature NativeOp) (q : NativeEff) :
    ∀ (r : List Nat) (decls : List DefDecl) (bodies bodies' : Effs NativeOp),
      (Node.effs bodies).replaceAt r (.eff q) = some (.effs bodies') →
      ∀ path, (Part.bodyAt sig decls bodies' path).map (·.1.sig) =
        (Part.bodyAt sig decls bodies path).map (·.1.sig)
  | [], _, _, _, h, _ => by
    simp only [Node.replaceAt] at h
    split at h <;> cases h
  | 0 :: _, _, .nil, _, h, _ => by
    simp only [Node.replaceAt, Node.child, Option.bind_none, reduceCtorEq] at h
  | 0 :: _, decls, .cons b bs, _, h, path => by
    obtain ⟨b', -, rfl⟩ := Node.replaceAt_effs_head h
    match decls, path with
    | [], _ => rfl
    | _ :: _, [] => rfl
    | _ :: _, 0 :: _ => rfl
    | _ :: _, 1 :: _ => rfl
    | _ :: _, (_ + 2) :: _ => rfl
  | 1 :: _, _, .nil, _, h, _ => by
    simp only [Node.replaceAt, Node.child, Option.bind_none, reduceCtorEq] at h
  | 1 :: r, decls, .cons b bs, _, h, path => by
    obtain ⟨bs', hr, rfl⟩ := Node.replaceAt_effs_tail h
    match decls, path with
    | [], _ => rfl
    | _ :: _, [] => rfl
    | _ :: _, 0 :: _ => rfl
    | _ :: ds, 1 :: rest => exact bodyAt_sig_replaceAt sig q r ds bs bs' hr rest
    | _ :: _, (_ + 2) :: _ => rfl
  | (_ + 2) :: _, _, .nil, _, h, _ => by
    simp only [Node.replaceAt, Node.child, Option.bind_none, reduceCtorEq] at h
  | (_ + 2) :: _, _, .cons _ _, _, h, _ => by
    simp only [Node.replaceAt, Node.child, Option.bind_none, reduceCtorEq] at h

/-- A replacement below the root keeps the signature of every part. -/
theorem partAt_sig_replaceAt {sig : Signature NativeOp} {p p' q : NativeEff} {i : Nat}
    {rest : List Nat} (h : (Node.eff p).replaceAt (i :: rest) (.eff q) = some (.eff p'))
    (path : List Nat) :
    (p'.partAt sig [] path).map (·.1.sig) = (p.partAt sig [] path).map (·.1.sig) := by
  cases hb : p.isBlock
  · have hb' : p'.isBlock = false := by
      have := Node.replaceAt_cons_isBlock h
      simp only [Node.isBlock] at this
      rw [this, hb]
    rw [Eff.partAt_plain hb, Eff.partAt_plain hb']
    rfl
  · obtain ⟨decls, bodies, main, layers, rfl⟩ := Eff.eq_defs_of_isBlock hb
    match i, h with
    | 0, h =>
      obtain ⟨bodies', hr, rfl⟩ := Node.replaceAt_defs_body h
      unfold Eff.partAt
      match path, layers with
      | [], _ => rfl
      | 0 :: r, _ => exact bodyAt_sig_replaceAt _ q rest decls bodies bodies' hr r
      | 1 :: _, _ => rfl
      | 2 :: _, .nil => rfl
      | 2 :: _, .cons _ _ => rfl
      | (_ + 3) :: _, _ => rfl
    | 1, h =>
      obtain ⟨main', -, rfl⟩ := Node.replaceAt_defs_main h
      unfold Eff.partAt
      match path, layers with
      | [], _ => rfl
      | 0 :: _, _ => rfl
      | 1 :: _, _ => rfl
      | 2 :: _, .nil => rfl
      | 2 :: _, .cons _ _ => rfl
      | (_ + 3) :: _, _ => rfl
    | 2, h =>
      rw [defs_replaceAt_layers] at h
      cases hr : (Node.layers layers).replaceAt rest (.eff q) with
      | none =>
        rw [hr] at h
        cases h
      | some n =>
        rw [hr, Option.bind_some] at h
        match n, h with
        | .layers ls', h =>
          simp only [Option.some.injEq, Node.eff.injEq] at h
          subst h
          cases layers with
          | nil =>
            cases rest with
            | nil =>
              simp only [Node.replaceAt] at hr
              split at hr <;> cases hr
            | cons j t =>
              simp only [Node.replaceAt, Node.child, Option.bind_none, reduceCtorEq] at hr
          | cons hd tl =>
            obtain ⟨h', t', rfl⟩ := Node.replaceAt_layers_cons hr
            unfold Eff.partAt
            match path with
            | [] => rfl
            | 0 :: _ => rfl
            | 1 :: _ => rfl
            | 2 :: _ => rfl
            | (_ + 3) :: _ => rfl
    | k + 3, h =>
      simp only [Node.replaceAt, Node.child, Option.bind_none, reduceCtorEq] at h

/-- **D3: a fill below the root keeps the signature of every address.**

Placement:
1. Concept: `initial-algebras-folds`; property: `typed-replacement`.
2. Question: step D3 of the proposed claim `workspace-fill-agreement` (role compatibility);
   consumers: `fills_compose` (D5) and `SourceSession.splice_coherent`.
3. Reach: any sketch `s`, application `app`, non-empty path `p ≠ []`, filling `q`, and target
   address `path`.
4. What it does not establish: root replacement (`p = []`), which can change `defs` declarations.
5. Unlocks: R14 (`workspace-fill-agreement`). -/
theorem sigAt_fillAt {s s' : Sketch} {app : SigApp} {p : List Nat} {q : NativeEff}
    (hp : p ≠ []) (h : s.fillAt p q = some s') (path : List Nat) :
    s'.sigAt app path = s.sigAt app path := by
  obtain ⟨p', hrep, rfl⟩ := Sketch.fillAt_some h
  obtain ⟨i, rest, rfl⟩ := List.exists_cons_of_ne_nil hp
  unfold Sketch.sigAt
  dsimp only
  rw [partAt_sig_replaceAt hrep path]

/-! ## A splice at the source's addresses

Where neither the sketch nor the candidate holds an ill-formed reference, the source table is the
expansion's table with the copies' entries dropped (`Sketch.sourceTable_eq_filter`). An edit's
subtree is one contiguous block of the expansion's addresses (`Node.addresses_split`), the
edited address is below no reference site (`belowSite_at_eff`), and the edit keeps the sites
outside its subtree (`belowSite_replaceAt`). So the filter commutes with the splice
(`Table.splice_filter`). Each statement here is a step of `source-feed-coherent`, and its
consumer is `SourceSession.splice_coherent`. -/

/-- An address below a child is below the child's address exactly where its rest is. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Table.under_cons_cons (i : Nat) (a b : List Nat) :
    Table.under (i :: a) (i :: b) = Table.under a b := by
  unfold Table.under
  apply Bool.eq_iff_iff.mpr
  rw [List.isPrefixOf_iff_prefix, List.isPrefixOf_iff_prefix, List.cons_prefix_cons]
  exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩

/-- A sibling's address is not below another child's. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Table.under_cons_ne (i j : Nat) (a b : List Nat) (h : j ≠ i) :
    Table.under (i :: a) (j :: b) = false := by
  have := Table.under_sibling_false [] a b h
  simpa only [List.nil_append] using this

/-- **The addresses below an address are one contiguous block**: a node's addresses are those
before the subtree, the subtree's addresses below the address, and those after it. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Node.addresses_split {Op : Type} :
    ∀ (path : List Nat) (n m : Node Op), n.at_ path = some m →
      ∃ A C, Node.addresses n = A ++ (Node.addresses m).map (path ++ ·) ++ C ∧
        (∀ a ∈ A, Table.under path a = false) ∧ (∀ a ∈ C, Table.under path a = false)
  | [], n, m, h => by
    cases h
    refine ⟨[], [], ?_, (fun _ h => nomatch h), (fun _ h => nomatch h)⟩
    simp only [List.nil_append, List.append_nil, List.map_id']
  | i :: rest, n, m, h => by
    cases hc : n.child i with
    | none =>
      simp only [Node.at_, hc, Option.bind_none] at h
      cases h
    | some c =>
      simp only [Node.at_, hc, Option.bind_some] at h
      obtain ⟨A', C', hsplit, hA', hC'⟩ := Node.addresses_split rest c m h
      have hlift : ∀ L : List (List Nat), (∀ a ∈ L, Table.under rest a = false) →
          ∀ a ∈ L.map (i :: ·), Table.under (i :: rest) a = false := by
        intro L hL a ha
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
        rw [Table.under_cons_cons]
        exact hL b hb
      have hother : ∀ j, j ≠ i → ∀ a ∈ n.childAddresses j, Table.under (i :: rest) a = false := by
        intro j hj a ha
        unfold Node.childAddresses at ha
        split at ha
        · obtain ⟨b, -, rfl⟩ := List.mem_map.mp ha
          exact Table.under_cons_ne i j rest b hj
        · cases ha
      have hci : n.childAddresses i =
          A'.map (i :: ·) ++ (Node.addresses m).map ((i :: rest) ++ ·) ++ C'.map (i :: ·) := by
        unfold Node.childAddresses
        simp only [hc]
        rw [hsplit]
        simp only [List.map_append, List.map_map]
        rfl
      rw [Node.addresses_eq_cons]
      match i, hci, hother with
      | 0, hci, hother =>
        refine ⟨[] :: A'.map (0 :: ·),
          C'.map (0 :: ·) ++ (n.childAddresses 1 ++ n.childAddresses 2), ?_, ?_, ?_⟩
        · rw [hci]
          simp only [List.cons_append, List.append_assoc]
        · intro a ha
          rcases List.mem_cons.mp ha with rfl | ha
          · rfl
          · exact hlift A' hA' a ha
        · intro a ha
          rcases List.mem_append.mp ha with ha | ha
          · exact hlift C' hC' a ha
          · rcases List.mem_append.mp ha with ha | ha
            · exact hother 1 (by decide) a ha
            · exact hother 2 (by decide) a ha
      | 1, hci, hother =>
        refine ⟨[] :: (n.childAddresses 0 ++ A'.map (1 :: ·)),
          C'.map (1 :: ·) ++ n.childAddresses 2, ?_, ?_, ?_⟩
        · rw [hci]
          simp only [List.cons_append, List.append_assoc]
        · intro a ha
          rcases List.mem_cons.mp ha with rfl | ha
          · rfl
          · rcases List.mem_append.mp ha with ha | ha
            · exact hother 0 (by decide) a ha
            · exact hlift A' hA' a ha
        · intro a ha
          rcases List.mem_append.mp ha with ha | ha
          · exact hlift C' hC' a ha
          · exact hother 2 (by decide) a ha
      | 2, hci, hother =>
        refine ⟨[] :: (n.childAddresses 0 ++ (n.childAddresses 1 ++ A'.map (2 :: ·))),
          C'.map (2 :: ·), ?_, ?_, ?_⟩
        · rw [hci]
          simp only [List.cons_append, List.append_assoc]
        · intro a ha
          rcases List.mem_cons.mp ha with rfl | ha
          · rfl
          · rcases List.mem_append.mp ha with ha | ha
            · exact hother 0 (by decide) a ha
            · rcases List.mem_append.mp ha with ha | ha
              · exact hother 1 (by decide) a ha
              · exact hlift A' hA' a ha
        · exact hlift C' hC'
      | k + 3, _, _ =>
        rw [Node.child_add_three] at hc
        cases hc

/-- **A filter commutes with a splice of a contiguous block**, where the block's head is kept
and the two filters agree outside the block. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Table.splice_filter {a : List Nat} {A B C P : List Table.Entry}
    {g g' : Table.Entry → Bool}
    (hA : ∀ e ∈ A, Table.under a e.path = false) (hC : ∀ e ∈ C, Table.under a e.path = false)
    (hB : ∀ e ∈ B, Table.under a e.path = true) {b : Table.Entry} (hb : b ∈ B) (hgb : g b = true)
    (hagree : ∀ e, Table.under a e.path = false → g' e = g e) :
    Table.splice ((A ++ B ++ C).filter g) a (P.filter g') = (A ++ P ++ C).filter g' := by
  have hfA : A.filter g' = A.filter g := List.filter_congr fun e he => hagree e (hA e he)
  have hfC : C.filter g' = C.filter g := List.filter_congr fun e he => hagree e (hC e he)
  rw [List.filter_append, List.filter_append, List.filter_append, List.filter_append, hfA, hfC,
    List.append_assoc, List.append_assoc]
  rw [Table.splice_three (fun e he => hA e (List.mem_filter.mp he).1)
    ⟨b, List.mem_filter.mpr ⟨hb, hgb⟩, hB b hb⟩ (fun e he => hC e (List.mem_filter.mp he).1),
    Table.splice_all_under (fun e he => hB e (List.mem_filter.mp he).1)]

/-- **With no ill-formed reference, the source table is the expansion's table with the copies'
entries dropped.** -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Sketch.sourceTable_eq_filter (s : Sketch) (app : SigApp)
    (h : s.program.firstRefFault = none) :
    s.sourceTable app = (s.expand.table app).filter (fun e => !Table.belowSite s.sites e.path) := by
  rw [← Sketch.sourceAnnotate_eq_sourceTable]
  unfold Sketch.sourceAnnotate Table.atSource
  rw [h, Sketch.annotate_eq_table]

/-- A reference site is never strictly above a node: a reference is a leaf. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem at_below_ref_none {n : Node NativeOp} {site path : List Nat} {t : List Nat}
    (hsite : n.at_ site = some (.layer (.ref t))) (hp : Path.properPrefix site path = true) :
    n.at_ path = none := by
  obtain ⟨r, hr, rfl⟩ := (Path.properPrefix_eq_true_iff site path).mp hp
  obtain ⟨i, r', rfl⟩ := List.exists_cons_of_ne_nil hr
  rw [Node.at_append, hsite, Option.bind_some, Node.at_ref_cons]

/-- A replacement at a program node keeps a reference site that an address outside the edited
subtree stands strictly below. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem at_site_replaceAt {n n' r : Node NativeOp} {path site b t : List Nat} {old : NativeEff}
    (hrep : n.replaceAt path r = some n') (hold : n.at_ path = some (.eff old))
    (hsite : n.at_ site = some (.layer (.ref t))) (hpre : Path.properPrefix site b = true)
    (hb : Table.under path b = false) : n'.at_ site = some (.layer (.ref t)) := by
  rcases Path.prefix_cases site path with ⟨r0, rfl⟩ | ⟨i, r0, rfl⟩ |
      ⟨c, k, l, r1, r2, hkl, rfl, rfl⟩
  · obtain ⟨r, -, rfl⟩ := (Path.properPrefix_eq_true_iff _ b).mp hpre
    have hu := Table.under_append path (r0 ++ r)
    rw [← List.append_assoc, hb] at hu
    cases hu
  · have hnone := at_below_ref_none hsite
      ((Path.properPrefix_eq_true_iff site (site ++ i :: r0)).mpr ⟨i :: r0, List.cons_ne_nil _ _, rfl⟩)
    rw [hold] at hnone
    cases hnone
  · rw [Node.at_replaceAt_disjoint c r2 r1 hrep hkl]
    exact hsite

/-- **An edit keeps whether an address outside its subtree is strictly below a reference site.** -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem belowSite_replaceAt {p p' x old : NativeEff} {path b : List Nat}
    (hrep : (Node.eff p).replaceAt path (.eff x) = some (.eff p'))
    (hold : (Node.eff p).at_ path = some (.eff old)) (hb : Table.under path b = false) :
    Table.belowSite ((p'.refSites []).map (·.1)) b =
      Table.belowSite ((p.refSites []).map (·.1)) b := by
  have hback : (Node.eff p').replaceAt path (.eff old) = some (.eff p) :=
    (Node.replaceAt_spec hrep).2.2 _ hold
  have hnew : (Node.eff p').at_ path = some (.eff x) := (Node.replaceAt_spec hrep).1
  unfold Table.belowSite
  rw [List.any_map, List.any_map]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, Function.comp_apply]
  constructor
  · rintro ⟨y, hy, hpre⟩
    have hat' := at_site_replaceAt hback hnew (at_of_mem_refSites hy) hpre hb
    exact ⟨(y.1, y.2), mem_refSites_of_at hat', hpre⟩
  · rintro ⟨y, hy, hpre⟩
    have hat' := at_site_replaceAt hrep hold (at_of_mem_refSites hy) hpre hb
    exact ⟨(y.1, y.2), mem_refSites_of_at hat', hpre⟩

/-- **A program node's address is strictly below no reference site.** -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem belowSite_at_eff {p old : NativeEff} {path : List Nat}
    (hold : (Node.eff p).at_ path = some (.eff old)) :
    Table.belowSite ((p.refSites []).map (·.1)) path = false := by
  unfold Table.belowSite
  rw [List.any_map]
  cases hany : (p.refSites []).any (fun y => Path.properPrefix y.1 path) with
  | false => exact hany
  | true =>
    obtain ⟨y, hy, hpre⟩ := List.any_eq_true.mp hany
    have hnone := at_below_ref_none (at_of_mem_refSites hy) hpre
    rw [hold] at hnone
    cases hnone

/-- The first entry at the root of a splice below the root is the old table's first entry. A step
of `source-feed-keep-exact`. Its consumer is `SourceSession.feed_keepExact_of_faultFree`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Table.typedAt_splice_root {x : Table.Entry} {rest sub : List Table.Entry} {a : List Nat}
    (hx : x.path = []) (ha : a ≠ []) :
    Table.typedAt (Table.splice (x :: rest) a sub) [] = Table.typedAt (x :: rest) [] := by
  have hxa : Table.under a x.path = false := by
    rw [hx]
    obtain ⟨i, r, rfl⟩ := List.exists_cons_of_ne_nil ha
    rfl
  have hsplit : Table.splice (x :: rest) a sub = x :: Table.splice rest a sub := by
    have h := Table.splice_append_out_left (X := [x]) (Y := rest) (sub := sub) (a := a)
      (fun e he => by
        rw [List.mem_singleton.mp he]
        exact hxa)
    simpa only [List.singleton_append] using h
  rw [hsplit]
  unfold Table.typedAt
  simp only [List.find?_cons, hx, decide_true]

/-- In a splice whose new segment starts at the address, the first entry at the address is the
segment's head. A step of `source-feed-keep-exact`. Its consumer is
`SourceSession.feed_keepExact_of_faultFree`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Table.typedAt_splice_at {old sub : List Table.Entry} {x : Table.Entry} {a : List Nat}
    (hx : x.path = a) :
    Table.typedAt (Table.splice old a (x :: sub)) a = Table.typedAt [x] a := by
  unfold Table.typedAt Table.splice
  have hnone : (old.takeWhile fun e => !Table.under a e.path).find?
      (fun e => decide (e.path = a)) = none := by
    rw [List.find?_eq_none]
    intro e he hea
    have hu : (!Table.under a e.path) = true := List.all_eq_true.mp List.all_takeWhile e he
    rw [decide_eq_true_eq] at hea
    rw [hea, Table.under_self] at hu
    cases hu
  rw [List.append_assoc, List.find?_append, hnone, Option.none_or, List.cons_append,
    List.find?_cons, List.find?_cons, hx, decide_eq_true (rfl : a = a)]

/-- The candidate's program is the old program with the edited address replaced. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Sketch.edit_replaceAt {s c : Sketch} {app : SigApp} {e : Edit} (h : s.edit app e = some c) :
    ∃ x, (Node.eff s.program).replaceAt e.path (.eff x) = some (.eff c.program) := by
  cases e with
  | fill a q =>
    obtain ⟨p', hrep, rfl⟩ := Sketch.fillAt_some h
    exact ⟨q, hrep⟩
  | omitAt a row =>
    obtain ⟨p', hrep, rfl⟩ := Sketch.fillAt_some h
    exact ⟨_, hrep⟩

/-- **An edit applies wherever a program stands**: the replacement at an address of a program
exists (`Node.replaceAt_eff`). A step of `source-feed-draft`. Its consumer is
`SourceSession.feed_draft`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Sketch.edit_of_at {s : Sketch} {app : SigApp} {e : Edit} {old : NativeEff}
    (hat : (Node.eff s.program).at_ e.path = some (.eff old)) : ∃ c, s.edit app e = some c := by
  cases e with
  | fill a q =>
    obtain ⟨p', hrep⟩ := Node.replaceAt_eff q hat
    exact ⟨_, Sketch.fillAt_of_replaceAt hrep⟩
  | omitAt a row =>
    obtain ⟨p', hrep⟩ := Node.replaceAt_eff (Sketch.hole app s.holes.length) hat
    exact ⟨_, Sketch.fillAt_of_replaceAt (s := { s with holes := s.holes ++ [row] }) hrep⟩

/-- **A filling's part signature at a focus below the root is the base's signature there**: the
filling keeps the part that holds the address (`partAt_sig_replaceAt`). A step of
`source-feed-coherent` and of `source-feed-draft`. Its consumers are
`SourceSession.splice_coherent` and `SourceSession.draft_conditions_of_reference`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Sketch.sigData_fillAt {s0 c : Sketch} {app : SigApp} {a : List Nat} {q' : NativeEff}
    {f : Focus NativeOp} (hne : a ≠ []) (hfill : s0.fillAt a q' = some c)
    (hf : s0.focusAt app a = some f) :
    (sketchSigData c app a).signature = s0.sigAt app a := by
  obtain ⟨i, rest, hpath⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨p', hrep, hcx⟩ := Sketch.fillAt_some hfill
  have hpart0 : (s0.program.partAt (app.withHoles s0.holes).signature [] a).isSome = true := by
    have hfp : programFocusAt (app.withHoles s0.holes).signature [] s0.program a = some f := by
      rw [hpath] at hf ⊢
      exact hf
    unfold programFocusAt at hfp
    obtain ⟨pr, hpr, -⟩ := Option.bind_eq_some_iff.mp hfp
    rw [hpr]
    rfl
  rw [sketchSigData_signature]
  · exact sigAt_fillAt hne hfill a
  · subst hcx
    rw [hpath] at hrep hpart0 ⊢
    have hpart' := partAt_sig_replaceAt (sig := (app.withHoles s0.holes).signature) hrep (i :: rest)
    rw [← Option.isSome_map (f := fun pr : Part NativeOp × List Nat => pr.1.sig)]
    show ((p'.partAt (app.withHoles s0.holes).signature [] (i :: rest)).map _).isSome = _
    rw [hpart', Option.isSome_map]
    exact hpart0

/-- **The checker's type does not read the path**: a type at one path is the type at every path
(`check_complete`). A step of `source-feed-draft`. Its consumers are
`SourceSession.draft_conditions_of_reference` and `SourceSession.draft_reference_spliced`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem check_ok_path {sig : Signature NativeOp} {env : TyEnv} {p : List Nat} {q : NativeEff}
    {t : EffTy} (h : Checker.check sig env p q = .ok t) (p' : List Nat) :
    Checker.check sig env p' q = .ok t :=
  check_complete _ _ _ _ (effTy_sound _ _ _ _ (effTy_of_check h)) p'

/-- **The table at a node stands at the node's addresses**, below its own address. A step of
`source-feed-draft`. Its consumer is `Check.placed_paths`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem tableAt_paths {Op : Type} (sig : Signature Op) (ctx : Option NodeEnv) (n : Node Op)
    (a : List Nat) : (tableAt sig ctx n a).map (·.path) = (Node.addresses n).map (a ++ ·) := by
  unfold tableAt
  rw [List.map_map]
  rfl

/-- **A part check's answer is the checker's at the part's signature.** A step of
`source-feed-coherent` and of `source-feed-draft`. Its consumers are
`SourceSession.splice_coherent`, `SourceSession.feed_keepExact_of_faultFree` and
`SourceSession.draft_conditions_of_reference`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Check.run_part_result (d : SigData) (env : TyEnv) (q : NativeEff) :
    (run (.part d env q)).result = Checker.check d.signature env [] q := by
  show (Annotate.check _ _ [] q).2 = _
  rw [Annotate.check_eq]

/-- **A placed part check's table stands at the sub-program's addresses**, below the edited
address. A step of `source-feed-draft`. Its consumer is `SourceSession.draft_reference_spliced`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Check.placed_paths (d : SigData) (env : TyEnv) (q : NativeEff) (a : List Nat) :
    (Internal.place a (run (.part d env q))).table.map (·.path) =
      (Node.addresses (.eff q)).map (a ++ ·) := by
  rw [run_placed, Annotate.check_eq]
  exact tableAt_paths _ _ _ _

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

/-- **A splice needs expansion agreement and no ill-formed reference on either side**
(`SourceSession.canSplice`). A step of `source-feed-edit`. Its consumers are the splice routes'
laws (`feed_ok_cases`, `feed_keepExact_ok`) and `feed_draft`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem canSplice_agrees {s : SourceSession} {c : Sketch} {e : Edit}
    (h : s.canSplice c e = true) : s.expandedEditAgrees c e = true := by
  unfold canSplice at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1

/-- **Where neither sketch holds an ill-formed reference, a splice needs only expansion
agreement.** A step of `source-feed-draft`. Its consumer is `feed_draft`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem canSplice_of_faultFree {s : SourceSession} {c : Sketch} {e : Edit}
    (hs : s.sketch.program.firstRefFault = none) (hc : c.program.firstRefFault = none) :
    s.canSplice c e = s.expandedEditAgrees c e := by
  unfold canSplice
  rw [hs, hc]
  simp only [Option.isNone_none, Bool.and_true]

/-- **Every accepted feed, by its route.** An edit that does not apply is accepted only by
`draft`, which leaves the session. An edit that applies either rechecks the module, or splices
the part check's table below the root at a typed focus, where the part keeps the focus's type and
`canSplice` holds: the expansion moved only at the address, and neither sketch holds an ill-formed
reference. A draft splice also needs `draftOmitAllows` and a typed root. A step of `source-feed-edit`. Its consumers are `feed_keeps` and the feed's coherence. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem feed_ok_cases {o : Oracle} {policy : FeedPolicy} {s : SourceSession} {e : Edit}
    {r : SourceSession × Edit.Step} (h : (s.feed o policy e).value = .ok r) :
    (s.sketch.edit s.app e = none ∧ policy = .draft ∧ r = (s, ⟨e, none, .unchanged⟩)) ∨
    ∃ old c, (Node.eff s.sketch.program).at_ e.path = some (.eff old) ∧
      s.sketch.edit s.app e = some c ∧
      (r = (⟨s.app, c, (run (.module s.app c.holes c.program)).table⟩, ⟨e, some old, .rechecked⟩) ∨
       ∃ key focus, e.path ≠ [] ∧ s.focusAt e.path = some focus ∧
         s.candidatePartKey e.path c = some key ∧ (run key).result = .ok focus.ty ∧
         s.canSplice c e = true ∧
         (policy = .keepExact ∨
           (policy = .draft ∧ draftOmitAllows e focus.ty = true ∧ s.view.type.isSome = true)) ∧
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
                    Or.inr ⟨rfl, hcond.2, ?_⟩, rfl⟩
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
                  refine Or.inr ⟨key, focus, hne, hfocus, hkey, ?_, hagree, Or.inl rfl, rfl⟩
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
spliced exactly where `canSplice` holds. A step of `kept-fill-reference`. Its consumer is
`kept_eq_certified` (`Laws/Program/FillSet.lean`). -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem feed_keepExact_ok {o : Oracle} {s : SourceSession} {e : Edit}
    {r : SourceSession × Edit.Step} (hne : e.path ≠ [])
    (h : (s.feed o .keepExact e).value = .ok r) :
    ∃ old c key focus, (Node.eff s.sketch.program).at_ e.path = some (.eff old) ∧
      s.sketch.edit s.app e = some c ∧ s.focusAt e.path = some focus ∧
      s.candidatePartKey e.path c = some key ∧ (run key).result = .ok focus.ty ∧
      (s.canSplice c e = true → r = s.splice c e old (run key)) ∧
      (s.canSplice c e = false → (s.recheck o .keepExact c e old).value = .ok r) := by
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
focus's type and `canSplice` holds. A step of `kept-fill-reference`. Its consumer is
`kept_eq_certified`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem feed_keepExact_of {o : Oracle} {s : SourceSession} {e : Edit} {old : NativeEff}
    {c : Sketch} {key : CheckInput} {focus : Focus NativeOp} (hne : e.path ≠ [])
    (hat : (Node.eff s.sketch.program).at_ e.path = some (.eff old))
    (hedit : s.sketch.edit s.app e = some c) (hfocus : s.focusAt e.path = some focus)
    (hkey : s.candidatePartKey e.path c = some key) (hres : (run key).result = .ok focus.ty)
    (hagree : s.canSplice c e = true) :
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

/-- **A draft recheck is accepted**: `finish` accepts every draft. A step of `source-feed-edit`.
Its consumer is `feed_draft_ok`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem recheck_draft_ok (o : Oracle) (s : SourceSession) (c : Sketch) (e : Edit)
    (old : NativeEff) : ∃ r, (s.recheck o .draft c e old).value = .ok r := by
  unfold recheck
  rw [Checked.bind_value, Checked.pure_value]
  exact ⟨_, rfl⟩

/-- **A draft is never refused.** A step of `source-session-undo` and of
`source-session-draft-transport`. Its consumers are `feed_undo` and
`DocInternal.replay_drafts_fold`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem feed_draft_ok (o : Oracle) (s : SourceSession) (e : Edit) :
    ∃ r, (s.feed o .draft e).value = .ok r := by
  unfold feed
  split
  · split
    · exact recheck_draft_ok _ _ _ _ _
    · dsimp only
      split
      · split
        · exact recheck_draft_ok _ _ _ _ _
        · split
          · exact recheck_draft_ok _ _ _ _ _
          · rw [Checked.bind_value]
            split
            · split
              · exact ⟨_, rfl⟩
              · exact recheck_draft_ok _ _ _ _ _
            · exact recheck_draft_ok _ _ _ _ _
      · exact recheck_draft_ok _ _ _ _ _
  · exact ⟨_, rfl⟩

/-- **An accepted feed keeps a coherent session coherent.** The pointer of `source-feed-coherent`.
It is false at head in one way: a kept-exact splice keeps a refused root entry that an
omission's new hole row can make typed (`FeedCounterexample.keep_omit_refused`). The splice of a
candidate holding an ill-formed reference once put a second root entry in place of the entry at
the edited address (`git:d048b9a1b`, `feed_coherent_refuted`); `canSplice` now refuses it. The statement is the specification.
`feed_coherent_of_faultFree` proves it on every route but a kept splice at a refused root. So a
feed that splices only where neither the sketch nor the candidate holds an ill-formed reference,
and keeps an omission only at a typed root, needs one more step: `splice_coherent` for a fill at
a refused root, which the battery `brokenElsewhere` accepts. A feed that also keeps fills only at
a typed root needs none. -/
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

/-! ## The splice's coherence where nothing is ill formed

`splice_coherent` is the feed's splice route at a typed root where the candidate holds no
ill-formed reference: the splice gives the candidate's source table. With the recheck route
(`recheck_coherent`), it proves `feed_coherent_of_faultFree`. Each statement is a step of
`source-feed-coherent` and names its consumer. -/

/-- A part key of a candidate is its expansion's sub-program at the address, in the focus's
environment. A step of `source-feed-coherent`. Its consumer is `splice_coherent`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem candidatePartKey_some {s : SourceSession} {path : List Nat} {c : Sketch}
    {key : CheckInput} {focus : Focus NativeOp} (hfocus : s.focusAt path = some focus)
    (h : s.candidatePartKey path c = some key) :
    ∃ q', (Node.eff c.expand.program).at_ path = some (.eff q') ∧
      key = .part (sketchSigData c.expand s.app path) focus.env q' := by
  unfold candidatePartKey at h
  split at h
  · rename_i old q' hf hat
    rw [hfocus, Option.some.injEq] at hf
    subst hf
    cases h
    exact ⟨q', hat, rfl⟩
  · cases h

/-- Where the expanded edit agrees, the old expansion's own edit gives the candidate's
expansion. A step of `source-feed-coherent`. Its consumer is `splice_coherent`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem expandedEditAgrees_some {s : SourceSession} {c : Sketch} {e : Edit}
    (h : s.expandedEditAgrees c e = true) :
    ∃ e', Edit.expanded c.expand e = some e' ∧ s.sketch.expand.edit s.app e' = some c.expand := by
  unfold expandedEditAgrees at h
  dsimp only at h
  split at h
  · rename_i e' he'
    refine ⟨e', he', ?_⟩
    obtain ⟨y, hy, hyeq⟩ := Option.map_eq_some_iff.mp (of_decide_eq_true h)
    obtain ⟨yp, yh⟩ := y
    simp only [Prod.mk.injEq] at hyeq
    obtain ⟨rfl, rfl⟩ := hyeq
    exact hy
  · cases h

/-- **The candidate's expansion is a filling of the old expansion**, grown by an omission's hole
row: that base keeps the old expansion's check, focus and table (`Sketch.check_more_holes`,
`Sketch.focusAt_more_holes`, `Sketch.table_more_holes`). A step of `source-feed-coherent`. Its
consumer is `splice_coherent`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem splice_base {s : SourceSession} {c : Sketch} {e e' : Edit} {q' q0 : NativeEff}
    {focus : Focus NativeOp} {T : EffTy}
    (hXcheck : s.sketch.expand.check s.app = .ok T)
    (hf0 : s.sketch.expand.focusAt s.app e.path = some ⟨q0, focus.env, focus.ty⟩)
    (hq'at : (Node.eff c.expand.program).at_ e.path = some (.eff q'))
    (he' : Edit.expanded c.expand e = some e') (hX' : s.sketch.expand.edit s.app e' = some c.expand) :
    ∃ s0 : Sketch, s0.fillAt e.path q' = some c.expand ∧ s0.check s.app = .ok T ∧
      s0.focusAt s.app e.path = some ⟨q0, focus.env, focus.ty⟩ ∧
      s0.table s.app = s.sketch.expand.table s.app := by
  cases e with
  | fill a q =>
    simp only [Edit.expanded, Edit.path] at he' hq'at hf0 ⊢
    rw [hq'at] at he'
    cases he'
    exact ⟨s.sketch.expand, hX', hXcheck, hf0, rfl⟩
  | omitAt a row =>
    simp only [Edit.expanded, Edit.path] at he' hq'at hf0 ⊢
    cases he'
    have hX'' : ({ s.sketch.expand with holes := s.sketch.expand.holes ++ [row] } : Sketch).fillAt a
        (Sketch.hole s.app s.sketch.expand.holes.length) = some c.expand := hX'
    obtain ⟨p', hrep, hcx⟩ := Sketch.fillAt_some hX''
    have hhole : (Node.eff c.expand.program).at_ a =
        some (.eff (Sketch.hole s.app s.sketch.expand.holes.length)) := by
      rw [hcx]
      exact (Node.replaceAt_spec hrep).1
    rw [hhole, Option.some.injEq, Node.eff.injEq] at hq'at
    subst hq'at
    exact ⟨_, hX'', Sketch.check_more_holes _ _ _ hXcheck, Sketch.focusAt_more_holes hXcheck hf0 _,
      Sketch.table_more_holes hXcheck _⟩

/-- **Splicing the source table is splicing the expansion's table with the copies' entries
dropped**, for any new segment, where the session's sketch holds no ill-formed reference: the
expansion's table splits at the edited address into a contiguous block (`Node.addresses_split`),
whose head is below no reference site, and the edit keeps the sites outside it. A step of
`source-feed-coherent` and of `source-feed-draft`. Its consumers are `splice_coherent` and
`feed_draft`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem source_splice_filter {s : SourceSession} {c : Sketch} {e : Edit} {old q0 : NativeEff}
    (hc : s.Coherent) (hsf : s.sketch.program.firstRefFault = none)
    (hedit : s.sketch.edit s.app e = some c)
    (hatS : (Node.eff s.sketch.program).at_ e.path = some (.eff old))
    (hatX : (Node.eff s.sketch.expand.program).at_ e.path = some (.eff q0)) (P : List Table.Entry) :
    Table.splice s.table e.path (P.filter fun x => !Table.belowSite c.sites x.path) =
      (Table.splice (s.sketch.expand.table s.app) e.path P).filter
        fun x => !Table.belowSite c.sites x.path := by
  rw [table_eq hc, Sketch.sourceTable_eq_filter _ _ hsf]
  obtain ⟨A, C, haddr, hA, hC⟩ := Node.addresses_split e.path (.eff s.sketch.expand.program)
    (.eff q0) hatX
  obtain ⟨restq, hq0head⟩ := addresses_eff_head q0
  have hT : s.sketch.expand.table s.app =
      A.map (s.sketch.expand.tableEntry s.app) ++
        ((Node.addresses (.eff q0)).map (e.path ++ ·)).map (s.sketch.expand.tableEntry s.app) ++
        C.map (s.sketch.expand.tableEntry s.app) := by
    unfold Sketch.table
    rw [haddr, List.map_append, List.map_append]
  have hpathE : ∀ a, (s.sketch.expand.tableEntry s.app a).path = a :=
    Sketch.tableEntry_path s.sketch.expand s.app
  have hAf : ∀ x ∈ A.map (s.sketch.expand.tableEntry s.app), Table.under e.path x.path = false := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    rw [hpathE]
    exact hA a ha
  have hCf : ∀ x ∈ C.map (s.sketch.expand.tableEntry s.app), Table.under e.path x.path = false := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    rw [hpathE]
    exact hC a ha
  have hBf : ∀ x ∈ ((Node.addresses (.eff q0)).map (e.path ++ ·)).map
      (s.sketch.expand.tableEntry s.app), Table.under e.path x.path = true := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    obtain ⟨r, -, rfl⟩ := List.mem_map.mp ha
    rw [hpathE]
    exact Table.under_append e.path r
  have hbmem : s.sketch.expand.tableEntry s.app e.path ∈
      ((Node.addresses (.eff q0)).map (e.path ++ ·)).map (s.sketch.expand.tableEntry s.app) := by
    refine List.mem_map.mpr ⟨e.path, List.mem_map.mpr ⟨[], ?_, List.append_nil _⟩, rfl⟩
    rw [hq0head]
    exact List.mem_cons_self
  have hgb : (!Table.belowSite s.sketch.sites (s.sketch.expand.tableEntry s.app e.path).path) =
      true := by
    rw [hpathE]
    unfold Sketch.sites
    rw [belowSite_at_eff hatS]
    rfl
  obtain ⟨x, hrepc⟩ := Sketch.edit_replaceAt hedit
  have hagreeSites : ∀ x' : Table.Entry, Table.under e.path x'.path = false →
      (!Table.belowSite c.sites x'.path) = (!Table.belowSite s.sketch.sites x'.path) := by
    intro x' hx'
    unfold Sketch.sites
    rw [belowSite_replaceAt hrepc hatS hx']
  have hspl : Table.splice (s.sketch.expand.table s.app) e.path P =
      A.map (s.sketch.expand.tableEntry s.app) ++ P ++ C.map (s.sketch.expand.tableEntry s.app) := by
    rw [hT, List.append_assoc, Table.splice_three hAf ⟨_, hbmem, hBf _ hbmem⟩ hCf,
      Table.splice_all_under hBf, List.append_assoc]
  rw [hspl, hT]
  exact Table.splice_filter hAf hCf hBf hbmem hgb hagreeSites

/-- **The splice gives the candidate's source table** at a typed root, where the candidate holds
no ill-formed reference, the part keeps the focus's type and the expanded edit agrees. The
expansion's table splices (`Sketch.table_fill`, at the base of `splice_base`), and dropping the
copies' entries commutes with that splice (`Table.splice_filter`). A step of
`source-feed-coherent`. Its consumer is `feed_coherent_of_faultFree`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem splice_coherent {s : SourceSession} {c : Sketch} {e : Edit} {old : NativeEff}
    {key : CheckInput} {focus : Focus NativeOp} {T : EffTy}
    (hc : s.Coherent) (hroot : s.sketch.sourceCheck s.app = .ok T)
    (hcf : c.program.firstRefFault = none) (hne : e.path ≠ [])
    (hedit : s.sketch.edit s.app e = some c) (hfocus : s.focusAt e.path = some focus)
    (hkey : s.candidatePartKey e.path c = some key) (hres : (run key).result = .ok focus.ty)
    (hagree : s.expandedEditAgrees c e = true) :
    (s.splice c e old (run key)).1.Coherent := by
  obtain ⟨hsf, hXcheck⟩ := Sketch.sourceCheck_ok hroot
  obtain ⟨q', hq'at, rfl⟩ := candidatePartKey_some hfocus hkey
  obtain ⟨e', he', hX'⟩ := expandedEditAgrees_some hagree
  obtain ⟨hatS, q0, hf0⟩ := focusAt_typed hc hfocus hne
  obtain ⟨s0, hfill0, hcheck0, hfocus0, htable0⟩ := splice_base hXcheck hf0 hq'at he' hX'
  -- the part check reads the base's signature at the address
  have hsig := Sketch.sigData_fillAt hne hfill0 hfocus0
  have hcheckq : Checker.check (s0.sigAt s.app e.path) focus.env [] q' = .ok focus.ty := by
    rw [← hsig, ← Check.run_part_result]
    exact hres
  have hq : HasTy (s0.sigAt s.app e.path) focus.env q' focus.ty :=
    effTy_sound _ _ _ _ (effTy_of_check hcheckq)
  have hfillT := Sketch.table_fill hcheck0 hne hfocus0 hq hfill0
  rw [htable0] at hfillT
  have hplaced : (Internal.place e.path (run (.part (sketchSigData c.expand s.app e.path) focus.env
      q'))).table = tableAt (s0.sigAt s.app e.path) (some (.env focus.env)) (.eff q') e.path := by
    rw [run_placed, Annotate.check_eq, hsig]
  show Table.splice s.table e.path (Table.atSource c.sites c.program.firstRefFault
    (Internal.place e.path (run (.part (sketchSigData c.expand s.app e.path) focus.env q'))).table) =
    c.sourceTable s.app
  dsimp only at hfillT
  have hatoms : ∀ (sites : List (List Nat)) (t : List Table.Entry),
      Table.atSource sites none t = t.filter (fun e => !Table.belowSite sites e.path) :=
    fun _ _ => rfl
  rw [hcf, hplaced, hatoms, Sketch.sourceTable_eq_filter _ _ hcf, hfillT]
  exact source_splice_filter hc hsf hedit hatS (Sketch.focusAt_at hf0) _

/-- **A recheck holds the candidate's source table**: the module check's table, part by part
(`Sketch.sourceAnnotate_eq_sourceTable`). A step of `source-feed-coherent`. Its consumer is
`feed_coherent_of_faultFree`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem recheck_coherent (s : SourceSession) (c : Sketch) :
    (⟨s.app, c, (run (.module s.app c.holes c.program)).table⟩ : SourceSession).Coherent :=
  Sketch.sourceAnnotate_eq_sourceTable c s.app

/-- **An accepted feed keeps coherence where the candidate holds no ill-formed reference and a
kept-exact splice stands at a typed root.** Every route but the two that `feed_coherent`'s
counterexamples take: the splice of a candidate with an ill-formed reference, and a kept-exact
splice at a refused root, where an omission's new hole row can change the root's check
(`FeedCounterexample.keep_omit_refused`). It is the true form of `feed_coherent` at head, and
the whole of its proof once the feed splices only there. A step of `source-feed-coherent`. Its
consumers are `feed_draft` and the feed's coherence. Not established: the cost, or a splice at a
refused root. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem feed_coherent_of_faultFree {o : Oracle} {policy : FeedPolicy} {s next : SourceSession}
    {e : Edit} {step : Edit.Step} (hc : s.Coherent)
    (hcand : ∀ c, s.sketch.edit s.app e = some c → c.program.firstRefFault = none)
    (hroot : policy = .keepExact → s.view.type.isSome = true)
    (h : (s.feed o policy e).value = .ok (next,step)) : next.Coherent := by
  rcases feed_ok_cases h with ⟨-, -, hr⟩ |
      ⟨old, c, -, hedit, hr | ⟨key, focus, hne, hfocus, hkey, hres, hagree, hpol, hr⟩⟩
  · cases hr
    exact hc
  · cases hr
    exact recheck_coherent s c
  · have hview : s.view.type.isSome = true := by
      rcases hpol with hk | ⟨-, -, hv⟩
      · exact hroot hk
      · exact hv
    rw [view_type hc] at hview
    obtain ⟨T, hT⟩ : ∃ T, s.sketch.sourceCheck s.app = .ok T := by
      cases hsc : s.sketch.sourceCheck s.app with
      | ok T => exact ⟨T, rfl⟩
      | error r =>
        rw [hsc] at hview
        cases hview
    cases hr
    exact splice_coherent (old := old) hc hT (hcand c hedit) hne hedit hfocus hkey hres
      (canSplice_agrees hagree)

/-! ## A draft is the expansion's edit session at the source's addresses

Where the sketch holds no ill-formed reference, the source table and the expansion's table hold
the same root and the same entry at a source address (`typedAt_root_expand`, `typedAt_expand`).
So the draft splices exactly where the expansion's edit session splices
(`draft_conditions_of_reference`, `draft_reference_spliced`), and both tables are coherent.
Each statement here is a step of `source-feed-draft`, and its consumer is `feed_draft`. -/

/-- At the root, the source table holds the expansion's entry where the sketch holds no
ill-formed reference. A step of `source-feed-draft`. Its consumer is `focusAt_of_expand`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem typedAt_root_expand {s : SourceSession} (hc : s.Coherent)
    (hfault : s.sketch.program.firstRefFault = none) :
    Table.typedAt s.table [] = Table.typedAt (s.sketch.expand.table s.app) [] := by
  obtain ⟨rest, ht⟩ := Sketch.sourceTable_head s.sketch s.app
  obtain ⟨rest', ht'⟩ := Sketch.table_head s.sketch.expand s.app
  have hsc : s.sketch.sourceCheck s.app = s.sketch.expand.check s.app := by
    unfold Sketch.sourceCheck
    rw [hfault]
  rw [table_eq hc, ht, ht', hsc]
  unfold Table.typedAt
  rw [List.find?_cons, List.find?_cons]
  rfl

/-- At an address of a program below the root, the source table holds the expansion's entry. A
step of `source-feed-draft`. Its consumer is `focusAt_of_expand`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem typedAt_expand {s : SourceSession} (hc : s.Coherent) {a : List Nat} {old : NativeEff}
    (hat : (Node.eff s.sketch.program).at_ a = some (.eff old)) (hne : a ≠ []) :
    Table.typedAt s.table a = Table.typedAt (s.sketch.expand.table s.app) a := by
  rw [table_eq hc]
  exact Sketch.sourceTable_typedAt s.sketch s.app ((mem_addresses_iff _ _).mpr (by rw [hat]; rfl))
    hne

/-- Where the expansion's table types the root and an address of a program, the session has the
focus there and the root's type. A step of `source-feed-draft`. Its consumer is
`draft_conditions_of_reference`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem focusAt_of_expand {s : SourceSession} {a : List Nat} {old : NativeEff}
    {root : TyEnv × EffTy} {tys : TyEnv} {ty : EffTy} (hc : s.Coherent)
    (hfault : s.sketch.program.firstRefFault = none)
    (hat : (Node.eff s.sketch.program).at_ a = some (.eff old)) (hne : a ≠ [])
    (hroot : Table.typedAt (s.sketch.expand.table s.app) [] = some root)
    (hatT : Table.typedAt (s.sketch.expand.table s.app) a = some (tys, ty)) :
    s.focusAt a = some ⟨old, tys, ty⟩ ∧ s.view.type = some root.2 ∧
      s.sketch.expand.check s.app = .ok root.2 := by
  have hXc : s.sketch.expand.check s.app = .ok root.2 := by
    have h0 := Table.typedAt_table_nil s.sketch.expand s.app
    rw [hroot] at h0
    cases hx : s.sketch.expand.check s.app with
    | ok t =>
      rw [hx] at h0
      cases h0
      rfl
    | error r =>
      rw [hx] at h0
      cases h0
  refine ⟨?_, ?_, hXc⟩
  · unfold focusAt
    rw [hat, typedAt_expand hc hat hne, hatT]
  · show (Table.typedAt s.table []).map (·.2) = _
    rw [typedAt_root_expand hc hfault, hroot]
    rfl

/-- **Where the expansion's edit session splices, the draft's splice conditions hold**: a focus
below the root, a typed root, `draftOmitAllows`, and a part key whose check keeps the focus's
type. The expansion's table holds the source's types (`focusAt_of_expand`), and the part check
reads the expansion's signature at the address (`Sketch.sigData_fillAt`). An omission's hole has
its row's type (`Sketch.hole_hasTy_focus`). A step of `source-feed-draft`. Its consumer is
`feed_draft`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem draft_conditions_of_reference {s : SourceSession} {c : Sketch} {e e' : Edit}
    {old : NativeEff} (hc : s.Coherent) (hfault : s.sketch.program.firstRefFault = none)
    (hat : (Node.eff s.sketch.program).at_ e.path = some (.eff old))
    (he' : Edit.expanded c.expand e = some e') (hX' : s.sketch.expand.edit s.app e' = some c.expand)
    (hspl : ((EditSession.open s.app s.sketch.expand).feed e').2 ≠ .rechecked) :
    ∃ focus ty0 key, e.path ≠ [] ∧ s.focusAt e.path = some focus ∧ s.view.type = some ty0 ∧
      draftOmitAllows e focus.ty = true ∧ s.candidatePartKey e.path c = some key ∧
      (run key).result = .ok focus.ty := by
  cases e with
  | fill a q =>
    simp only [Edit.expanded] at he'
    split at he'
    · rename_i q' hq'at
      cases he'
      have hfillX : s.sketch.expand.fillAt a q' = some c.expand := hX'
      simp only [EditSession.open, EditSession.feed, hfillX, Sketch.annotate_eq_table] at hspl
      split at hspl
      · rename_i i r root tys ty hroot hatT
        split at hspl
        · rename_i sub ty' hcheck
          split at hspl
          · rename_i hty
            subst hty
            simp only [Edit.path] at hat ⊢
            have hne : i :: r ≠ [] := List.cons_ne_nil i r
            obtain ⟨hfocus, hview, -⟩ := focusAt_of_expand hc hfault hat hne hroot hatT
            obtain ⟨q0, hf0⟩ := Table.typedAt_table hatT hne
            have hsig := Sketch.sigData_fillAt hne hfillX hf0
            rw [Annotate.check_eq] at hcheck
            have hchk := (Prod.mk.inj hcheck).2
            refine ⟨⟨old, tys, ty'⟩, root.2, .part (sketchSigData c.expand s.app (i :: r)) tys q',
              hne, hfocus, hview, rfl, ?_, ?_⟩
            · unfold candidatePartKey
              rw [hfocus, hq'at]
            · rw [Check.run_part_result, hsig]
              exact check_ok_path hchk []
          · exact absurd rfl hspl
        · exact absurd rfl hspl
      · exact absurd rfl hspl
    · cases he'
  | omitAt a row =>
    simp only [Edit.expanded] at he'
    cases he'
    have homitX : s.sketch.expand.omitAt s.app a row = some c.expand := hX'
    have hX'' : ({ s.sketch.expand with holes := s.sketch.expand.holes ++ [row] } : Sketch).fillAt a
        (Sketch.hole s.app s.sketch.expand.holes.length) = some c.expand := homitX
    obtain ⟨p', hrep, hcx⟩ := Sketch.fillAt_some hX''
    have hhole : (Node.eff c.expand.program).at_ a =
        some (.eff (Sketch.hole s.app s.sketch.expand.holes.length)) := by
      rw [hcx]
      exact (Node.replaceAt_spec hrep).1
    simp only [EditSession.open, EditSession.feed, homitX, Sketch.annotate_eq_table] at hspl
    split at hspl
    · rename_i i r root tys ty hroot hatT
      split at hspl
      · rename_i hcond
        obtain ⟨hrow, hans, herr, hansN, herrN, hform⟩ := hcond
        simp only [Edit.path] at hat ⊢
        have hne : i :: r ≠ [] := List.cons_ne_nil i r
        obtain ⟨hfocus, hview, hXc⟩ := focusAt_of_expand hc hfault hat hne hroot hatT
        obtain ⟨q0, hf0⟩ := Table.typedAt_table hatT hne
        have hf1 := Sketch.focusAt_more_holes hXc hf0 [row]
        have hsig := Sketch.sigData_fillAt hne hX'' hf1
        have hform' := hform
        rw [hrow] at hform'
        have formed := (Formation.check_eq_none_iff _).mp (Option.isNone_iff_eq_none.mp hform')
        have hq := Sketch.hole_hasTy_focus (s := s.sketch.expand) (app := s.app) (path := i :: r)
          (f := ⟨q0, tys, ty⟩) row.name hans herr hansN herrN formed
        rw [← hrow] at hq
        refine ⟨⟨old, tys, ty⟩, root.2,
          .part (sketchSigData c.expand s.app (i :: r)) tys
            (Sketch.hole s.app s.sketch.expand.holes.length),
          hne, hfocus, hview, ?_, ?_, ?_⟩
        · simp only [draftOmitAllows, decide_eq_true hrow, hans, herr, decide_eq_true hansN,
            decide_eq_true herrN, hform, Bool.and_self]
        · unfold candidatePartKey
          rw [hfocus, hhole]
        · rw [Check.run_part_result, hsig]
          exact check_complete _ _ _ _ hq []
      · exact absurd rfl hspl
    · exact absurd rfl hspl

/-- **A draft below the root splices** where the focus and the root are typed, `canSplice` holds,
`draftOmitAllows` holds and the part check keeps the focus's type: the converse of
`feed_ok_cases`'s draft splice. A step of `source-feed-draft`. Its consumer is `feed_draft`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem feed_draft_of {o : Oracle} {s : SourceSession} {e : Edit} {old : NativeEff} {c : Sketch}
    {key : CheckInput} {focus : Focus NativeOp} {ty0 : EffTy} (hne : e.path ≠ [])
    (hat : (Node.eff s.sketch.program).at_ e.path = some (.eff old))
    (hedit : s.sketch.edit s.app e = some c) (hfocus : s.focusAt e.path = some focus)
    (hview : s.view.type = some ty0) (hagree : s.canSplice c e = true)
    (hallow : draftOmitAllows e focus.ty = true)
    (hkey : s.candidatePartKey e.path c = some key) (hres : (run key).result = .ok focus.ty) :
    (s.feed o .draft e).value = .ok (s.splice c e old (run key)) := by
  obtain ⟨i, rest, hpath⟩ := List.exists_cons_of_ne_nil hne
  unfold feed
  simp only [hat, hedit]
  split
  · rename_i h0
    rw [hpath] at h0
    cases h0
  · simp only [hfocus, hview, hagree, hallow, Bool.not_true, Bool.or_self, Bool.false_eq_true,
      ↓reduceIte, hkey, Checked.bind_value, Checked.ask_value, hres, Checked.pure_value]

/-- **The expansion's edit session holds the candidate expansion's table**: it is coherent
(`EditSession.feed_coherent`) and holds the candidate's expansion. A step of `source-feed-draft`.
Its consumer is `feed_draft`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem reference_table {s : SourceSession} {c : Sketch} {e' : Edit}
    (hX' : s.sketch.expand.edit s.app e' = some c.expand) :
    ((EditSession.open s.app s.sketch.expand).feed e').1.table = c.expand.table s.app := by
  have h1 := EditSession.feed_coherent (EditSession.open_coherent s.app s.sketch.expand) e'
  have h2 : ((EditSession.open s.app s.sketch.expand).feed e').1.sketch = c.expand :=
    EditSession.feed_edit hX'
  have h3 := (EditSession.feed_keeps (EditSession.open s.app s.sketch.expand) e').1
  rw [h1, h2, h3]
  rfl

/-- **Where the draft splices, the expansion's edit session splices**, and shows the addresses
of the part's placed table: a filling's check at the expansion's signature keeps the focus's
type, and an omission's row declares it. A step of `source-feed-draft`. Its consumer is
`feed_draft`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem draft_reference_spliced {s : SourceSession} {c : Sketch} {e e' : Edit}
    {focus : Focus NativeOp} {ty0 : EffTy} {key : CheckInput} (hc : s.Coherent) (hne : e.path ≠ [])
    (hfocus : s.focusAt e.path = some focus) (hview : s.view.type = some ty0)
    (hallow : draftOmitAllows e focus.ty = true)
    (hkey : s.candidatePartKey e.path c = some key) (hres : (run key).result = .ok focus.ty)
    (he' : Edit.expanded c.expand e = some e') (hX' : s.sketch.expand.edit s.app e' = some c.expand) :
    ((EditSession.open s.app s.sketch.expand).feed e').2 =
      .spliced ((Internal.place e.path (run key)).table.map (·.path)) := by
  have hsc : s.sketch.sourceCheck s.app = .ok ty0 := by
    rw [view_type hc] at hview
    cases hx : s.sketch.sourceCheck s.app with
    | ok t =>
      rw [hx] at hview
      cases hview
      rfl
    | error r =>
      rw [hx] at hview
      cases hview
  obtain ⟨-, hXc⟩ := Sketch.sourceCheck_ok hsc
  obtain ⟨-, q0, hf0⟩ := focusAt_typed hc hfocus hne
  obtain ⟨q', hq'at, rfl⟩ := candidatePartKey_some hfocus hkey
  obtain ⟨rest, hhead⟩ := Sketch.table_head s.sketch.expand s.app
  have hroot : Table.typedAt (s.sketch.expand.table s.app) [] = some ([], ty0) := by
    rw [hhead, hXc]
    unfold Table.typedAt
    rw [List.find?_cons]
    rfl
  have hatT := Table.typedAt_table_of_focusAt hf0 hne
  obtain ⟨i, r, hpath⟩ := List.exists_cons_of_ne_nil hne
  cases e with
  | fill a q =>
    rw [Check.placed_paths]
    simp only [Edit.path] at hpath hq'at hatT hf0 hfocus hne hres ⊢
    subst hpath
    simp only [Edit.expanded, hq'at] at he'
    cases he'
    have hfillX : s.sketch.expand.fillAt (i :: r) q' = some c.expand := hX'
    have hsig := Sketch.sigData_fillAt hne hfillX hf0
    have hchk : Checker.check (s.sketch.expand.sigAt s.app (i :: r)) focus.env (i :: r) q' =
        .ok focus.ty := by
      rw [Check.run_part_result, hsig] at hres
      exact check_ok_path hres (i :: r)
    simp only [EditSession.open, EditSession.feed, hfillX, Sketch.annotate_eq_table, hroot, hatT,
      Annotate.check_eq, hchk, ↓reduceIte, tableAt_paths]
  | omitAt a row =>
    simp only [Edit.path] at hpath hq'at hatT hf0 hfocus hne hallow ⊢
    subst hpath
    simp only [Edit.expanded] at he'
    cases he'
    have homitX : s.sketch.expand.omitAt s.app (i :: r) row = some c.expand := hX'
    have hX'' : ({ s.sketch.expand with holes := s.sketch.expand.holes ++ [row] } : Sketch).fillAt
        (i :: r) (Sketch.hole s.app s.sketch.expand.holes.length) = some c.expand := homitX
    obtain ⟨p', hrep, hcx⟩ := Sketch.fillAt_some hX''
    have hhole : (Node.eff c.expand.program).at_ (i :: r) =
        some (.eff (Sketch.hole s.app s.sketch.expand.holes.length)) := by
      rw [hcx]
      exact (Node.replaceAt_spec hrep).1
    rw [hhole, Option.some.injEq, Node.eff.injEq] at hq'at
    subst hq'at
    have hcond : row = Row.hole row.name focus.ty.answer focus.ty.error focus.ty.requires.elems ∧
        focus.ty.answer.closed = true ∧ focus.ty.error.closed = true ∧
        focus.ty.answer.normalize = focus.ty.answer ∧ focus.ty.error.normalize = focus.ty.error ∧
        (Formation.check (Formation.instantiatedSites row.normalizeTypes [])).isNone = true := by
      simp only [draftOmitAllows, Bool.and_eq_true, decide_eq_true_eq] at hallow
      obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hallow
      exact ⟨h1, h2, h3, h4, h5, h6⟩
    simp only [EditSession.open, EditSession.feed, homitX, Sketch.annotate_eq_table, hroot, hatT]
    rw [if_pos hcond, run_placed, Annotate.check_eq]
    simp only [Sketch.hole, tableAt_perform, List.map_cons, List.map_nil]

/-- **A draft from a coherent session whose sketch and candidate hold no ill-formed reference is
the expansion's edit session, shown at the source's addresses.** `EditSession.feed` is the
reference, and no second edit interpreter is defined. The draft splices exactly where the
reference splices (`draft_conditions_of_reference`, `draft_reference_spliced`), and both tables
are coherent (`feed_coherent_of_faultFree`, `reference_table`). The pointer of
`source-feed-draft`. Reach: coherent sessions, every edit, certified oracles. The first form had
no premise on ill-formed references and is false: on a sketch with one the draft refuses to
splice, since its root is refused, while the expansion's edit session splices
(`FeedCounterexample.feed_draft_refuted`). Not established: the cost. Consumers:
`replay_drafts_view` and the transport of `source-session-coherent`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem feed_draft (o : Oracle) (s : SourceSession) (hc : s.Coherent) (e : Edit)
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
           step.delta = reference.2.atSource candidate.sites) := by
  obtain ⟨⟨next, step⟩, hv⟩ := feed_draft_ok o s e
  have hcoh : next.Coherent := feed_coherent_of_faultFree hc hcand (by intro h; cases h) hv
  refine ⟨next, step, hv, ?_⟩
  rcases feed_ok_cases hv with ⟨hnone, -, hr⟩ |
      ⟨old, c, hat, hedit, hr | ⟨key, focus, hne, hfocus, hkey, hres, hagree, hpol, hr⟩⟩
  · -- the edit does not apply
    obtain ⟨hn, hst⟩ := Prod.mk.inj hr
    subst next step
    refine ⟨rfl, ?_, ?_⟩
    · split
      · rename_i old hat
        obtain ⟨c, hc'⟩ := Sketch.edit_of_at (app := s.app) (e := e) hat
        rw [hnone] at hc'
        cases hc'
      · rfl
    · rw [hnone]
      exact ⟨rfl, rfl⟩
  · -- a recheck
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
    have hcf := hcand c hedit
    have htab : (run (.module s.app c.holes c.program)).table =
        Table.atSource c.sites c.program.firstRefFault (c.expand.table s.app) := by
      rw [hcf]
      exact (recheck_coherent s c).trans (Sketch.sourceTable_eq_filter c s.app hcf)
    refine ⟨rfl, by rw [hat], ?_⟩
    rw [hedit]
    refine ⟨rfl, rfl, ?_⟩
    dsimp only
    cases hag : s.expandedEditAgrees c e with
    | false =>
      split
      · simp only [Bool.false_eq_true, ↓reduceIte]
        refine ⟨?_, rfl⟩
        rw [htab]
        exact congrArg _ (Sketch.annotate_eq_table c.expand s.app).symm
      · refine ⟨?_, rfl⟩
        rw [htab]
        exact congrArg _ (Sketch.annotate_eq_table c.expand s.app).symm
    | true =>
      obtain ⟨e', he', hX'⟩ := expandedEditAgrees_some hag
      rw [he']
      simp only [↓reduceIte]
      refine ⟨by rw [reference_table hX']; exact htab, ?_⟩
      -- the reference rechecks too: a splice there gives the draft's splice conditions
      have hrech : ((EditSession.open s.app s.sketch.expand).feed e').2 = .rechecked := by
        cases hd : ((EditSession.open s.app s.sketch.expand).feed e').2 with
        | rechecked => rfl
        | spliced shown =>
          obtain ⟨focus, ty0, key, hne, hfocus, hview, hallow, hkey, hres⟩ :=
            draft_conditions_of_reference hc hfault hat he' hX' (by rw [hd]; exact nofun)
          have hv' := feed_draft_of (o := o) hne hat hedit hfocus hview
            ((canSplice_of_faultFree hfault (hcand c hedit)).trans hag) hallow hkey hres
          rw [hv] at hv'
          have hd' := congrArg (fun r : Except FeedRefusal (SourceSession × Edit.Step) =>
            match r with
            | .ok x => x.2.delta
            | .error _ => .unchanged) hv'
          cases hd'
        | unchanged =>
          obtain ⟨focus, ty0, key, hne, hfocus, hview, hallow, hkey, hres⟩ :=
            draft_conditions_of_reference hc hfault hat he' hX' (by rw [hd]; exact nofun)
          have hv' := feed_draft_of (o := o) hne hat hedit hfocus hview
            ((canSplice_of_faultFree hfault (hcand c hedit)).trans hag) hallow hkey hres
          rw [hv] at hv'
          have hd' := congrArg (fun r : Except FeedRefusal (SourceSession × Edit.Step) =>
            match r with
            | .ok x => x.2.delta
            | .error _ => .unchanged) hv'
          cases hd'
      rw [hrech]
      rfl
  · -- a splice
    have hcf := hcand c hedit
    have hnext : next = (s.splice c e old (run key)).1 := congrArg Prod.fst hr
    have hstep : step = (s.splice c e old (run key)).2 := congrArg Prod.snd hr
    subst hnext hstep
    rcases hpol with hk | ⟨-, hallow, hviewS⟩
    · cases hk
    obtain ⟨ty0, hview⟩ := Option.isSome_iff_exists.mp hviewS
    obtain ⟨e', he', hX'⟩ := expandedEditAgrees_some (canSplice_agrees hagree)
    have hspl := draft_reference_spliced hc hne hfocus hview hallow hkey hres he' hX'
    refine ⟨rfl, by rw [hat]; rfl, ?_⟩
    rw [hedit]
    refine ⟨rfl, rfl, ?_⟩
    dsimp only
    rw [he', canSplice_agrees hagree]
    simp only [↓reduceIte]
    refine ⟨?_, ?_⟩
    · have h1 : (s.splice c e old (run key)).1.table = c.sourceTable s.app := hcoh
      rw [h1, reference_table hX', hcf]
      exact Sketch.sourceTable_eq_filter c s.app hcf
    · rw [hspl]
      show Edit.Delta.spliced ((Table.atSource c.sites c.program.firstRefFault
          (Internal.place e.path (run key)).table).map (·.path)) =
        Edit.Delta.spliced (((Internal.place e.path (run key)).table.map (·.path)).filter
          fun a => !Table.belowSite c.sites a)
      rw [hcf, List.filter_map]
      rfl

/-- **A kept-exact finish keeps the root's type and the edited address's entry.** A step of
`source-feed-keep-exact`. Its consumer is `recheck_keepExact_ok`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem finish_keepExact_ok {s n : SourceSession} {e : Edit} {st : Edit.Step} {v : Verdict}
    {r : SourceSession × Edit.Step} (h : finish .keepExact s n e st v = .ok r) :
    ∃ ty, v.result = .ok ty ∧ s.view.type = some ty ∧
      (e.path ≠ [] → Table.typedAt s.table e.path = Table.typedAt n.table e.path) := by
  cases hv : v.result with
  | error why =>
    simp only [finish, hv] at h
    cases h
  | ok ty =>
    simp only [finish, hv] at h
    split at h
    · cases h
    · rename_i hty
      split at h
      · cases h
      · rename_i hloc
        refine ⟨ty, rfl, ?_, fun hne => ?_⟩
        · simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hty
          exact hty
        · simp only [bne_iff_ne, ne_eq, Bool.and_eq_true, not_and, Decidable.not_not] at hloc
          exact hloc hne

/-- **An accepted kept-exact recheck**: its session and step, a typed module check equal to the old
root's type, and the edited address's entry kept. A step of `source-feed-keep-exact`. Its
consumer is `feed_keepExact_of_faultFree`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem recheck_keepExact_ok {o : Oracle} {s : SourceSession} {c : Sketch} {e : Edit}
    {old : NativeEff} {r : SourceSession × Edit.Step}
    (h : (s.recheck o .keepExact c e old).value = .ok r) :
    r = (⟨s.app, c, (run (.module s.app c.holes c.program)).table⟩, ⟨e, some old, .rechecked⟩) ∧
    ∃ ty, (run (.module s.app c.holes c.program)).result = .ok ty ∧ s.view.type = some ty ∧
      (e.path ≠ [] → Table.typedAt s.table e.path =
        Table.typedAt (run (.module s.app c.holes c.program)).table e.path) := by
  refine ⟨recheck_ok h, ?_⟩
  unfold recheck at h
  rw [Checked.bind_value, Checked.pure_value, Checked.ask_value] at h
  exact finish_keepExact_ok h

/-- **A kept-exact feed below the root, whose candidate holds no ill-formed reference, keeps the
root's and the address's types, and splices exactly where `canSplice` holds.** The splice
keeps the root entry first, and its new segment starts with the part's own entry at the focus's
type; a recheck is checked by `finish`. It is the true form of `feed_keepExact` at head, and the
whole of its proof once the feed splices only such candidates. A step of
`source-feed-keep-exact`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem feed_keepExact_of_faultFree {o : Oracle} {s next : SourceSession} {e : Edit}
    {step : Edit.Step} (hc : s.Coherent) (hne : e.path ≠ [])
    (hcand : ∀ c, s.sketch.edit s.app e = some c → c.program.firstRefFault = none)
    (h : (s.feed o .keepExact e).value = .ok (next,step)) :
    next.view.type = s.view.type ∧
      Table.typedAt next.table e.path = Table.typedAt s.table e.path ∧
      (s.canSplice next.sketch e = true → ∃ shown, step.delta = .spliced shown) ∧
      (s.canSplice next.sketch e = false → step.delta = .rechecked) := by
  obtain ⟨old, c, key, focus, hat, hedit, hfocus, hkey, hres, hspl, hrec⟩ := feed_keepExact_ok hne h
  have hsk : next.sketch = c := (feed_keeps h).2.2.2 c hedit
  rw [hsk]
  cases hagree : s.canSplice c e with
  | true =>
    have hr := hspl hagree
    obtain ⟨q', hq'at, rfl⟩ := candidatePartKey_some hfocus hkey
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
    refine ⟨?_, ?_, fun _ => ⟨_, rfl⟩, fun hf => nomatch hf⟩
    · show (Table.typedAt (Table.splice s.table e.path _) []).map (·.2) =
        (Table.typedAt s.table []).map (·.2)
      obtain ⟨rest, hhead⟩ := Sketch.sourceTable_head s.sketch s.app
      rw [table_eq hc, hhead, Table.typedAt_splice_root rfl hne]
    · have hold : Table.typedAt s.table e.path = some (focus.env, focus.ty) := by
        unfold focusAt at hfocus
        split at hfocus
        · rename_i q0 env0 ty0 hat0 htyped
          cases hfocus
          exact htyped
        · cases hfocus
      have hcheck0 : Checker.check (sketchSigData c.expand s.app e.path).signature focus.env [] q' =
          .ok focus.ty := by
        rw [← Check.run_part_result]
        exact hres
      have hcheck : Checker.check (sketchSigData c.expand s.app e.path).signature focus.env e.path
          q' = .ok focus.ty := by
        have hr := Checker.check_rebase (sketchSigData c.expand s.app e.path).signature e.path
          focus.env [] q'
        rw [List.append_nil, hcheck0] at hr
        exact hr
      have hP : (Internal.place e.path (run (.part (sketchSigData c.expand s.app e.path) focus.env
          q'))).table = ⟨e.path, some (.env focus.env), some (.ok focus.ty)⟩ ::
            ((childTableAt (sketchSigData c.expand s.app e.path).signature (some (.env focus.env))
              (.eff q') e.path 0) ++ ((childTableAt (sketchSigData c.expand s.app e.path).signature
              (some (.env focus.env)) (.eff q') e.path 1) ++ (childTableAt
              (sketchSigData c.expand s.app e.path).signature (some (.env focus.env)) (.eff q')
              e.path 2))) := by
        rw [run_placed, Annotate.check_eq, tableAt_eq_cons]
        simp only [nodeAnswer, hcheck]
      obtain ⟨x, hrepc⟩ := Sketch.edit_replaceAt hedit
      have hkept : (!Table.belowSite c.sites e.path) = true := by
        unfold Sketch.sites
        rw [belowSite_at_eff (Node.replaceAt_spec hrepc).1]
        rfl
      have hatoms : ∀ (sites : List (List Nat)) (t : List Table.Entry),
          Table.atSource sites none t = t.filter (fun e => !Table.belowSite sites e.path) :=
        fun _ _ => rfl
      show Table.typedAt (Table.splice s.table e.path (Table.atSource c.sites
        c.program.firstRefFault (Internal.place e.path (run (.part (sketchSigData c.expand s.app
          e.path) focus.env q'))).table)) e.path = Table.typedAt s.table e.path
      rw [hcand c hedit, hatoms, hP,
        List.filter_cons_of_pos (p := fun (x : Table.Entry) => !Table.belowSite c.sites x.path)
          hkept,
        Table.typedAt_splice_at (x := ⟨e.path, some (.env focus.env), some (.ok focus.ty)⟩)
          (a := e.path) rfl, hold]
      unfold Table.typedAt
      rw [List.find?_cons, decide_eq_true (rfl : e.path = e.path)]
  | false =>
    obtain ⟨hr1, ty, hres', hview, htyped⟩ := recheck_keepExact_ok (hrec hagree)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr1
    refine ⟨?_, (htyped hne).symm, (fun ht => nomatch ht), fun _ => rfl⟩
    rw [view_type (recheck_coherent s c), hview]
    have hsc : c.sourceCheck s.app = .ok ty := hres'
    rw [hsc]
    rfl

/-- **A kept-exact feed below the root keeps the root's and the address's types, and splices
exactly where `canSplice` holds**, showing the next source program's addresses below the edited
path, in source order (copies inside an expanded reference are not source addresses). The
pointer of `source-feed-keep-exact`. The first form said a splice shows `[e.path]` alone; a
splice shows every address of the new subtree (`FeedCounterexample.feed_keepExact_delta_refuted`).
The feed's earlier splice of a candidate holding an ill-formed reference refuted the statement
(`git:84f88cf6f`, `feed_keepExact_refuted`); `canSplice` now refuses that splice.
`feed_keepExact_of_faultFree` proves its fault-free form. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
proof_goal feed_keepExact {o : Oracle} {s next : SourceSession} {e : Edit} {step : Edit.Step}
    (hc : s.Coherent) (hne : e.path ≠ [])
    (h : (s.feed o .keepExact e).value = .ok (next,step)) :
    next.view.type = s.view.type ∧
      Table.typedAt next.table e.path = Table.typedAt s.table e.path ∧
      (s.canSplice next.sketch e = true → step.delta =
        .spliced ((Node.addresses (.eff next.sketch.program)).filter (Table.under e.path))) ∧
      (s.canSplice next.sketch e = false → step.delta = .rechecked)

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

/-- **Undo**: an edit that applies, then the draft that puts back the old sub-program as written,
restores a coherent session exactly. The path lens's get-put (`replaceAt_spec`) restores the
sketch, a draft is never refused, and coherence fixes the table (`Coherent.ext`). The pointer of
`source-session-undo`. It is proved modulo `feed_coherent`. Its counterexample at the earlier
feed, a candidate holding an ill-formed reference (`git:d048b9a1b`, `feed_undo_refuted`), no
longer holds: `canSplice` refuses that splice. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem feed_undo {o : Oracle} {s next : SourceSession} {a : List Nat} {q old : NativeEff}
    {candidate : Sketch} {step : Edit.Step} (hc : s.Coherent)
    (hat : (Node.eff s.sketch.program).at_ a = some (.eff old))
    (hfill : s.sketch.fillAt a q = some candidate)
    (hnext : (s.feed o .draft (.fill a q)).value = .ok (next,step)) :
    ∃ back, (next.feed o .draft (.fill a old)).value = .ok (s,back) := by
  have hnc : next.Coherent := feed_coherent hc hnext
  obtain ⟨happ, -, -, hsk⟩ := feed_keeps hnext
  have hs1 : next.sketch = candidate := hsk candidate hfill
  obtain ⟨⟨b, back⟩, hv⟩ := feed_draft_ok o next (.fill a old)
  have hbc : b.Coherent := feed_coherent hnc hv
  obtain ⟨happ2, -, -, hsk2⟩ := feed_keeps hv
  have hback : next.sketch.edit next.app (.fill a old) = some s.sketch := by
    rw [hs1]
    obtain ⟨p', hrep, rfl⟩ := Sketch.fillAt_some hfill
    exact Sketch.fillAt_of_replaceAt ((Node.replaceAt_spec hrep).2.2 _ hat)
  have hb : b = s := Coherent.ext hbc hc (happ2.trans happ) (hsk2 _ hback)
  subst hb
  exact ⟨back, hv⟩

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

/-! ## The document's replay keeps coherence

Each action runs feeds in order (`DocInternal.apply`): a commit's batch, a draft, or a revert's
inverses. Each statement below is a step of `source-document-coherent`, proved modulo
`SourceSession.feed_coherent`, and names its consumer. -/

namespace DocInternal
open _root_.Effect4.Program.Check

/-- **A batch of feeds that each keep coherence keeps it.** A step of
`source-document-coherent`. Its consumer is `apply_coherent`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem batch_coherent {o : Oracle} {policy : FeedPolicy}
    (hfeed : ∀ {s next : SourceSession} {e : Edit} {step : Edit.Step}, s.Coherent →
      (s.feed o policy e).value = .ok (next, step) → next.Coherent) :
    ∀ (items : List (Place × Change)) (s : SourceSession) (idx : Nat) (fresh : Fresh),
      s.Coherent → (batch o policy s idx items).value = .ok fresh → fresh.session.Coherent
  | [], s, idx, fresh, hc, h => by
    simp only [batch, Checked.pure_value] at h
    cases h
    exact hc
  | (place, change) :: rest, s, idx, fresh, hc, h => by
    unfold batch at h
    split at h
    · cases h
    · split at h
      · cases h
      · rw [Checked.bind_value] at h
        split at h
        · cases h
        · rename_i next step hf
          rw [Checked.bind_value] at h
          split at h
          · cases h
          · rename_i later hlater
            rw [Checked.pure_value] at h
            cases h
            exact batch_coherent hfeed rest next (idx + 1) later (hfeed hc hf) hlater

/-- **A revert's inverses, each a feed that keeps coherence, keep it.** A step of
`source-document-coherent`. Its consumer is `apply_coherent`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem undoItems_coherent {o : Oracle} {policy : FeedPolicy}
    (hfeed : ∀ {s next : SourceSession} {e : Edit} {step : Edit.Step}, s.Coherent →
      (s.feed o policy e).value = .ok (next, step) → next.Coherent) :
    ∀ (items : List UndoItem) (s : SourceSession) (idx : Nat) (fresh : Fresh),
      s.Coherent → (undoItems o policy s idx items).value = .ok fresh → fresh.session.Coherent
  | [], s, idx, fresh, hc, h => by
    simp only [undoItems, Checked.pure_value] at h
    cases h
    exact hc
  | item :: rest, s, idx, fresh, hc, h => by
    unfold undoItems at h
    split at h
    · cases h
    · rw [Checked.bind_value] at h
      split at h
      · cases h
      · rename_i next step hf
        rw [Checked.bind_value] at h
        split at h
        · cases h
        · rename_i later hlater
          rw [Checked.pure_value] at h
          cases h
          exact undoItems_coherent hfeed rest next (idx + 1) later (hfeed hc hf) hlater

/-- **The sole interpreter keeps coherence**, modulo `SourceSession.feed_coherent`. A step of
`source-document-coherent`. Its consumer is `replayStep_coherent`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem apply_coherent {o : Oracle} {st : State} {a : DocAction} {fresh : Fresh}
    (hc : st.session.Coherent) (h : (apply o st a).value = .ok fresh) :
    fresh.session.Coherent := by
  unfold apply at h
  split at h
  · cases h
  · exact batch_coherent (fun hs hf => SourceSession.feed_coherent hs hf) _ _ _ _ hc h
  · rw [Checked.bind_value] at h
    split at h
    · cases h
    · rename_i next step hf
      rw [Checked.pure_value] at h
      cases h
      exact SourceSession.feed_coherent hc hf
  · split at h
    · cases h
    · exact undoItems_coherent (fun hs hf => SourceSession.feed_coherent hs hf) _ _ _ _ hc h

/-- One replay step keeps coherence. A step of `source-document-coherent`. Its consumer is
`foldl_replayStep_coherent`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem replayStep_coherent {x : Except (Nat × DocRefusal) State} {a : DocAction} {st : State}
    (hx : ∀ st, x = .ok st → st.session.Coherent)
    (h : (replayStep Oracle.uncached x a).value = .ok st) : st.session.Coherent := by
  cases x with
  | error why => cases h
  | ok prev =>
    change (advance prev (apply Oracle.uncached prev a).value) = .ok st at h
    cases happ : (apply Oracle.uncached prev a).value with
    | error why =>
      rw [happ] at h
      cases h
    | ok fresh =>
      rw [happ] at h
      cases h
      exact apply_coherent (hx prev rfl) happ

/-- A run of replay steps keeps coherence. A step of `source-document-coherent`. Its consumer
is `replayState_coherent`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem foldl_replayStep_coherent :
    ∀ (l : List DocAction) (x : Except (Nat × DocRefusal) State),
      (∀ st, x = .ok st → st.session.Coherent) → ∀ st,
      l.foldl (fun st a => (replayStep Oracle.uncached st a).value) x = .ok st →
      st.session.Coherent
  | [], _, hx, st, h => hx st h
  | _ :: l, _, hx, st, h =>
    foldl_replayStep_coherent l _ (fun _ h' => replayStep_coherent hx h') st h

/-- **Every replayed state is coherent**: the origin opens a coherent session
(`SourceSession.open_coherent`). A step of `source-document-coherent`. Its consumer is
`Doc.coherent`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem replayState_coherent (origin : DocOrigin) (history : List DocAction) (st : State)
    (h : replayState origin history = .ok st) : st.session.Coherent := by
  refine foldl_replayStep_coherent history _ ?_ st h
  intro st0 h0
  change (Except.ok ⟨(SourceSession.open Oracle.uncached origin.app origin.sketch).value, []⟩ :
    Except (Nat × DocRefusal) State) = .ok st0 at h0
  cases h0
  exact SourceSession.open_coherent _ _ _

/-- **A replay of drafts keeps the application, folds the edited sketch, and keeps coherence**,
modulo `SourceSession.feed_coherent`. A step of `source-session-draft-transport`. Its consumer is
`SourceSession.replay_drafts_view`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem replay_drafts_fold (app : SigApp) :
    ∀ (edits : List Edit) (st : State), st.session.Coherent → st.session.app = app →
      ∃ st', (edits.map DocAction.draft).foldl
          (fun x a => (replayStep Oracle.uncached x a).value) (.ok st) = .ok st' ∧
        st'.session.app = app ∧
        st'.session.sketch = edits.foldl (fun s e => (s.edit app e).getD s) st.session.sketch ∧
        st'.session.Coherent
  | [], st, hc, happ => ⟨st, rfl, happ, rfl, hc⟩
  | e :: rest, st, hc, happ => by
    obtain ⟨⟨next, step⟩, hv⟩ := SourceSession.feed_draft_ok Oracle.uncached st.session e
    have hstep : (replayStep Oracle.uncached (.ok st) (.draft e)).value =
        .ok ⟨next, st.entries ++ [⟨.draft, record next step⟩]⟩ := by
      show advance st (apply Oracle.uncached st (.draft e)).value = _
      simp only [apply, Checked.bind_value, hv, Checked.pure_value]
      rfl
    obtain ⟨happ', -, hnone, hsome⟩ := SourceSession.feed_keeps hv
    have hnc := SourceSession.feed_coherent hc hv
    obtain ⟨st', hfold, h1, h2, h3⟩ := replay_drafts_fold app rest
      ⟨next, st.entries ++ [⟨.draft, record next step⟩]⟩ hnc (happ'.trans happ)
    refine ⟨st', ?_, h1, ?_, h3⟩
    · simp only [List.map_cons, List.foldl_cons]
      rw [hstep]
      exact hfold
    · rw [h2]
      simp only [List.foldl_cons]
      congr 1
      rw [← happ]
      cases hed : st.session.sketch.edit st.session.app e with
      | none =>
        rw [hnone hed]
        rfl
      | some c =>
        rw [hsome c hed]
        rfl

end DocInternal

/-- **Every sealed document's session is coherent**: its runtime state is a replay of its
history (`Doc.replayedState`), and every replayed state is coherent. The pointer of
`source-document-coherent`. It is proved modulo `SourceSession.feed_coherent`, which is false
at head (`FeedCounterexample.keep_omit_refused`). Placement: initial-algebras-folds;
source-session-coherent's reachable-state obligation, R14. Consumer:
`SourceSession.reached_view`. This establishes no admission or progress claim. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Doc.coherent (d : Doc) : d.session.Coherent :=
  DocInternal.replayState_coherent d.origin d.history d.runtime d.replayedState

namespace SourceSession
open _root_.Effect4.Program.Check in
/-- The old draft-list reach, stated through the sole document replay.
Placement: source-session-coherent, initial-algebras-folds, R14.
This retains every old application, initial sketch, and edit list without a coherence premise.
Consumer: the draft case of Doc.coherent and transport of the old reached_view observation.
It establishes no admission, progress, or native behavior. It is proved modulo
`feed_coherent`. Its counterexample at the earlier feed (`git:d048b9a1b`,
`replay_drafts_view_refuted`) no longer holds: `canSplice` refuses that splice. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem replay_drafts_view (app : SigApp) (initial : Sketch) (edits : List Edit) (id : DocId) :
    ∃ session, replayDoc ⟨id,app,initial⟩ (edits.map DocAction.draft) = .ok session ∧
      session.app = app ∧
      session.sketch = edits.foldl (fun s e => (s.edit app e).getD s) initial ∧
      session.view.table = session.sketch.sourceTable app ∧
      session.view.refusals = session.sketch.sourceRefusals app ∧
      session.view.type = (session.sketch.sourceCheck app).toOption := by
  obtain ⟨st', hfold, happ, hsk, hc⟩ := DocInternal.replay_drafts_fold app edits
    ⟨(SourceSession.open Oracle.uncached app initial).value, []⟩
    (SourceSession.open_coherent _ _ _) rfl
  refine ⟨st'.session, ?_, happ, hsk, ?_⟩
  · have hstate : DocInternal.replayState ⟨id, app, initial⟩ (edits.map DocAction.draft) =
        .ok st' := hfold
    unfold replayDoc
    rw [hstate]
    rfl
  · have hv := SourceSession.view_eq hc
    rw [happ] at hv
    exact hv

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

Each statement below is a control, kernel-checked by evaluation (`decide`). Its placement names
the concept and no requirement. One verdict shows where a law stops at head: `keepOmitRefused`.
It fails to elaborate once the feed keeps an omission only at a typed root, and then it goes.
Two show why a first statement was restated, and they stay: `keepWide` and
`draftFaultyRechecks`.

Five more verdicts showed the splice of a candidate holding an ill-formed reference: `draftLate`,
`keepLate`, `docLate`, `replayLate` and `undoFaulty`, with the refutations of `feed_coherent`,
`feed_keepExact`, `Doc.coherent`, `replay_drafts_view` and `feed_undo` built on them
(`git:d048b9a1b:src/Effect4/Laws/Program/SourceTable.lean`). The feed now splices only where
`SourceSession.canSplice` holds, so each evaluates false and they are gone. -/

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

/-- The kept-exact fill of `wide` splices its whole subtree, so its delta lists three addresses. -/
def keepWide : Bool :=
  match (opened.feed Oracle.uncached .keepExact (.fill [0] wide)).value with
  | .ok (next, step) => !decide (step.delta = .spliced [[0]]) &&
      opened.expandedEditAgrees next.sketch (.fill [0] wide)
  | .error _ => false

/-- On the faulty base, a draft away from the reference rechecks: its root is refused. -/
def draftFaultyRechecks : Bool :=
  match (faultyOpened.feed Oracle.uncached .draft (.fill [1, 1] seven)).value with
  | .ok (_, step) => decide (step.delta = .rechecked)
  | .error _ => false

/-- A base with no reference whose root is refused: its second step performs row `0`, which the
hole table does not hold yet. -/
def refusedRoot : Sketch := ⟨.bind seven (.perform (.external 0) (.lit .unit)), []⟩

/-- The session the refused base opens. -/
def refusedOpened : SourceSession := (SourceSession.open Oracle.uncached {} refusedRoot).value

/-- The kept omission of `[0]` declares row `0`, which the second step names: the candidate's root
checks, but the splice keeps the refused root entry. -/
def keepOmitRefused : Bool :=
  match (refusedOpened.feed Oracle.uncached .keepExact (.omitAt [0] (Row.hole "h" .nat))).value with
  | .ok (next, _) => !decide (next.table = next.sketch.sourceTable next.app)
  | .error _ => false

set_option maxRecDepth 100000 in
/-- The evaluation of the three verdicts. -/
theorem verdicts : keepWide = true ∧ draftFaultyRechecks = true ∧ keepOmitRefused = true := by
  decide +kernel

end FeedCounterexample

open _root_.Effect4.Program.Check in
/-- **`SourceSession.feed_coherent` is false at head**: a kept
omission at a refused root declares the row that the refusal names, so the candidate's root
checks, while the splice keeps the refused root entry. A splice reads the root only where the
root is typed (`Sketch.table_more_holes`). A control of the claim `source-feed-coherent`. -/
@[semantics "initial-algebras-folds"]
theorem FeedCounterexample.keep_omit_refused :
    ¬ ∀ (o : Oracle) (policy : FeedPolicy) (s next : SourceSession) (e : Edit) (step : Edit.Step),
      s.Coherent → (s.feed o policy e).value = .ok (next, step) → next.Coherent := by
  intro h
  have hv := FeedCounterexample.verdicts.2.2
  unfold FeedCounterexample.keepOmitRefused at hv
  split at hv
  · rename_i next step heq
    have hcoh := h _ _ _ _ _ _ (SourceSession.open_coherent _ _ _) heq
    rw [Bool.not_eq_true', decide_eq_false_iff_not] at hv
    exact hv hcoh
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
  have hv := FeedCounterexample.verdicts.2.1
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
  have hv := FeedCounterexample.verdicts.1
  unfold FeedCounterexample.keepWide at hv
  split at hv
  · rename_i next step heq
    rw [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hv
    exact hv.1 (h _ _ _ (.fill [0] FeedCounterexample.wide) _ (SourceSession.open_coherent _ _ _)
      (List.cons_ne_nil 0 []) heq hv.2)
  · cases hv

end Effect4.Program
