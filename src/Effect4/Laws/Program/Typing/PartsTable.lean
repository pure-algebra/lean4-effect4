import Effect4.Program.Typing.PartsTable
import Effect4.Laws.Program.Sketch
import Effect4.Laws.Program.Typing.Splice
import Effect4.Laws.Program.Address
import Effect4.Laws.Auto.Semantics

/-!
# Laws.Program.Typing.PartsTable — a whole program's table is its parts' tables, and an edit in a part splices it

`Program/Typing/PartsTable.lean` computes a sketch's address table part by part
(`Sketch.annotate`). This module proves it equal to the table's specification (`Sketch.table`),
and lifts the splice law (`table_splice`, `Laws/Program/Typing/Splice.lean`) from a program with
no block to a whole program: an edit inside one part, at the part's type, splices the whole
table, the module check's root entry and the other parts included.

| Statement | In words |
| --- | --- |
| `Table.bodies_eq` | the bodies' spine's entries, read part by part, are the specification's |
| `Sketch.annotate_eq_table` | a sketch's table, part by part, is its table |
| `Table.bodies_splice` | an edit inside one body splices the spine's entries |
| `annotateModule_fill` | an edit inside one part splices a whole program's table |
| `Sketch.table_fill` | so a filling at a sketch's focus, of the focus's type, splices the sketch's table |

## Placement

Concept `initial-algebras-folds`; property: the address table is a fold, and a whole program's
fold is its parts' folds placed at their bases, so an edit inside a part changes only that part's
segment. Requirement R14 (program as data: regions, the focus, holes), under decisions rows 328,
333 and 334.

- **`module-annotate-table`** (claim, role compatibility; pointer `Sketch.annotate_eq_table`).
  Reach: every sketch and application, refused ones included; a block whose declarations and
  bodies differ in number. Not established: the cost, which no theorem counts. Consumer: the edit
  session over sketches, which opens and checks again with `Sketch.annotate`.
- **`module-table-splices`** (claim, role preservation; pointer `Sketch.table_fill`). Reach: a
  sketch that checks, an address below the root that `Sketch.focusAt` answers, and a filling of
  the focus's type in the focus's environment at the part's signature (`Sketch.sigAt`). Not
  established: an edit of the whole program at the root, which checks again; an edit that
  changes the type; layer references. Consumer: the edit session over sketches.
- Every other statement is a step of these two, and names its consumer.
-/

set_option autoImplicit false

namespace Effect4.Program

open Conform.Effect4.Typing

variable {Op : Type}

/-! ## The entries the specification reads -/

/-- **The entry of a part at an address**: the environment at `rest` from the part's root, and
the checker's answer there at the part's signature, located at the whole program's address `a`.
It is `Sketch.tableEntry`'s entry inside a part. -/
def Table.partEntry (part : Part Op) (rest a : List Nat) : Table.Entry :=
  let env := (Node.eff part.program).envAt part.sig (.env part.env) rest
  ⟨a, env, match (Node.eff part.program).at_ rest, env with
    | some (.eff q), some (.env tys) => some (Checker.check part.sig tys a q)
    | _, _ => none⟩

/-- **The entry of a block's bodies' spine at the spine address `r`**, standing at `base`: the
entry of the body that holds it, or no environment and no answer. -/
def Table.bodyEntry (sig : Signature Op) (decls : List DefDecl) (bodies : Effs Op)
    (base r : List Nat) : Table.Entry :=
  match Part.bodyAt sig decls bodies r with
  | some (part, rest) => Table.partEntry part rest (base ++ r)
  | none => ⟨base ++ r, none, none⟩

/-- **Whether a program is a definition block.** -/
def Eff.isBlock : Eff Op → Bool
  | .defs _ _ _ => true
  | _ => false

/-- **Whether a node is a program that is a definition block.** -/
def Node.isBlock : Node Op → Bool
  | .eff e => e.isBlock
  | _ => false

/-! ## Blocks -/

/-- A typed program is no block. A step of `module-table-splices`. Its consumer is
`annotateModule_fill_plain`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem HasTy.isBlock {s : Signature Op} {env : TyEnv} {e : Eff Op} {t : EffTy}
    (h : HasTy s env e t) : e.isBlock = false := by
  cases h <;> rfl

/-- A program that is no block is none of the block's constructor. A step of
`module-table-splices`. Its consumers are `annotateModule_plain` and `Eff.partAt_plain`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Eff.ne_defs_of_isBlock {e : Eff Op} (h : e.isBlock = false) :
    ∀ decls bodies main, e ≠ .defs decls bodies main := by
  intro decls bodies main he
  subst he
  cases h

/-- A program that is a block is one. A step of `module-table-splices`. Its consumer is
`annotateModule_fill`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Eff.eq_defs_of_isBlock {e : Eff Op} (h : e.isBlock = true) :
    ∃ decls bodies main, e = .defs decls bodies main := by
  unfold Eff.isBlock at h
  split at h
  · exact ⟨_, _, _, rfl⟩
  · cases h

/-- A child edit keeps whether a node is a block. A step of `module-table-splices`. Its consumer
is `Node.replaceAt_cons_isBlock`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Node.setChild_isBlock {node result r : Node Op} {i : Nat}
    (h : node.setChild i r = some result) : result.isBlock = node.isBlock := by
  unfold Node.setChild at h
  split at h <;> cases h <;> rfl

/-- An edit below the root keeps whether a node is a block. A step of `module-table-splices`.
Its consumer is `annotateModule_fill_plain`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Node.replaceAt_cons_isBlock {node result r : Node Op} {i : Nat} {rest : List Nat}
    (h : node.replaceAt (i :: rest) r = some result) : result.isBlock = node.isBlock := by
  simp only [Node.replaceAt] at h
  cases hc : node.child i with
  | none =>
    rw [hc] at h
    cases h
  | some c =>
    rw [hc, Option.bind_some] at h
    cases hr : c.replaceAt rest r with
    | none =>
      rw [hr] at h
      cases h
    | some c' =>
      rw [hr, Option.bind_some] at h
      exact Node.setChild_isBlock h

/-- A program that is no block is one part. A step of `module-table-splices`. Its consumer is
`annotateModule_fill`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Eff.partAt_plain {s : Signature Op} {env0 : TyEnv} {p : Eff Op}
    (h : p.isBlock = false) (path : List Nat) : p.partAt s env0 path = some (⟨s, env0, p⟩, path) := by
  unfold Eff.partAt
  split
  · cases h
  · rfl

/-- A program that is no block has `annotate`'s table. A step of `module-annotate-table` and of
`module-table-splices`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem annotateModule_plain {s : Signature Op} {root : Except TypeRefusal EffTy} {p : Eff Op}
    (h : p.isBlock = false) : annotateModule s root p = annotate s [] p := by
  unfold annotateModule
  split
  · cases h
  · rfl

/-- An edit of a block's main program. A step of `module-table-splices`. Its consumer is
`annotateModule_fill_main`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Node.replaceAt_defs_main {decls : List DefDecl} {bodies : Effs Op} {main p' q' : Eff Op}
    {r : List Nat} (h : (Node.eff (.defs decls bodies main)).replaceAt (1 :: r) (.eff q') = some (.eff p')) :
    ∃ main', (Node.eff main).replaceAt r (.eff q') = some (.eff main') ∧ p' = .defs decls bodies main' := by
  simp only [Node.replaceAt, Node.child, Option.bind_some] at h
  cases hr : (Node.eff main).replaceAt r (.eff q') with
  | none =>
    rw [hr] at h
    cases h
  | some c =>
    rw [hr, Option.bind_some] at h
    cases c
    case eff x =>
      cases h
      exact ⟨x, rfl, rfl⟩
    all_goals cases h

/-- An edit of a block's bodies. A step of `module-table-splices`. Its consumer is
`annotateModule_fill_body`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Node.replaceAt_defs_body {decls : List DefDecl} {bodies : Effs Op} {main p' q' : Eff Op}
    {r : List Nat} (h : (Node.eff (.defs decls bodies main)).replaceAt (0 :: r) (.eff q') = some (.eff p')) :
    ∃ bodies', (Node.effs bodies).replaceAt r (.eff q') = some (.effs bodies') ∧
      p' = .defs decls bodies' main := by
  simp only [Node.replaceAt, Node.child, Option.bind_some] at h
  cases hr : (Node.effs bodies).replaceAt r (.eff q') with
  | none =>
    rw [hr] at h
    cases h
  | some c =>
    rw [hr, Option.bind_some] at h
    cases c
    case effs x =>
      cases h
      exact ⟨x, rfl, rfl⟩
    all_goals cases h

/-! ## The table, part by part -/

/-- An address is under itself. A step of `module-table-splices`. Its consumers are
`Table.bodies_mem_under` and `Table.bodies_splice`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Table.under_self (a : List Nat) : Table.under a a = true := by
  have h := Table.under_append a []
  rwa [List.append_nil] at h

/-- The spine's own node has no part. A step of `module-annotate-table`. Its consumer is
`Table.bodies_eq`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Table.bodyEntry_nil (sig : Signature Op) (decls : List DefDecl) (bodies : Effs Op)
    (base : List Nat) : Table.bodyEntry sig decls bodies base [] = ⟨base, none, none⟩ := by
  have h : Part.bodyAt sig decls bodies [] = none := by cases decls <;> cases bodies <;> rfl
  simp only [Table.bodyEntry, h, List.append_nil]

/-- With no declaration, the spine holds no part. A step of `module-annotate-table`. Its consumer
is `Table.bodies_eq`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Table.bodyEntry_nodecl (sig : Signature Op) (bodies : Effs Op) (base : List Nat) :
    Table.bodyEntry sig [] bodies base = fun r => ⟨base ++ r, none, none⟩ := rfl

/-- The spine's head body is a part at its base. A step of `module-annotate-table`. Its consumer
is `Table.bodies_eq`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Table.bodyEntry_head (sig : Signature Op) (d : DefDecl) (ds : List DefDecl) (body : Eff Op)
    (rest : Effs Op) (base b : List Nat) :
    Table.bodyEntry sig (d :: ds) (.cons body rest) base (0 :: b) =
      tableEntryAt sig (some (.env [d.request.normalize])) (.eff body) (base ++ [0]) b := by
  simp only [Table.bodyEntry, Part.bodyAt, tableEntryAt, Table.partEntry, List.append_assoc,
    List.singleton_append, Option.bind_some]
  rfl

/-- The spine's tail is the spine of the rest, one step further. A step of
`module-annotate-table`. Its consumer is `Table.bodies_eq`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Table.bodyEntry_tail (sig : Signature Op) (d : DefDecl) (ds : List DefDecl) (body : Eff Op)
    (rest : Effs Op) (base b : List Nat) :
    Table.bodyEntry sig (d :: ds) (.cons body rest) base (1 :: b) =
      Table.bodyEntry sig ds rest (base ++ [1]) b := by
  simp only [Table.bodyEntry, Part.bodyAt, List.append_assoc, List.singleton_append]

/-- **The bodies' spine, part by part, is the specification's.** A step of
`module-annotate-table`. Its consumer is `Sketch.annotate_eq_table`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Table.bodies_eq (sig : Signature Op) (decls : List DefDecl) (bodies : Effs Op)
    (base : List Nat) :
    (Node.addresses (.effs bodies)).map (Table.bodyEntry sig decls bodies base) =
      Table.bodies sig decls bodies base := by
  match decls, bodies with
  | ds, .nil =>
    rw [Node.addresses_eq_cons]
    have h : Table.bodies sig ds .nil base = [⟨base, none, none⟩] := by cases ds <;> rfl
    rw [h]
    simp only [Node.childAddresses, Node.child, List.append_nil, List.map_cons, List.map_nil,
      Table.bodyEntry_nil]
  | [], .cons body rest =>
    rw [Node.addresses_eq_cons]
    simp only [Node.childAddresses, Node.child, List.append_nil, List.map_cons, List.map_append,
      List.map_map, Table.bodyEntry_nil]
    simp only [Table.bodies, ← Table.bodies_eq sig [] rest (base ++ [1]), Function.comp_def,
      Table.bodyEntry_nodecl, List.append_assoc, List.singleton_append]
  | d :: ds, .cons body rest =>
    rw [Node.addresses_eq_cons]
    simp only [Node.childAddresses, Node.child, List.append_nil, List.map_cons, List.map_append,
      List.map_map, Table.bodyEntry_nil]
    simp only [Table.bodies, ← Table.bodies_eq sig ds rest (base ++ [1]), Annotate.check_eq, tableAt,
      Function.comp_def, Table.bodyEntry_head, Table.bodyEntry_tail]

/-- **A sketch's table, part by part, is its table.** The pointer of `module-annotate-table`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Sketch.annotate_eq_table (s : Sketch) (app : SigApp) : s.annotate app = s.table app := by
  unfold Sketch.annotate Sketch.table
  cases hb : s.program.isBlock
  · rw [annotateModule_plain hb, Program.annotate_eq_table]
    unfold Program.table
    apply List.map_congr_left
    intro a _
    cases a with
    | nil =>
      simp only [Sketch.tableEntry, Sketch.check, checkModule_eq_check _ (Eff.ne_defs_of_isBlock hb)]
      rfl
    | cons i r =>
      simp only [Sketch.tableEntry, Eff.partAt_plain hb]
      generalize (Node.eff s.program).at_ (i :: r) = x
      generalize Node.envAt (app.withHoles s.holes).signature (NodeEnv.env []) (Node.eff s.program)
        (i :: r) = y
      rcases x with _ | (_ | _ | _ | _ | _ | _ | _) <;> rcases y with _ | (_ | _ | _) <;> rfl
  · obtain ⟨decls, bodies, main, hp⟩ := Eff.eq_defs_of_isBlock hb
    rw [hp]
    simp only [annotateModule]
    rw [Node.addresses_eq_cons]
    simp only [Node.childAddresses, Node.child, List.append_nil, List.map_cons, List.map_append,
      List.map_map]
    rw [← Table.bodies_eq, Annotate.check_eq]
    unfold tableAt
    congr 1
    congr 1
    · apply List.map_congr_left
      intro r _
      simp only [Function.comp_def, Sketch.tableEntry, hp, Eff.partAt, Table.bodyEntry,
        Table.partEntry, List.singleton_append]
      generalize Part.bodyAt ((app.withHoles s.holes).signature.withDefs decls) decls bodies r = o
      rcases o with _ | ⟨part, rest⟩
      · rfl
      · dsimp only
        generalize (Node.eff part.program).at_ rest = x
        generalize Node.envAt part.sig (NodeEnv.env part.env) (Node.eff part.program) rest = y
        rcases x with _ | (_ | _ | _ | _ | _ | _ | _) <;> rcases y with _ | (_ | _ | _) <;> rfl
    · apply List.map_congr_left
      intro r _
      simp only [Function.comp_def, Sketch.tableEntry, hp, Eff.partAt, tableEntryAt,
        Option.bind_some, List.singleton_append]
      generalize (Node.eff main).at_ r = x
      generalize Node.envAt ((app.withHoles s.holes).signature.withDefs decls) (NodeEnv.env [])
        (Node.eff main) r = y
      rcases x with _ | (_ | _ | _ | _ | _ | _ | _) <;> rcases y with _ | (_ | _ | _) <;> rfl

/-! ## An edit inside a part -/

/-- Every entry of the bodies' spine stands under its base. A step of `module-table-splices`. Its
consumers are `annotateModule_fill_main` and `Table.bodies_splice`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Table.bodies_under (sig : Signature Op) (decls : List DefDecl) (bodies : Effs Op)
    (base : List Nat) : ∀ e ∈ Table.bodies sig decls bodies base, ∃ x, e.path = base ++ x := by
  match decls, bodies with
  | ds, .nil =>
    intro e he
    have h : Table.bodies sig ds .nil base = [⟨base, none, none⟩] := by cases ds <;> rfl
    rw [h, List.mem_singleton] at he
    subst he
    exact ⟨[], (List.append_nil base).symm⟩
  | [], .cons body rest =>
    intro e he
    simp only [Table.bodies, List.mem_cons, List.mem_append, List.mem_map] at he
    rcases he with rfl | ⟨r, -, rfl⟩ | he
    · exact ⟨[], (List.append_nil base).symm⟩
    · exact ⟨0 :: r, rfl⟩
    · obtain ⟨x, hx⟩ := Table.bodies_under sig [] rest (base ++ [1]) e he
      exact ⟨[1] ++ x, by rw [hx, List.append_assoc]⟩
  | d :: ds, .cons body rest =>
    intro e he
    simp only [Table.bodies, List.mem_cons, List.mem_append] at he
    rcases he with rfl | he | he
    · exact ⟨[], (List.append_nil base).symm⟩
    · rw [Annotate.check_eq] at he
      obtain ⟨b, hb⟩ := tableAt_path he
      exact ⟨[0] ++ b, by rw [hb, List.append_assoc]⟩
    · obtain ⟨x, hx⟩ := Table.bodies_under sig ds rest (base ++ [1]) e he
      exact ⟨[1] ++ x, by rw [hx, List.append_assoc]⟩

/-- The spine holds an entry at every address of a body's part. A step of
`module-table-splices`. Its consumer is `annotateModule_fill_body`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Table.bodies_mem_under {sig : Signature Op} {decls : List DefDecl} {bodies : Effs Op}
    {r rest : List Nat} {part : Part Op} {x : Node Op} (base : List Nat)
    (hbody : Part.bodyAt sig decls bodies r = some (part, rest))
    (hat : (Node.eff part.program).at_ rest = some x) :
    ∃ e ∈ Table.bodies sig decls bodies base, Table.under (base ++ r) e.path = true := by
  have hpath : (Node.effs bodies).at_ r = some x := (Part.bodyAt_at hbody).trans hat
  have hmem : r ∈ Node.addresses (.effs bodies) := (mem_addresses_iff _ _).mpr (by rw [hpath]; rfl)
  refine ⟨Table.bodyEntry sig decls bodies base r, ?_, ?_⟩
  · rw [← Table.bodies_eq]
    exact List.mem_map_of_mem hmem
  · simp only [Table.bodyEntry, hbody]
    exact Table.under_self _

/-- An edit of the spine's head body. A step of `module-table-splices`. Its consumer is
`Table.bodies_splice`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Node.replaceAt_effs_head {body q' : Eff Op} {rest bodies' : Effs Op} {r : List Nat}
    (h : (Node.effs (.cons body rest)).replaceAt (0 :: r) (.eff q') = some (.effs bodies')) :
    ∃ body', (Node.eff body).replaceAt r (.eff q') = some (.eff body') ∧
      bodies' = .cons body' rest := by
  simp only [Node.replaceAt, Node.child, Option.bind_some] at h
  cases hr : (Node.eff body).replaceAt r (.eff q') with
  | none =>
    rw [hr] at h
    cases h
  | some c =>
    rw [hr, Option.bind_some] at h
    cases c
    case eff x =>
      cases h
      exact ⟨x, rfl, rfl⟩
    all_goals cases h

/-- An edit of the spine's tail. A step of `module-table-splices`. Its consumer is
`Table.bodies_splice`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Node.replaceAt_effs_tail {body q' : Eff Op} {rest bodies' : Effs Op} {r : List Nat}
    (h : (Node.effs (.cons body rest)).replaceAt (1 :: r) (.eff q') = some (.effs bodies')) :
    ∃ rest', (Node.effs rest).replaceAt r (.eff q') = some (.effs rest') ∧
      bodies' = .cons body rest' := by
  simp only [Node.replaceAt, Node.child, Option.bind_some] at h
  cases hr : (Node.effs rest).replaceAt r (.eff q') with
  | none =>
    rw [hr] at h
    cases h
  | some c =>
    rw [hr, Option.bind_some] at h
    cases c
    case effs x =>
      cases h
      exact ⟨x, rfl, rfl⟩
    all_goals cases h

/-- **An edit inside one body splices the spine's entries.** A step of `module-table-splices`.
Its consumer is `annotateModule_fill_body`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Table.bodies_splice {sig : Signature Op} {decls : List DefDecl} {bodies bodies' : Effs Op}
    {r rest : List Nat} {part : Part Op} {q' : Eff Op} {t : EffTy} {f : Focus Op} (base : List Nat)
    (hbody : Part.bodyAt sig decls bodies r = some (part, rest))
    (ht : HasTy part.sig part.env part.program t)
    (hf : focusAt part.sig part.env part.program rest = some f) (hq' : HasTy part.sig f.env q' f.ty)
    (hrep : (Node.effs bodies).replaceAt r (.eff q') = some (.effs bodies')) :
    Table.bodies sig decls bodies' base =
      Table.splice (Table.bodies sig decls bodies base) (base ++ r)
        (tableAt part.sig (some (.env f.env)) (.eff q') (base ++ r)) := by
  match decls, bodies, r, hbody, hrep with
  | d :: ds, .cons body rest, 0 :: r0, hbody, hrep =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hbody)
    obtain ⟨body', hb', rfl⟩ := Node.replaceAt_effs_head hrep
    have ht' : HasTy sig [d.request.normalize] body t := ht
    obtain ⟨hat, henv, hty⟩ := focusAt_eq_some.mp hf
    have hat' : (Node.eff body).at_ r0 = some (.eff f.program) := hat
    have hsp : tableAt sig (some (.env [d.request.normalize])) (.eff body') (base ++ [0]) =
        Table.splice (tableAt sig (some (.env [d.request.normalize])) (.eff body) (base ++ [0]))
          (base ++ 0 :: r0) (tableAt sig (some (.env f.env)) (.eff q') (base ++ 0 :: r0)) := by
      have h := tableAt_splice r0 (NodeHasTy.eff ht') hat henv (effTy_sound _ _ _ _ hty) hq' hb'
        (pre := base ++ [0])
      rw [List.append_assoc, List.singleton_append] at h
      exact h
    simp only [Table.bodies, Annotate.check_eq]
    rw [hsp]
    have hX : ∀ e ∈ [(⟨base, none, none⟩ : Table.Entry)], Table.under (base ++ 0 :: r0) e.path = false := by
      intro e he
      rw [List.mem_singleton] at he
      subst he
      exact Table.under_prefix_false base r0 0
    obtain ⟨e, he, hpe⟩ := tableAt_mem_path (s := sig) (ctx := some (.env [d.request.normalize]))
      (pre := base ++ [0]) hat'
    have hY : ∃ e ∈ tableAt sig (some (.env [d.request.normalize])) (.eff body) (base ++ [0]),
        Table.under (base ++ 0 :: r0) e.path = true := by
      refine ⟨e, he, ?_⟩
      rw [hpe, List.append_assoc, List.singleton_append]
      exact Table.under_self _
    have hZ : ∀ e ∈ Table.bodies sig ds rest (base ++ [1]),
        Table.under (base ++ 0 :: r0) e.path = false := by
      intro e he
      obtain ⟨x, hx⟩ := Table.bodies_under _ _ _ _ e he
      rw [hx, List.append_assoc, List.singleton_append]
      exact Table.under_sibling_false base r0 x (by decide)
    exact (Table.splice_three hX hY hZ).symm
  | d :: ds, .cons body rest, 1 :: r1, hbody, hrep =>
    obtain ⟨rest', hr', rfl⟩ := Node.replaceAt_effs_tail hrep
    have ih := Table.bodies_splice (decls := ds) (bodies := rest) (r := r1) (base ++ [1]) hbody ht hf
      hq' hr'
    rw [List.append_assoc, List.singleton_append] at ih
    simp only [Table.bodies]
    rw [ih]
    have hX : ∀ e ∈ (⟨base, none, none⟩ :: (Annotate.check sig [d.request.normalize] (base ++ [0]) body).1 :
        List Table.Entry),
        Table.under (base ++ 1 :: r1) e.path = false := by
      intro e he
      rcases List.mem_cons.mp he with he | he
      · subst he
        exact Table.under_prefix_false base r1 1
      · rw [Annotate.check_eq] at he
        obtain ⟨b, hb⟩ := tableAt_path he
        rw [hb, List.append_assoc, List.singleton_append]
        exact Table.under_sibling_false base r1 b (by decide)
    have h := Table.splice_append_out_left (Y := Table.bodies sig ds rest (base ++ [1]))
      (sub := tableAt part.sig (some (.env f.env)) (.eff q') (base ++ 1 :: r1)) hX
    simp only [List.cons_append] at h
    exact h.symm
  | _ :: _, .cons _ _, [], hbody, _ => cases hbody
  | _ :: _, .cons _ _, (_ + 2) :: _, hbody, _ => cases hbody
  | [], .cons _ _, _, hbody, _ => cases hbody
  | ds, .nil, r, hbody, _ =>
    have hnone : Part.bodyAt sig ds .nil r = none := by
      rcases ds with _ | ⟨d, ds⟩ <;> rcases r with _ | ⟨_ | _ | i, r⟩ <;> rfl
    rw [hnone] at hbody
    cases hbody

/-- **An edit inside a program with no block splices its table.** The splice law, through
`annotate`. A step of `module-table-splices`. Its consumer is `annotateModule_fill`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem annotateModule_fill_plain {s : Signature Op} {p p' q' : Eff Op} {T : EffTy}
    {path : List Nat} {f : Focus Op} (hb : p.isBlock = false) (hp : Checker.checkModule s p = .ok T)
    (hf : focusAt s [] p path = some f) (hq' : HasTy s f.env q' f.ty)
    (hrep : (Node.eff p).replaceAt path (.eff q') = some (.eff p')) :
    annotateModule s (.ok T) p' =
      Table.splice (annotateModule s (.ok T) p) path (tableAt s (some (.env f.env)) (.eff q') path) := by
  have hb' : p'.isBlock = false := by
    cases path with
    | nil =>
      have hsame : Node.eff p' = Node.eff q' := Option.some.inj
        (hrep.symm.trans (by simp only [Node.replaceAt]; rfl))
      cases hsame
      exact HasTy.isBlock hq'
    | cons i rest => exact (Node.replaceAt_cons_isBlock hrep).trans hb
  rw [annotateModule_plain hb, annotateModule_plain hb', annotate_eq_table, annotate_eq_table]
  rw [checkModule_eq_check s (Eff.ne_defs_of_isBlock hb)] at hp
  exact table_splice (check_sound s p [] [] T hp) hf hq' hrep

/-- **An edit inside a block's main program splices the whole table.** The splice law at the
main program's base `[1]`. A step of `module-table-splices`. Its consumer is
`annotateModule_fill`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem annotateModule_fill_main {s : Signature Op} {decls : List DefDecl} {bodies : Effs Op}
    {main p' q' : Eff Op} {T : EffTy} {r : List Nat} {f : Focus Op}
    (hp : Checker.checkModule s (.defs decls bodies main) = .ok T)
    (hf : focusAt (s.withDefs decls) [] main r = some f)
    (hq' : HasTy (s.withDefs decls) f.env q' f.ty)
    (hrep : (Node.eff (.defs decls bodies main)).replaceAt (1 :: r) (.eff q') = some (.eff p')) :
    annotateModule s (.ok T) p' =
      Table.splice (annotateModule s (.ok T) (.defs decls bodies main)) (1 :: r)
        (tableAt (s.withDefs decls) (some (.env f.env)) (.eff q') (1 :: r)) := by
  obtain ⟨main', hmain, rfl⟩ := Node.replaceAt_defs_main hrep
  obtain ⟨t, ht⟩ := moduleHasTy_partAt_typed (checkModule_sound _ _ _ hp)
    (show (Eff.defs decls bodies main).partAt s [] (1 :: r) = some (⟨s.withDefs decls, [], main⟩, r)
      from rfl)
  have ht' : HasTy (s.withDefs decls) [] main t := ht
  obtain ⟨hat, henv, hty⟩ := focusAt_eq_some.mp hf
  have hsplice : tableAt (s.withDefs decls) (some (.env [])) (.eff main') [1] =
      Table.splice (tableAt (s.withDefs decls) (some (.env [])) (.eff main) [1]) (1 :: r)
        (tableAt (s.withDefs decls) (some (.env f.env)) (.eff q') (1 :: r)) :=
    tableAt_splice r (NodeHasTy.eff ht') hat henv (effTy_sound _ _ _ _ hty) hq' hmain (pre := [1])
  simp only [annotateModule, Annotate.check_eq]
  rw [hsplice]
  have hX : ∀ e ∈ (⟨[], some (.env []), some (.ok T)⟩ :: Table.bodies (s.withDefs decls) decls bodies [0]),
      Table.under (1 :: r) e.path = false := by
    intro e he
    rcases List.mem_cons.mp he with he | he
    · subst he
      rfl
    · obtain ⟨b, hb⟩ := Table.bodies_under _ _ _ _ e he
      rw [hb]
      exact Table.under_sibling_false [] r b (by decide)
  rw [← List.cons_append, ← List.cons_append, Table.splice_append_out_left hX]

/-- **An edit inside one of a block's bodies splices the whole table.** A step of
`module-table-splices`. Its consumer is `annotateModule_fill`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem annotateModule_fill_body {s : Signature Op} {decls : List DefDecl} {bodies : Effs Op}
    {main p' q' : Eff Op} {T : EffTy} {r rest : List Nat} {part : Part Op} {f : Focus Op}
    (hp : Checker.checkModule s (.defs decls bodies main) = .ok T)
    (hpart : Part.bodyAt (s.withDefs decls) decls bodies r = some (part, rest))
    (hf : focusAt part.sig part.env part.program rest = some f) (hq' : HasTy part.sig f.env q' f.ty)
    (hrep : (Node.eff (.defs decls bodies main)).replaceAt (0 :: r) (.eff q') = some (.eff p')) :
    annotateModule s (.ok T) p' =
      Table.splice (annotateModule s (.ok T) (.defs decls bodies main)) (0 :: r)
        (tableAt part.sig (some (.env f.env)) (.eff q') (0 :: r)) := by
  obtain ⟨bodies', hb, rfl⟩ := Node.replaceAt_defs_body hrep
  obtain ⟨t, ht⟩ := moduleHasTy_partAt_typed (checkModule_sound _ _ _ hp)
    (show (Eff.defs decls bodies main).partAt s [] (0 :: r) = some (part, rest) from hpart)
  have hsplice := Table.bodies_splice [0] hpart ht hf hq' hb
  obtain ⟨hat, -, -⟩ := focusAt_eq_some.mp hf
  have hY := Table.bodies_mem_under [0] hpart hat
  simp only [annotateModule]
  rw [hsplice]
  have hX : ∀ e ∈ [(⟨[], some (.env []), some (.ok T)⟩ : Table.Entry)],
      Table.under (0 :: r) e.path = false := by
    intro e he
    rw [List.mem_singleton] at he
    subst he
    rfl
  have hZ : ∀ e ∈ (Annotate.check (s.withDefs decls) [] [1] main).1,
      Table.under (0 :: r) e.path = false := by
    intro e he
    rw [Annotate.check_eq] at he
    obtain ⟨b, hb⟩ := tableAt_path he
    rw [hb]
    exact Table.under_sibling_false [] r b (by decide)
  have h3 := Table.splice_three (sub := tableAt part.sig (some (.env f.env)) (.eff q') (0 :: r))
    hX hY hZ
  exact h3.symm

/-- **An edit inside one part splices a whole program's table**: the part's own table is spliced
at its base, and the root's entry and the other parts' entries stay. A step of
`module-table-splices`. Its consumer is `Sketch.table_fill`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem annotateModule_fill {s : Signature Op} {p p' q' : Eff Op} {T : EffTy} {path rest : List Nat}
    {part : Part Op} {f : Focus Op} (hp : Checker.checkModule s p = .ok T)
    (hpart : p.partAt s [] path = some (part, rest))
    (hf : focusAt part.sig part.env part.program rest = some f) (hq' : HasTy part.sig f.env q' f.ty)
    (hrep : (Node.eff p).replaceAt path (.eff q') = some (.eff p')) :
    annotateModule s (.ok T) p' =
      Table.splice (annotateModule s (.ok T) p) path
        (tableAt part.sig (some (.env f.env)) (.eff q') path) := by
  cases hb : p.isBlock
  · rw [Eff.partAt_plain hb, Option.some.injEq, Prod.mk.injEq] at hpart
    obtain ⟨rfl, rfl⟩ := hpart
    exact annotateModule_fill_plain hb hp hf hq' hrep
  · obtain ⟨decls, bodies, main, rfl⟩ := Eff.eq_defs_of_isBlock hb
    match path, hpart with
    | 0 :: r, hpart => exact annotateModule_fill_body hp hpart hf hq' hrep
    | 1 :: r, hpart =>
      cases hpart
      exact annotateModule_fill_main hp hf hq' hrep
    | [], hpart => cases hpart
    | (_ + 2) :: _, hpart => cases hpart

/-! ## A sketch -/

/-- A filling replaces the program and keeps the hole table. A step of `module-table-splices`.
Its consumer is `Sketch.table_fill`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Sketch.fillAt_some {s s' : Sketch} {path : List Nat} {q' : NativeEff}
    (h : s.fillAt path q' = some s') :
    ∃ p', (Node.eff s.program).replaceAt path (.eff q') = some (.eff p') ∧
      s' = { s with program := p' } := by
  unfold Sketch.fillAt at h
  cases hr : (Node.eff s.program).replaceAt path (.eff q') with
  | none =>
    rw [hr] at h
    cases h
  | some n =>
    rw [hr] at h
    cases n
    case eff p' =>
      cases h
      exact ⟨p', rfl, rfl⟩
    all_goals cases h

/-- A filling of the focus's type keeps the sketch's type. A step of `module-table-splices`. Its
consumer is `Sketch.table_fill`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Sketch.check_fill_kept {s : Sketch} {app : SigApp} {T : EffTy} {path : List Nat}
    {f : Focus NativeOp} {q' p' : NativeEff} (hs : s.check app = .ok T)
    (hf : s.focusAt app path = some f) (hq' : HasTy (s.sigAt app path) f.env q' f.ty)
    (hrep : (Node.eff s.program).replaceAt path (.eff q') = some (.eff p')) :
    ({ s with program := p' } : Sketch).check app = .ok T := by
  have hs0 : ({ s with holes := s.holes ++ [] } : Sketch) = s := by
    cases s
    simp only [List.append_nil]
  obtain ⟨s'', hfill, hcheck⟩ := Sketch.check_fill_focusAt s app hs hf [] (q' := q') (pq := path)
    (by rw [hs0]; exact check_complete _ q' _ _ hq' path)
  rw [hs0, Sketch.fillAt_of_replaceAt hrep, Option.some.injEq] at hfill
  rw [hfill]
  exact hcheck

/-- **A filling at a sketch's focus, of the focus's type, splices the sketch's table.** Below
the root, in the part that holds the address, at the part's signature: the root's entry holds
the same check, the other parts' entries stay, and the part's segment is the splice law's. The
pointer of `module-table-splices`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Sketch.table_fill {s s' : Sketch} {app : SigApp} {T : EffTy} {path : List Nat}
    {f : Focus NativeOp} {q' : NativeEff} (hs : s.check app = .ok T) (hnil : path ≠ [])
    (hf : s.focusAt app path = some f) (hq' : HasTy (s.sigAt app path) f.env q' f.ty)
    (hfill : s.fillAt path q' = some s') :
    s'.table app = Table.splice (s.table app) path
      (tableAt (s.sigAt app path) (some (.env f.env)) (.eff q') path) := by
  obtain ⟨p', hrep, rfl⟩ := Sketch.fillAt_some hfill
  have hs' := Sketch.check_fill_kept hs hf hq' hrep
  obtain ⟨i, r, rfl⟩ := List.exists_cons_of_ne_nil hnil
  obtain ⟨⟨part, rest⟩, hpart, hfp⟩ := Option.bind_eq_some_iff.mp hf
  rw [Sketch.sigAt_part hpart] at hq' ⊢
  rw [← Sketch.annotate_eq_table, ← Sketch.annotate_eq_table]
  unfold Sketch.annotate
  rw [hs, hs']
  exact annotateModule_fill hs hpart hfp hq' hrep

end Effect4.Program
