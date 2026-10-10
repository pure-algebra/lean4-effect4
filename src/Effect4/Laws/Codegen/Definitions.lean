import Effect4.Laws.Codegen.ReadLeaf
import Effect4.Laws.Program.Definitions

/-!
# Laws.Codegen.Definitions — the spelling map of a definition block

A module with a definition block is read at the block's signature (`Signature.withDefs`),
through the block's spelling map (`defsSpell`): a definition's name spells its invocation, and
every other spelling is the signature's own (decisions row 328, slice PROC-3). The read laws
`read_print` and `read_exact` hold at any lawful spelling (`LawfulSpelling`), so they reach a
block's bodies and its main program once the block's spelling is lawful. This module states
when it is: `LawfulSpelling.withDefs`.

What the signature owes is `LawfulCalls`: `call k` is the invocation of definition `k`, an
invocation is its own face, the two updates of an operation keep its definition, and the
signature's own spelling names no invocation. What the block owes is `DefsNamed`: its names are
distinct, no row spells one, and none is a binder or a reserved head. The native signature
meets the first (`nativeCalls`); the module printer's name check gives the second.

Placement: concept `exact-codecs`, claim `module-defs-round-trip` (R8). Consumers: the module
round trip on the readable domain (`Laws/Api/ModuleReadable.lean`). Nothing here says that
tsgo accepts a printed block or how rc.112 runs it.
-/

set_option autoImplicit false

namespace Effect4.Program

variable {Op : Type}

/-- What a signature's invocations owe a block's spelling map. `call k` invokes definition `k`;
an invocation is its own face; replacing an operation's term or its type arguments keeps the
definition it invokes; and the signature's own spelling map answers no invocation. -/
structure LawfulCalls (sig : Signature Op) (spell : String → List RowArg → Option Op)
    (call : Nat → Op) : Prop where
  callOf_call : ∀ k, sig.callOf (call k) = some k
  face_call : ∀ op k, sig.callOf op = some k → sig.face op = call k
  callOf_withTerm : ∀ op f, sig.callOf (sig.withTerm op f) = sig.callOf op
  callOf_withTypeArgs : ∀ op tys, sig.callOf (sig.withTypeArgs op tys) = sig.callOf op
  spell_plain : ∀ s names op, spell s names = some op → sig.callOf op = none

/-- The names of a block that its spelling map reads back: distinct, spelled by no row of the
signature, no printed binder and no reserved head. -/
structure DefsNamed (spell : String → List RowArg → Option Op) (defs : List DefDecl) :
    Prop where
  distinct : (defs.map (·.name)).Nodup
  unspelled : ∀ d ∈ defs, ∀ names, spell d.name names = none
  notBinder : ∀ d ∈ defs, ∀ i, d.name ≠ Var.name i
  notReserved : ∀ d ∈ defs, d.name ∉ reserved

/-- An invocation of a definition the block lacks reads the signature's own row. A step of
`LawfulSpelling.withDefs`. -/
theorem withDefs_rowOf_out (sig : Signature Op) (defs : List DefDecl) {op : Op} {k : Nat}
    (h : sig.callOf op = some k) (hd : defs[k]? = none) :
    (sig.withDefs defs).rowOf op = sig.rowOf op := by
  simp only [Signature.withDefs, h, hd]

/-- A distinct name's first index is its own. (The core lemma `List.findIdx?_eq_some_iff_getElem`
brings `Classical.choice`; this induction does not.) -/
theorem findIdx_name : ∀ {defs : List DefDecl}, (defs.map (·.name)).Nodup →
    ∀ {k : Nat} (hk : k < defs.length), defs.findIdx? (·.name == defs[k].name) = some k
  | [], _, k, hk => absurd hk (Nat.not_lt_zero k)
  | d :: ds, distinct, k, hk => by
    rw [List.findIdx?_cons]
    obtain ⟨notIn, rest⟩ := List.nodup_cons.mp distinct
    cases k with
    | zero =>
      have same : (d.name == (d :: ds)[0].name) = true := beq_iff_eq.mpr rfl
      rw [if_pos same]
    | succ j =>
      have hj : j < ds.length := Nat.lt_of_succ_lt_succ hk
      have ne : (d.name == ds[j].name) = false := by
        cases h : (d.name == ds[j].name) with
        | false => rfl
        | true =>
          exact absurd (List.mem_map.mpr ⟨ds[j], List.getElem_mem hj, (beq_iff_eq.mp h).symm⟩)
            notIn
      simp only [List.getElem_cons_succ]
      rw [if_neg (by rw [ne]; exact Bool.false_ne_true), findIdx_name rest hj]
      rfl

/-- A name the block spells is a definition's name, at the index it answers. -/
theorem findIdx_some : ∀ {defs : List DefDecl} {s : String} {k : Nat},
    defs.findIdx? (·.name == s) = some k → ∃ d, defs[k]? = some d ∧ d.name = s
  | [], _, _, h => by rw [List.findIdx?_nil] at h; cases h
  | d :: ds, s, k, h => by
    rw [List.findIdx?_cons] at h
    split at h
    · rename_i hd
      cases h
      exact ⟨d, rfl, beq_iff_eq.mp hd⟩
    · obtain ⟨j, hj, heq⟩ := Option.map_eq_some_iff.mp h
      subst heq
      obtain ⟨d', hd', hname⟩ := findIdx_some hj
      exact ⟨d', by rw [List.getElem?_cons_succ]; exact hd', hname⟩

/-- **The spelling map of a block is lawful** (decisions row 328, slice PROC-3): at a lawful
spelling, under the signature's `LawfulCalls` and a block whose names are `DefsNamed`, the
block's spelling map is lawful at the block's signature. So `read_print` and `read_exact` hold
at a block's signature. A step of the claim `module-defs-round-trip`; its consumer is the module
round trip on the readable domain (`readModule_printModule_readable`). -/
theorem LawfulSpelling.withDefs {sig : Signature Op} {spell : String → List RowArg → Option Op}
    {call : Nat → Op} (hl : LawfulSpelling sig spell) (calls : LawfulCalls sig spell call)
    {defs : List DefDecl} (named : DefsNamed spell defs) :
    LawfulSpelling (sig.withDefs defs) (defsSpell call defs spell) where
  spell_row := by
    intro op hd hh
    cases hc : sig.callOf op with
    | none =>
      rw [Signature.withDefs_dom_of_none sig defs hc] at hd
      rw [Signature.withDefs_rowOf_of_none sig defs hc] at hh ⊢
      have base := hl.spell_row op hd hh
      change defsSpell call defs spell (sig.rowOf op).spelling (sig.rowOf op).trailing =
        some (sig.face op)
      cases htr : (sig.rowOf op).trailing with
      | cons a as =>
        rw [htr] at base
        exact base
      | nil =>
        rw [htr] at base
        cases hf : defs.findIdx? (·.name == (sig.rowOf op).spelling) with
        | none => simp only [defsSpell, hf, base]
        | some k =>
          obtain ⟨d, hdk, hname⟩ := findIdx_some hf
          have unspelled := named.unspelled d (List.mem_of_getElem? hdk) []
          rw [hname, base] at unspelled
          cases unspelled
    | some k =>
      replace hd : k < defs.length := Signature.withDefs_dom_call_lt sig defs hc hd
      rw [Signature.withDefs_rowOf_call sig defs hc (List.getElem?_eq_getElem hd)]
      change defsSpell call defs spell defs[k].name [] = some (sig.face op)
      simp only [defsSpell, findIdx_name named.distinct hd, calls.face_call op k hc]
  row_of_spell := by
    intro s names op h
    have plain : ∀ {op}, spell s names = some op →
        ((sig.withDefs defs).rowOf op).spelling = s ∧
          ((sig.withDefs defs).rowOf op).trailing = names := by
      intro op h
      rw [Signature.withDefs_rowOf_of_none sig defs (calls.spell_plain s names op h)]
      exact hl.row_of_spell s names op h
    cases names with
    | cons a as => exact plain h
    | nil =>
      cases hf : defs.findIdx? (·.name == s) with
      | none =>
        simp only [defsSpell, hf] at h
        exact plain h
      | some k =>
        simp only [defsSpell, hf, Option.some.injEq] at h
        subst h
        obtain ⟨d, hdk, hname⟩ := findIdx_some hf
        rw [Signature.withDefs_rowOf_call sig defs (calls.callOf_call k) hdk]
        exact ⟨hname, rfl⟩
  value_trailing := by
    intro op hshape
    cases hc : sig.callOf op with
    | none =>
      rw [Signature.withDefs_rowOf_of_none sig defs hc] at hshape ⊢
      exact hl.value_trailing op hshape
    | some k =>
      cases hdk : defs[k]? with
      | none =>
        rw [withDefs_rowOf_out sig defs hc hdk] at hshape ⊢
        exact hl.value_trailing op hshape
      | some d =>
        rw [Signature.withDefs_rowOf_call sig defs hc hdk] at hshape
        cases hshape
  spelling_ne_name := by
    intro op i
    cases hc : sig.callOf op with
    | none =>
      rw [Signature.withDefs_rowOf_of_none sig defs hc]
      exact hl.spelling_ne_name op i
    | some k =>
      cases hdk : defs[k]? with
      | none =>
        rw [withDefs_rowOf_out sig defs hc hdk]
        exact hl.spelling_ne_name op i
      | some d =>
        rw [Signature.withDefs_rowOf_call sig defs hc hdk]
        exact named.notBinder d (List.mem_of_getElem? hdk) i
  spelling_not_reserved := by
    intro op
    cases hc : sig.callOf op with
    | none =>
      rw [Signature.withDefs_rowOf_of_none sig defs hc]
      exact hl.spelling_not_reserved op
    | some k =>
      cases hdk : defs[k]? with
      | none =>
        rw [withDefs_rowOf_out sig defs hc hdk]
        exact hl.spelling_not_reserved op
      | some d =>
        rw [Signature.withDefs_rowOf_call sig defs hc hdk]
        exact named.notReserved d (List.mem_of_getElem? hdk)
  trailing_ne_name := by
    intro op i
    cases hc : sig.callOf op with
    | none =>
      rw [Signature.withDefs_rowOf_of_none sig defs hc]
      exact hl.trailing_ne_name op i
    | some k =>
      cases hdk : defs[k]? with
      | none =>
        rw [withDefs_rowOf_out sig defs hc hdk]
        exact hl.trailing_ne_name op i
      | some d =>
        rw [Signature.withDefs_rowOf_call sig defs hc hdk]
        exact List.not_mem_nil
  trailing_ne_undefined := by
    intro op
    cases hc : sig.callOf op with
    | none =>
      rw [Signature.withDefs_rowOf_of_none sig defs hc]
      exact hl.trailing_ne_undefined op
    | some k =>
      cases hdk : defs[k]? with
      | none =>
        rw [withDefs_rowOf_out sig defs hc hdk]
        exact hl.trailing_ne_undefined op
      | some d =>
        rw [Signature.withDefs_rowOf_call sig defs hc hdk]
        exact List.not_mem_nil
  withTerm_row := by
    intro op f
    change (sig.withDefs defs).rowOf (sig.withTerm op f) = (sig.withDefs defs).rowOf op
    cases hc : sig.callOf op with
    | none =>
      rw [Signature.withDefs_rowOf_of_none sig defs hc, Signature.withDefs_rowOf_of_none sig defs
        ((calls.callOf_withTerm op f).trans hc)]
      exact hl.withTerm_row op f
    | some k =>
      have hc' := (calls.callOf_withTerm op f).trans hc
      cases hdk : defs[k]? with
      | none =>
        rw [withDefs_rowOf_out sig defs hc hdk, withDefs_rowOf_out sig defs hc' hdk]
        exact hl.withTerm_row op f
      | some d =>
        rw [Signature.withDefs_rowOf_call sig defs hc hdk,
          Signature.withDefs_rowOf_call sig defs hc' hdk]
  termOf_withTerm := hl.termOf_withTerm
  withTerm_termOf := hl.withTerm_termOf
  withTerm_withTerm := hl.withTerm_withTerm
  withTerm_none := hl.withTerm_none
  typeArgs :=
    { call := by
        intro op tys
        change ((sig.withDefs defs).rowOf (sig.withTypeArgs op tys)).callColumns =
          ((sig.withDefs defs).rowOf op).callColumns
        cases hc : sig.callOf op with
        | none =>
          rw [Signature.withDefs_rowOf_of_none sig defs hc, Signature.withDefs_rowOf_of_none sig
            defs ((calls.callOf_withTypeArgs op tys).trans hc)]
          exact hl.typeArgs.call op tys
        | some k =>
          have hc' := (calls.callOf_withTypeArgs op tys).trans hc
          cases hdk : defs[k]? with
          | none =>
            rw [withDefs_rowOf_out sig defs hc hdk, withDefs_rowOf_out sig defs hc' hdk]
            exact hl.typeArgs.call op tys
          | some d =>
            rw [Signature.withDefs_rowOf_call sig defs hc hdk,
              Signature.withDefs_rowOf_call sig defs hc' hdk]
      typeArgsOf_withTypeArgs := hl.typeArgs.typeArgsOf_withTypeArgs
      length_typeArgsOf := hl.typeArgs.length_typeArgsOf
      withTypeArgs_typeArgsOf := hl.typeArgs.withTypeArgs_typeArgsOf
      withTypeArgs_withTypeArgs := hl.typeArgs.withTypeArgs_withTypeArgs
      withTypeArgs_withTerm := hl.typeArgs.withTypeArgs_withTerm
      termOf_withTypeArgs := hl.typeArgs.termOf_withTypeArgs
      typeArgsOf_withTerm := hl.typeArgs.typeArgsOf_withTerm }
  -- an invocation's spelling is its definition's name, which no key of the signature spells
  literal_alone := by
    intro op v names hd hp
    change defsSpell call defs spell ((sig.withDefs defs).rowOf op).spelling (.str v :: names) =
      none
    simp only [defsSpell]
    cases hc : sig.callOf op with
    | none =>
      rw [Signature.withDefs_dom_of_none sig defs hc] at hd
      rw [Signature.withDefs_rowOf_of_none sig defs hc] at hp ⊢
      exact hl.literal_alone op v names hd hp
    | some k =>
      replace hd : k < defs.length := Signature.withDefs_dom_call_lt sig defs hc hd
      rw [Signature.withDefs_rowOf_call sig defs hc (List.getElem?_eq_getElem hd)]
      exact named.unspelled defs[k] (List.getElem_mem hd) _

/-- The operations the native spelling map answers invoke no definition. -/
theorem nativeSpelled_callOf : ∀ op ∈ NativeOp.spelled, (nativeSignature []).callOf op = none := by
  decide

/-- **The native signature's invocations are lawful**: `NativeOp.call k` invokes definition `k`
and is its own face, the updates of an operation keep its definition, and the native spelling
map answers no invocation. A step of the claim `module-defs-round-trip`. -/
theorem nativeCalls (table : RowTable) :
    LawfulCalls (nativeSignature table) (nativeSpell table) NativeOp.call where
  callOf_call _ := rfl
  face_call op k h := by
    cases op <;> simp only [nativeSignature, reduceCtorEq, Option.some.injEq] at h
    subst h
    rfl
  callOf_withTerm op f := by cases op <;> rfl
  callOf_withTypeArgs op tys := by
    cases op with
    | deferredMakeOf value error =>
      cases tys with
      | nil => rfl
      | cons a rest =>
        cases rest with
        | nil => rfl
        | cons b rest => cases rest <;> rfl
    | _ => rfl
  spell_plain s names op h := by
    unfold nativeSpell at h
    cases hf : NativeOp.spelled.find? (fun op => decide (rowKey op.row = (s, names))) with
    | some found =>
      simp only [hf, Option.some.injEq] at h
      subst h
      exact nativeSpelled_callOf found (List.mem_of_find?_eq_some hf)
    | none =>
      simp only [hf] at h
      obtain ⟨i, _, heq⟩ := Option.map_eq_some_iff.mp h
      subst heq
      rfl

/-- A printed binder is a binder name. A step of `defsNamed_of_fault`. -/
theorem binderNamed_name (i : Nat) : binderNamed (Var.name i) = true := by
  have ha : "a".toByteArray.data.toList = [97] := by decide
  have bytes : (Var.name i).toByteArray.data.toList =
      97 :: (Nat.repr i).toByteArray.data.toList := by
    rw [Var.name, String.toByteArray_append, ByteArray.data_append, Array.toList_append, ha]
    rfl
  unfold binderNamed
  rw [bytes]
  simp only [decodeBytes_repr, decide_true]

/-- What a safe export name is not: no binder, no reserved head, and a binding of the target.
A step of `defsNamed_of_fault`. -/
theorem exportNameSafe_facts {s : String} (h : exportNameSafe s = true) :
    Effect4.Codegen.Names.binderName s = true ∧ binderNamed s = false ∧
      reserved.contains s = false := by
  unfold exportNameSafe at h
  rw [Option.isNone_iff_eq_none] at h
  unfold exportNameFault at h
  split at h
  · cases h
  · rename_i hbinding
    split at h
    · cases h
    · rename_i hbinder
      split at h
      · cases h
      · rename_i hreserved
        exact ⟨by simpa only [Bool.not_eq_true', Bool.not_eq_false] using hbinding,
          by simpa only [Bool.not_eq_true] using hbinder,
          by simpa only [Bool.not_eq_true] using hreserved⟩

/-- No built-in row's spelling is a binding: each holds a dot. -/
theorem spelled_not_binding :
    NativeOp.spelled.all (fun op => !Effect4.Codegen.Names.binderName op.row.spelling) = true := by
  decide +kernel

/-- **The printer's name check gives the names that a block's spelling map reads back**, at the
native signature: distinct, spelled by no built-in row and no row of the table, no binder and
no reserved head. A step of the claim `module-defs-round-trip`; its consumer is
`ModuleEmission.readModule`. -/
theorem defsNamed_of_fault {table : RowTable} {name : String} {defs : List DefDecl}
    (h : defsNameFault table name defs = none) : DefsNamed (nativeSpell table) defs := by
  induction defs with
  | nil => exact ⟨List.nodup_nil, nofun, nofun, nofun⟩
  | cons d ds ih =>
    unfold defsNameFault at h
    split at h
    · cases h
    · rename_i hfault
      simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false] at hfault
      obtain ⟨⟨⟨hsafe, _⟩, htable⟩, hrest⟩ := hfault
      obtain ⟨hbinding, hbinder, hreserved⟩ := exportNameSafe_facts hsafe
      have rest := ih h
      have unspelled : ∀ names, nativeSpell table d.name names = none := by
        intro names
        unfold nativeSpell
        cases hf : NativeOp.spelled.find? (fun op => decide (rowKey op.row = (d.name, names))) with
        | some op =>
          have mem := List.mem_of_find?_eq_some hf
          have key := of_decide_eq_true
            (List.find?_some (p := fun op : NativeOp => decide (rowKey op.row = (d.name, names)))
              hf)
          have spelling : op.row.spelling = d.name := congrArg Prod.fst key
          have plain := List.all_eq_true.mp spelled_not_binding op mem
          rw [spelling, hbinding] at plain
          cases plain
        | none =>
          have absent :
              table.findIdx? (fun row => decide (rowKey row = (d.name, names))) = none := by
            apply List.findIdx?_eq_none_iff.mpr
            intro row mem
            apply decide_eq_false
            intro key
            have spelling : row.spelling = d.name := congrArg Prod.fst key
            exact htable (List.any_eq_true.mpr ⟨row, mem, beq_iff_eq.mpr spelling⟩)
          simp only [absent, Option.map_none]
      refine ⟨?_, ?_, ?_, ?_⟩
      · refine List.nodup_cons.mpr ⟨?_, rest.distinct⟩
        intro mem
        obtain ⟨d', hd', same⟩ := List.mem_map.mp mem
        exact hrest (List.any_eq_true.mpr ⟨d', hd', beq_iff_eq.mpr same⟩)
      · intro d' mem
        rcases List.mem_cons.mp mem with rfl | tail
        · exact unspelled
        · exact rest.unspelled d' tail
      · intro d' mem i same
        rcases List.mem_cons.mp mem with rfl | tail
        · rw [same, binderNamed_name] at hbinder
          cases hbinder
        · exact rest.notBinder d' tail i same
      · intro d' mem
        rcases List.mem_cons.mp mem with rfl | tail
        · intro hm
          rw [List.contains_iff_mem.mpr hm] at hreserved
          cases hreserved
        · exact rest.notReserved d' tail

end Effect4.Program
