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

/-! ## A signature extended by named rows

A block's signature (`Signature.withDefs`) and a body's (`Signature.withParams`) extend a
signature the same way: the operations an index names read a row each, spelled by a name of its
own, and every other operation reads the signature's own row. One law covers both
(`LawfulSpelling.extend`). -/

/-- **A signature extended by named rows**: the operations that `ix` indexes read the row at their
index when there is one, and every other operation reads the signature's own row and domain; an
indexed operation in the domain has its row; the two updates of an operation and their readings
are the signature's. A step of `LawfulSpelling.extend`. -/
structure NamedRows (sig ext : Signature Op) (ix : Op → Option Nat) (rows : List Row) :
    Prop where
  rowOf_none : ∀ op, ix op = none → ext.rowOf op = sig.rowOf op
  dom_none : ∀ op, ix op = none → ext.dom op = sig.dom op
  rowOf_ix : ∀ op k, ix op = some k → ext.rowOf op = rows[k]?.getD (sig.rowOf op)
  dom_lt : ∀ op k, ix op = some k → ext.dom op = true → k < rows.length
  termOf : ext.termOf = sig.termOf
  withTerm : ext.withTerm = sig.withTerm
  typeArgsOf : ext.typeArgsOf = sig.typeArgsOf
  withTypeArgs : ext.withTypeArgs = sig.withTypeArgs

/-- What a signature's indexed operations owe a spelling map that names them: `mk k` is indexed
by `k` and is the face of every operation indexed by `k`; the two updates keep the index; and the
signature's own spelling map answers no indexed operation. A step of `LawfulSpelling.extend`. -/
structure LawfulIndex (sig : Signature Op) (spell : String → List RowArg → Option Op)
    (ix : Op → Option Nat) (mk : Nat → Op) : Prop where
  ix_mk : ∀ k, ix (mk k) = some k
  face_mk : ∀ op k, ix op = some k → sig.face op = mk k
  ix_withTerm : ∀ op f, ix (sig.withTerm op f) = ix op
  ix_withTypeArgs : ∀ op tys, ix (sig.withTypeArgs op tys) = ix op
  spell_plain : ∀ s names op, spell s names = some op → ix op = none

/-- The names of an extension's rows that its spelling map reads back: `nameIdx` answers each
row's index from its spelling, and only those; each row has no trailing argument, and its
spelling is spelled by no row of the signature, is no printed binder and no reserved head. A
step of `LawfulSpelling.extend`. -/
structure RowsNamed (spell : String → List RowArg → Option Op) (rows : List Row)
    (nameIdx : String → Option Nat) : Prop where
  idx_row : ∀ k (h : k < rows.length), nameIdx rows[k].spelling = some k
  row_idx : ∀ s k, nameIdx s = some k → ∃ r, rows[k]? = some r ∧ r.spelling = s
  trailing : ∀ r ∈ rows, r.trailing = []
  unspelled : ∀ r ∈ rows, ∀ names, spell r.spelling names = none
  notBinder : ∀ r ∈ rows, ∀ i, r.spelling ≠ Var.name i
  notReserved : ∀ r ∈ rows, r.spelling ∉ reserved

/-- An indexed operation's row is its index's row, or the signature's own where the index has
none. A step of `LawfulSpelling.extend`. -/
theorem NamedRows.row_cases {sig ext : Signature Op} {ix : Op → Option Nat} {rows : List Row}
    (hx : NamedRows sig ext ix rows) (op : Op) :
    ext.rowOf op = sig.rowOf op ∨ ∃ k r, ix op = some k ∧ rows[k]? = some r ∧ ext.rowOf op = r := by
  cases h : ix op with
  | none => exact Or.inl (hx.rowOf_none op h)
  | some k =>
    rw [hx.rowOf_ix op k h]
    cases hk : rows[k]? with
    | none => exact Or.inl rfl
    | some r => exact Or.inr ⟨k, r, rfl, hk, rfl⟩

/-- **A lawful spelling stays lawful under named rows** (decisions rows 328 and 340): at a
lawful spelling, an extension by rows whose index is lawful and whose names the map reads back is
lawful under its spelling map. So `read_print` and `read_exact` hold at a block's signature and
at a body's. A step of the claim `module-defs-round-trip`; its consumers are
`LawfulSpelling.withDefs` and `LawfulSpelling.withParams`. -/
theorem LawfulSpelling.extend {sig ext : Signature Op} {spell : String → List RowArg → Option Op}
    {ix : Op → Option Nat} {mk : Nat → Op} {rows : List Row} {nameIdx : String → Option Nat}
    (hl : LawfulSpelling sig spell) (hx : NamedRows sig ext ix rows)
    (index : LawfulIndex sig spell ix mk) (named : RowsNamed spell rows nameIdx) :
    LawfulSpelling ext (namedSpell mk nameIdx spell) := by
  have face : ∀ op, ext.face op = sig.face op := fun op => by
    simp only [Signature.face, hx.withTerm, hx.withTypeArgs]
  -- a row's name answers no other spelling of the signature
  have plainOf : ∀ s names op, spell s names = some op → namedSpell mk nameIdx spell s names = some op := by
    intro s names op h
    cases names with
    | cons a as => exact h
    | nil =>
      cases hi : nameIdx s with
      | none => simp only [namedSpell, hi, h]
      | some k =>
        obtain ⟨r, hr, rfl⟩ := named.row_idx s k hi
        rw [named.unspelled r (List.mem_of_getElem? hr) []] at h
        cases h
  have atRow : ∀ k (h : k < rows.length),
      namedSpell mk nameIdx spell rows[k].spelling [] = some (mk k) := by
    intro k h
    simp only [namedSpell, named.idx_row k h]
  exact
  { spell_row := by
      intro op hd hh
      rw [face]
      cases hi : ix op with
      | none =>
        rw [hx.dom_none op hi] at hd
        rw [hx.rowOf_none op hi] at hh ⊢
        exact plainOf _ _ _ (hl.spell_row op hd hh)
      | some k =>
        have hk := hx.dom_lt op k hi hd
        rw [hx.rowOf_ix op k hi, List.getElem?_eq_getElem hk, Option.getD_some,
          named.trailing _ (List.getElem_mem hk), index.face_mk op k hi]
        exact atRow k hk
    row_of_spell := by
      intro s names op h
      have plain : spell s names = some op →
          (ext.rowOf op).spelling = s ∧ (ext.rowOf op).trailing = names := by
        intro h
        rw [hx.rowOf_none op (index.spell_plain s names op h)]
        exact hl.row_of_spell s names op h
      cases names with
      | cons a as => exact plain h
      | nil =>
        cases hi : nameIdx s with
        | none =>
          simp only [namedSpell, hi] at h
          exact plain h
        | some k =>
          simp only [namedSpell, hi, Option.some.injEq] at h
          subst h
          obtain ⟨r, hr, hs⟩ := named.row_idx s k hi
          rw [hx.rowOf_ix _ k (index.ix_mk k), hr, Option.getD_some]
          exact ⟨hs, named.trailing r (List.mem_of_getElem? hr)⟩
    value_trailing := by
      intro op hshape
      rcases hx.row_cases op with same | ⟨k, r, -, hr, hrow⟩
      · rw [same] at hshape ⊢
        exact hl.value_trailing op hshape
      · rw [hrow]
        exact named.trailing r (List.mem_of_getElem? hr)
    spelling_ne_name := by
      intro op i
      rcases hx.row_cases op with same | ⟨k, r, -, hr, hrow⟩
      · rw [same]
        exact hl.spelling_ne_name op i
      · rw [hrow]
        exact named.notBinder r (List.mem_of_getElem? hr) i
    spelling_not_reserved := by
      intro op
      rcases hx.row_cases op with same | ⟨k, r, -, hr, hrow⟩
      · rw [same]
        exact hl.spelling_not_reserved op
      · rw [hrow]
        exact named.notReserved r (List.mem_of_getElem? hr)
    trailing_ne_name := by
      intro op i
      rcases hx.row_cases op with same | ⟨k, r, -, hr, hrow⟩
      · rw [same]
        exact hl.trailing_ne_name op i
      · rw [hrow, named.trailing r (List.mem_of_getElem? hr)]
        exact List.not_mem_nil
    trailing_ne_undefined := by
      intro op
      rcases hx.row_cases op with same | ⟨k, r, -, hr, hrow⟩
      · rw [same]
        exact hl.trailing_ne_undefined op
      · rw [hrow, named.trailing r (List.mem_of_getElem? hr)]
        exact List.not_mem_nil
    withTerm_row := by
      intro op f
      rw [hx.withTerm]
      cases hi : ix op with
      | none =>
        rw [hx.rowOf_none op hi, hx.rowOf_none _ ((index.ix_withTerm op f).trans hi)]
        exact hl.withTerm_row op f
      | some k =>
        rw [hx.rowOf_ix op k hi, hx.rowOf_ix _ k ((index.ix_withTerm op f).trans hi),
          hl.withTerm_row op f]
    termOf_withTerm := by
      rw [hx.termOf, hx.withTerm]
      exact hl.termOf_withTerm
    withTerm_termOf := by
      rw [hx.termOf, hx.withTerm]
      exact hl.withTerm_termOf
    withTerm_withTerm := by
      rw [hx.withTerm]
      exact hl.withTerm_withTerm
    withTerm_none := by
      rw [hx.termOf, hx.withTerm]
      exact hl.withTerm_none
    typeArgs :=
      { call := by
          intro op tys
          rw [hx.withTypeArgs]
          cases hi : ix op with
          | none =>
            rw [hx.rowOf_none op hi, hx.rowOf_none _ ((index.ix_withTypeArgs op tys).trans hi)]
            exact hl.typeArgs.call op tys
          | some k =>
            rw [hx.rowOf_ix op k hi, hx.rowOf_ix _ k ((index.ix_withTypeArgs op tys).trans hi)]
            cases rows[k]? with
            | none => exact hl.typeArgs.call op tys
            | some r => rfl
        typeArgsOf_withTypeArgs := by
          rw [hx.typeArgsOf, hx.withTypeArgs]
          exact hl.typeArgs.typeArgsOf_withTypeArgs
        length_typeArgsOf := by
          rw [hx.typeArgsOf, hx.withTypeArgs]
          exact hl.typeArgs.length_typeArgsOf
        withTypeArgs_typeArgsOf := by
          rw [hx.typeArgsOf, hx.withTypeArgs]
          exact hl.typeArgs.withTypeArgs_typeArgsOf
        withTypeArgs_withTypeArgs := by
          rw [hx.withTypeArgs]
          exact hl.typeArgs.withTypeArgs_withTypeArgs
        withTypeArgs_withTerm := by
          rw [hx.withTypeArgs, hx.withTerm]
          exact hl.typeArgs.withTypeArgs_withTerm
        termOf_withTypeArgs := by
          rw [hx.termOf, hx.withTypeArgs]
          exact hl.typeArgs.termOf_withTypeArgs
        typeArgsOf_withTerm := by
          rw [hx.typeArgsOf, hx.withTerm]
          exact hl.typeArgs.typeArgsOf_withTerm }
    -- a row's spelling is its name, which no key of the signature spells
    literal_alone := by
      intro op v names hd hp
      change spell (ext.rowOf op).spelling (.str v :: names) = none
      cases hi : ix op with
      | none =>
        rw [hx.dom_none op hi] at hd
        rw [hx.rowOf_none op hi] at hp ⊢
        exact hl.literal_alone op v names hd hp
      | some k =>
        have hk := hx.dom_lt op k hi hd
        rw [hx.rowOf_ix op k hi, List.getElem?_eq_getElem hk, Option.getD_some]
        exact named.unspelled _ (List.getElem_mem hk) _ }

/-! ## A block's signature -/

/-- A block's signature is an extension by its definitions' rows. A step of
`LawfulSpelling.withDefs`. -/
theorem namedRows_withDefs (sig : Signature Op) (defs : List DefDecl) :
    NamedRows sig (sig.withDefs defs) sig.callOf (defs.map (·.row.normalizeTypes)) where
  rowOf_none _ h := sig.withDefs_rowOf_of_none defs h
  dom_none _ h := sig.withDefs_dom_of_none defs h
  rowOf_ix op k h := by
    rw [List.getElem?_map]
    cases hk : defs[k]? with
    | none => exact withDefs_rowOf_out sig defs h hk
    | some d => exact sig.withDefs_rowOf_call defs h hk
  dom_lt _ _ h hd := by
    rw [List.length_map]
    exact sig.withDefs_dom_call_lt defs h hd
  termOf := rfl
  withTerm := rfl
  typeArgsOf := rfl
  withTypeArgs := rfl

/-- A block's names are the names of its rows. A step of `LawfulSpelling.withDefs`. -/
theorem DefsNamed.rows {spell : String → List RowArg → Option Op} {defs : List DefDecl}
    (named : DefsNamed spell defs) :
    RowsNamed spell (defs.map (·.row.normalizeTypes)) fun s => defs.findIdx? (·.name == s) where
  idx_row k h := by
    rw [List.length_map] at h
    simp only [List.getElem_map]
    exact findIdx_name named.distinct h
  row_idx s k h := by
    obtain ⟨d, hd, hs⟩ := findIdx_some h
    exact ⟨d.row.normalizeTypes, by rw [List.getElem?_map, hd]; rfl, hs⟩
  trailing r mem := by
    obtain ⟨d, -, rfl⟩ := List.mem_map.mp mem
    rfl
  unspelled r mem := by
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp mem
    exact named.unspelled d hd
  notBinder r mem := by
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp mem
    exact named.notBinder d hd
  notReserved r mem := by
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp mem
    exact named.notReserved d hd

/-- A signature's lawful invocations are a lawful index. A step of `LawfulSpelling.withDefs`. -/
theorem LawfulCalls.index {sig : Signature Op} {spell : String → List RowArg → Option Op}
    {call : Nat → Op} (calls : LawfulCalls sig spell call) : LawfulIndex sig spell sig.callOf call where
  ix_mk := calls.callOf_call
  face_mk := calls.face_call
  ix_withTerm := calls.callOf_withTerm
  ix_withTypeArgs := calls.callOf_withTypeArgs
  spell_plain := calls.spell_plain

/-- **The spelling map of a block is lawful** (decisions row 328, slice PROC-3): at a lawful
spelling, under the signature's `LawfulCalls` and a block whose names are `DefsNamed`, the
block's spelling map is lawful at the block's signature. So `read_print` and `read_exact` hold
at a block's signature. A step of the claim `module-defs-round-trip`; its consumer is the module
round trip on the readable domain (`readModule_printModule_readable`). -/
theorem LawfulSpelling.withDefs {sig : Signature Op} {spell : String → List RowArg → Option Op}
    {call : Nat → Op} (hl : LawfulSpelling sig spell) (calls : LawfulCalls sig spell call)
    {defs : List DefDecl} (named : DefsNamed spell defs) :
    LawfulSpelling (sig.withDefs defs) (defsSpell call defs spell) :=
  hl.extend (namedRows_withDefs sig defs) calls.index named.rows

/-! ## A body's signature (slice HO-3) -/

/-- What a signature's parameter runs owe a body's spelling map: a lawful index (`LawfulIndex`
at `paramOf`), and every run of a parameter outside the signature's own domain, as the native
signature keeps it. -/
structure LawfulParams (sig : Signature Op) (spell : String → List RowArg → Option Op)
    (param : Nat → Op) : Prop extends LawfulIndex sig spell sig.paramOf param where
  outside : ∀ op i, sig.paramOf op = some i → sig.dom op = false

/-- The parameters of a body that its spelling map reads back: distinct, spelled by no row of the
block's map, no printed binder and no reserved head. -/
structure ParamsNamed (spell : String → List RowArg → Option Op) (ps : List ParamDecl) :
    Prop where
  distinct : (ps.map (·.name)).Nodup
  unspelled : ∀ q ∈ ps, ∀ names, spell q.name names = none
  notBinder : ∀ q ∈ ps, ∀ i, q.name ≠ Var.name i
  notReserved : ∀ q ∈ ps, q.name ∉ reserved

/-- A distinct parameter name's first index is its own. A step of `ParamsNamed.rows`. -/
theorem findIdx_param : ∀ {ps : List ParamDecl}, (ps.map (·.name)).Nodup →
    ∀ {k : Nat} (hk : k < ps.length), ps.findIdx? (·.name == ps[k].name) = some k
  | [], _, k, hk => absurd hk (Nat.not_lt_zero k)
  | q :: qs, distinct, k, hk => by
    rw [List.findIdx?_cons]
    obtain ⟨notIn, rest⟩ := List.nodup_cons.mp distinct
    cases k with
    | zero =>
      have same : (q.name == (q :: qs)[0].name) = true := beq_iff_eq.mpr rfl
      rw [if_pos same]
    | succ j =>
      have hj : j < qs.length := Nat.lt_of_succ_lt_succ hk
      have ne : (q.name == qs[j].name) = false := by
        cases h : (q.name == qs[j].name) with
        | false => rfl
        | true =>
          exact absurd (List.mem_map.mpr ⟨qs[j], List.getElem_mem hj, (beq_iff_eq.mp h).symm⟩)
            notIn
      simp only [List.getElem_cons_succ]
      rw [if_neg (by rw [ne]; exact Bool.false_ne_true), findIdx_param rest hj]
      rfl

/-- A name a body spells is a parameter's name, at the index it answers. A step of
`ParamsNamed.rows`. -/
theorem findIdx_param_some : ∀ {ps : List ParamDecl} {s : String} {k : Nat},
    ps.findIdx? (·.name == s) = some k → ∃ q, ps[k]? = some q ∧ q.name = s
  | [], _, _, h => by rw [List.findIdx?_nil] at h; cases h
  | q :: qs, s, k, h => by
    rw [List.findIdx?_cons] at h
    split at h
    · rename_i hq
      cases h
      exact ⟨q, rfl, beq_iff_eq.mp hq⟩
    · obtain ⟨j, hj, heq⟩ := Option.map_eq_some_iff.mp h
      subst heq
      obtain ⟨q', hq', hname⟩ := findIdx_param_some hj
      exact ⟨q', by rw [List.getElem?_cons_succ]; exact hq', hname⟩

/-- A body's parameter names are the names of its rows. A step of `LawfulSpelling.withParams`. -/
theorem ParamsNamed.rows {spell : String → List RowArg → Option Op} {ps : List ParamDecl}
    (named : ParamsNamed spell ps) :
    RowsNamed spell (ps.map (·.row.normalizeTypes)) fun s => ps.findIdx? (·.name == s) where
  idx_row k h := by
    rw [List.length_map] at h
    simp only [List.getElem_map]
    exact findIdx_param named.distinct h
  row_idx s k h := by
    obtain ⟨q, hq, hs⟩ := findIdx_param_some h
    exact ⟨q.row.normalizeTypes, by rw [List.getElem?_map, hq]; rfl, hs⟩
  trailing r mem := by
    obtain ⟨q, -, rfl⟩ := List.mem_map.mp mem
    rfl
  unspelled r mem := by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp mem
    exact named.unspelled q hq
  notBinder r mem := by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp mem
    exact named.notBinder q hq
  notReserved r mem := by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp mem
    exact named.notReserved q hq

/-- A body's signature is an extension by its parameters' rows, at a signature that keeps every
run of a parameter outside its domain. A step of `LawfulSpelling.withParams`. -/
theorem namedRows_withParams (sig : Signature Op) (ps : List ParamDecl)
    (outside : ∀ op i, sig.paramOf op = some i → sig.dom op = false) :
    NamedRows sig (sig.withParams ps) sig.paramOf (ps.map (·.row.normalizeTypes)) := by
  cases ps with
  | nil =>
    exact
    { rowOf_none := fun _ _ => rfl
      dom_none := fun _ _ => rfl
      rowOf_ix := fun _ _ _ => rfl
      dom_lt := fun op i h hd => by
        change sig.dom op = true at hd
        rw [outside op i h] at hd
        cases hd
      termOf := rfl
      withTerm := rfl
      typeArgsOf := rfl
      withTypeArgs := rfl }
  | cons q qs =>
    exact
    { rowOf_none := fun _ h => by simp only [Signature.withParams, h]
      dom_none := fun _ h => by simp only [Signature.withParams, h]
      rowOf_ix := fun op k h => by
        rw [List.getElem?_map]
        cases hk : (q :: qs)[k]? with
        | none => simp only [Signature.withParams, h, hk, Option.map_none, Option.getD_none]
        | some p => simp only [Signature.withParams, h, hk, Option.map_some, Option.getD_some]
      dom_lt := fun op k h hd => by
        simp only [Signature.withParams, h] at hd
        rw [List.length_map]
        exact of_decide_eq_true hd
      termOf := rfl
      withTerm := rfl
      typeArgsOf := rfl
      withTypeArgs := rfl }

/-- **The spelling map of a body is lawful** (decisions row 340, slice HO-3): at a lawful
spelling, under the signature's `LawfulParams` and parameters whose names are `ParamsNamed`, the
body's spelling map is lawful at the body's signature. So `read_print` holds at a body's
signature. A step of the claim `module-defs-round-trip`; its consumer is the module round trip on
the readable domain. -/
theorem LawfulSpelling.withParams {sig : Signature Op} {spell : String → List RowArg → Option Op}
    {param : Nat → Op} (hl : LawfulSpelling sig spell) (params : LawfulParams sig spell param)
    {ps : List ParamDecl} (named : ParamsNamed spell ps) :
    LawfulSpelling (sig.withParams ps) (paramsSpell param ps spell) :=
  hl.extend (namedRows_withParams sig ps params.outside) params.toLawfulIndex named.rows

/-- **A block keeps its signature's parameter runs lawful**: at a block's signature and spelling
map, the runs of a parameter are as lawful as at the signature, when no invocation runs a
parameter. A step of the claim `module-defs-round-trip`. -/
theorem LawfulParams.withDefs {sig : Signature Op} {spell : String → List RowArg → Option Op}
    {param call : Nat → Op} (params : LawfulParams sig spell param)
    (calls : LawfulCalls sig spell call)
    (apart : ∀ op i, sig.paramOf op = some i → sig.callOf op = none) (defs : List DefDecl) :
    LawfulParams (sig.withDefs defs) (defsSpell call defs spell) param where
  ix_mk := params.ix_mk
  face_mk := params.face_mk
  ix_withTerm := params.ix_withTerm
  ix_withTypeArgs := params.ix_withTypeArgs
  spell_plain s names op h := by
    change sig.paramOf op = none
    cases names with
    | cons a as =>
      simp only [defsSpell, namedSpell] at h
      exact params.spell_plain s _ op h
    | nil =>
      cases hf : defs.findIdx? (·.name == s) with
      | none =>
        simp only [defsSpell, namedSpell, hf] at h
        exact params.spell_plain s [] op h
      | some k =>
        simp only [defsSpell, namedSpell, hf, Option.some.injEq] at h
        subst h
        cases hp : sig.paramOf (call k) with
        | none => rfl
        | some i =>
          have invoked := apart _ i hp
          rw [calls.callOf_call] at invoked
          cases invoked
  outside op i h := by
    rw [Signature.withDefs_dom_of_none sig defs (apart op i h)]
    exact params.outside op i h

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

/-- The operations the native spelling map answers run no parameter. -/
theorem nativeSpelled_paramOf :
    ∀ op ∈ NativeOp.spelled, (nativeSignature []).paramOf op = none := by
  decide

/-- **The native signature's parameter runs are lawful** (slice HO-3): `NativeOp.param i` runs
parameter `i` and is its own face, the updates of an operation keep its parameter, the native
spelling map answers no run, and every run is outside the domain. A step of the claim
`module-defs-round-trip`. -/
theorem nativeParams (table : RowTable) :
    LawfulParams (nativeSignature table) (nativeSpell table) NativeOp.param where
  ix_mk _ := rfl
  face_mk op k h := by
    cases op <;> simp only [nativeSignature, reduceCtorEq, Option.some.injEq] at h
    subst h
    rfl
  ix_withTerm op f := by cases op <;> rfl
  ix_withTypeArgs op tys := by
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
      exact nativeSpelled_paramOf found (List.mem_of_find?_eq_some hf)
    | none =>
      simp only [hf] at h
      obtain ⟨i, _, heq⟩ := Option.map_eq_some_iff.mp h
      subst heq
      rfl
  outside op i h := by
    cases op <;> simp only [nativeSignature, reduceCtorEq] at h ⊢

/-- A native run of a parameter invokes no definition. -/
theorem nativeApart (table : RowTable) :
    ∀ op i, (nativeSignature table).paramOf op = some i →
      (nativeSignature table).callOf op = none := by
  intro op i h
  cases op <;> simp only [nativeSignature, reduceCtorEq] at h ⊢

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

/-- A binding that no row of the table spells is spelled by no key of the native map: each
built-in row's spelling holds a dot. A step of `defsNamed_of_fault` and `paramsNamed_of_fault`. -/
theorem nativeSpell_binding {table : RowTable} {s : String}
    (hbinding : Effect4.Codegen.Names.binderName s = true)
    (htable : ¬ (table.any (·.spelling == s) = true)) :
    ∀ names, nativeSpell table s names = none := by
  intro names
  unfold nativeSpell
  cases hf : NativeOp.spelled.find? (fun op => decide (rowKey op.row = (s, names))) with
  | some op =>
    have mem := List.mem_of_find?_eq_some hf
    have key := of_decide_eq_true
      (List.find?_some (p := fun op : NativeOp => decide (rowKey op.row = (s, names))) hf)
    have spelling : op.row.spelling = s := congrArg Prod.fst key
    have plain := List.all_eq_true.mp spelled_not_binding op mem
    rw [spelling, hbinding] at plain
    cases plain
  | none =>
    have absent :
        table.findIdx? (fun row => decide (rowKey row = (s, names))) = none := by
      apply List.findIdx?_eq_none_iff.mpr
      intro row mem
      apply decide_eq_false
      intro key
      have spelling : row.spelling = s := congrArg Prod.fst key
      exact htable (List.any_eq_true.mpr ⟨row, mem, beq_iff_eq.mpr spelling⟩)
    simp only [absent, Option.map_none]

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
      have unspelled := nativeSpell_binding hbinding htable
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

/-- **The printer's parameter check gives the names that a body's spelling map reads back**
(slice HO-3), at a block of the native signature: distinct, spelled by no definition, no
built-in row and no row of the table, no binder and no reserved head. A step of the claim
`module-defs-round-trip`; its consumer is `ModuleEmission.readModule`. -/
theorem paramsNamed_of_fault {table : RowTable} {name : String} {defs : List DefDecl} :
    ∀ {ps : List ParamDecl}, paramsNameFault table name defs ps = none →
      ParamsNamed (defsSpell NativeOp.call defs (nativeSpell table)) ps
  | [], _ => ⟨List.nodup_nil, nofun, nofun, nofun⟩
  | q :: qs, h => by
    unfold paramsNameFault at h
    split at h
    · cases h
    · rename_i hfault
      simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false] at hfault
      obtain ⟨⟨⟨⟨hsafe, _⟩, htable⟩, hdefs⟩, hrest⟩ := hfault
      obtain ⟨hbinding, hbinder, hreserved⟩ := exportNameSafe_facts hsafe
      have rest := paramsNamed_of_fault h
      have unspelled : ∀ names, defsSpell NativeOp.call defs (nativeSpell table) q.name names =
          none := by
        intro names
        have absent : defs.findIdx? (·.name == q.name) = none := by
          apply List.findIdx?_eq_none_iff.mpr
          intro d mem
          cases same : (d.name == q.name) with
          | false => rfl
          | true => exact absurd (List.any_eq_true.mpr ⟨d, mem, same⟩) hdefs
        cases names with
        | nil =>
          simp only [defsSpell, namedSpell, absent]
          exact nativeSpell_binding hbinding htable []
        | cons a as =>
          simp only [defsSpell, namedSpell]
          exact nativeSpell_binding hbinding htable _
      refine ⟨?_, ?_, ?_, ?_⟩
      · refine List.nodup_cons.mpr ⟨?_, rest.distinct⟩
        intro mem
        obtain ⟨q', hq', same⟩ := List.mem_map.mp mem
        exact hrest (List.any_eq_true.mpr ⟨q', hq', beq_iff_eq.mpr same⟩)
      · intro q' mem
        rcases List.mem_cons.mp mem with rfl | tail
        · exact unspelled
        · exact rest.unspelled q' tail
      · intro q' mem i same
        rcases List.mem_cons.mp mem with rfl | tail
        · rw [same, binderNamed_name] at hbinder
          cases hbinder
        · exact rest.notBinder q' tail i same
      · intro q' mem
        rcases List.mem_cons.mp mem with rfl | tail
        · intro hm
          rw [List.contains_iff_mem.mpr hm] at hreserved
          cases hreserved
        · exact rest.notReserved q' tail

/-- The parameters of every definition of a block that the printer's check passes are named. -/
theorem blockParamsNamed {table : RowTable} {name : String} {defs : List DefDecl}
    (h : blockParamsFault table name defs = none) :
    ∀ d ∈ defs, ParamsNamed (defsSpell NativeOp.call defs (nativeSpell table)) d.params := by
  intro d mem
  apply paramsNamed_of_fault (name := name)
  unfold blockParamsFault at h
  exact List.findSome?_eq_none_iff.mp h d mem

end Effect4.Program
