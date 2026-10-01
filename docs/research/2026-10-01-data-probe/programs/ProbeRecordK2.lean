/-! Seat PROGRAMS of the data probe (2026-10-01), probe 5: the record stage's K2 obligation to
JSON, in miniature (no tree import). A record type is a binary row extension (`ProbeSpine.lean`'s
`U`), a record value the field values in field order, and its JSON image an object. The decoder
looks fields up by key and ignores keys the record does not name, as rc.112's `Schema.Struct`
does by default (`onExcessProperty: "ignore"`, `vendor/effect-4.0.0-rc.112/src/SchemaAST.ts:445`).

Two laws, the vocabulary's three K2 laws with totality folded into the first:
* `dec_enc`: on a well-formed type (labels distinct along each chain), a member encodes, and
  its encoding decodes to it (retraction);
* `enc_dec`: whatever decodes re-encodes to the decoded object put in the named normal form `N`
  (fields in the record's order, keys it does not name dropped): exactness modulo `N`.
Red controls: an object with an excess key and another key order decodes, and does not
re-encode to itself (so `N` is needed); duplicate labels break the retraction (so the
well-formedness premise is needed). Scratch, not in the tree. -/

set_option autoImplicit false

namespace Probe.RecordK2

inductive U where
  | nat
  | str
  | empty
  | extend (label : String) (field : U) (rest : U)

inductive V where
  | nat (n : Nat)
  | str (s : String)
  | list (xs : List V)

inductive J where
  | num (n : Nat)
  | str (s : String)
  | obj (entries : List (String × J))

/-- The first entry under a key. -/
def find (key : String) : List (String × J) → Option J
  | [] => none
  | (k, j) :: rest => if k = key then some j else find key rest

/-- A record chain: `empty`, or an extension of one. -/
def RecU : U → Prop
  | .empty => True
  | .extend _ _ r => RecU r
  | _ => False

def labels : U → List String
  | .extend l _ r => l :: labels r
  | _ => []

/-- Well-formed: every extension extends a record chain with a fresh label. -/
def WF : U → Prop
  | .nat | .str | .empty => True
  | .extend l t r => WF t ∧ RecU r ∧ WF r ∧ l ∉ labels r

def Fits : U → V → Prop
  | .nat, .nat _ => True
  | .str, .str _ => True
  | .empty, .list [] => True
  | .extend _ t r, .list (v :: vs) => Fits t v ∧ Fits r (.list vs)
  | _, _ => False

def enc : U → V → Option J
  | .nat, .nat n => some (.num n)
  | .str, .str s => some (.str s)
  | .empty, .list [] => some (.obj [])
  | .extend l t r, .list (v :: vs) =>
    match enc t v, enc r (.list vs) with
    | some j, some (.obj kvs) => some (.obj ((l, j) :: kvs))
    | _, _ => none
  | _, _ => none

def dec : U → J → Option V
  | .nat, .num n => some (.nat n)
  | .str, .str s => some (.str s)
  | .empty, .obj _ => some (.list [])
  | .extend l t r, .obj kvs =>
    match find l kvs with
    | none => none
    | some j =>
      match dec t j, dec r (.obj kvs) with
      | some v, some (.list vs) => some (.list (v :: vs))
      | _, _ => none
  | _, _ => none

/-- The named normaliser: the record's fields in its own order, each normalised, keys it does
not name dropped. -/
def N : U → J → J
  | .empty, .obj _ => .obj []
  | .extend l t r, .obj kvs =>
    match find l kvs, N r (.obj kvs) with
    | some j, .obj rest => .obj ((l, N t j) :: rest)
    | _, other => other
  | _, j => j

/-! ## Retraction on well-formed types -/

theorem find_cons_ne {l k : String} {j : J} {kvs : List (String × J)} (h : k ≠ l) :
    find l ((k, j) :: kvs) = find l kvs := by
  simp only [find, h, if_false]

/-- A key the chain does not name is invisible to its decoder. -/
theorem dec_cons_irrelevant (l : String) (j : J) :
    ∀ (r : U) (kvs : List (String × J)), RecU r → l ∉ labels r →
      dec r (.obj ((l, j) :: kvs)) = dec r (.obj kvs) := by
  intro r
  induction r with
  | empty => intro _ _ _; rfl
  | extend l' t' r' _ ihr =>
    intro kvs hrec hnot
    have hne : l ≠ l' := fun e => hnot (e ▸ List.mem_cons_self)
    have hnot' : l ∉ labels r' := fun m => hnot (List.mem_cons_of_mem _ m)
    simp only [dec, find_cons_ne hne, ihr kvs hrec hnot']
  | nat => intro _ h _; exact h.elim
  | str => intro _ h _; exact h.elim

/-- A record chain encodes to an object. -/
theorem enc_rec_obj : ∀ (r : U) (v : V) (j : J), RecU r → enc r v = some j →
    ∃ kvs, j = .obj kvs := by
  intro r
  induction r with
  | empty =>
    intro v j _ h
    match v, h with
    | .list [], h => simp only [enc, Option.some.injEq] at h; exact ⟨[], h.symm⟩
  | extend l t r _ _ =>
    intro v j _ h
    match v, h with
    | .list (x :: xs), h =>
      simp only [enc] at h
      split at h
      · simp only [Option.some.injEq] at h; exact ⟨_, h.symm⟩
      · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  | nat => intro _ _ h _; exact h.elim
  | str => intro _ _ h _; exact h.elim

theorem dec_enc : ∀ (u : U) (v : V), WF u → Fits u v → ∃ j, enc u v = some j ∧ dec u j = some v := by
  intro u
  induction u with
  | nat =>
    intro v _ hf
    match v, hf with
    | .nat n, _ => exact ⟨.num n, rfl, rfl⟩
  | str =>
    intro v _ hf
    match v, hf with
    | .str s, _ => exact ⟨.str s, rfl, rfl⟩
  | empty =>
    intro v _ hf
    match v, hf with
    | .list [], _ => exact ⟨.obj [], rfl, rfl⟩
  | extend l t r iht ihr =>
    intro v hw hf
    match v, hf with
    | .list (x :: xs), ⟨hx, hxs⟩ =>
      obtain ⟨hwt, hrec, hwr, hfresh⟩ := hw
      obtain ⟨jt, hjt, hdt⟩ := iht x hwt hx
      obtain ⟨jr, hjr, hdr⟩ := ihr (.list xs) hwr hxs
      obtain ⟨kvs, rfl⟩ := enc_rec_obj r (.list xs) jr hrec hjr
      refine ⟨.obj ((l, jt) :: kvs), ?_, ?_⟩
      · simp only [enc, hjt, hjr]
      · have hfind : find l ((l, jt) :: kvs) = some jt := by simp only [find, if_true]
        simp only [dec, hfind, hdt, dec_cons_irrelevant l jt r kvs hrec hfresh, hdr]

/-! ## Exactness modulo `N`, with no premise -/

/-- Whatever a chain decodes, its normal form is an object. -/
theorem N_obj_of_dec : ∀ (r : U) (kvs : List (String × J)) (w : V), dec r (.obj kvs) = some w →
    ∃ rest, N r (.obj kvs) = .obj rest := by
  intro r
  induction r with
  | empty => intro _ _ _; exact ⟨[], rfl⟩
  | extend l t r _ ihr =>
    intro kvs w h
    simp only [dec] at h
    split at h
    · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
    · rename_i j hj
      split at h
      · rename_i v vs _ hr
        obtain ⟨rest, hrest⟩ := ihr kvs (.list vs) hr
        exact ⟨(l, N t j) :: rest, by simp only [N, hj, hrest]⟩
      · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  | nat => intro _ _ h; simp only [dec, reduceCtorEq] at h
  | str => intro _ _ h; simp only [dec, reduceCtorEq] at h

theorem enc_dec : ∀ (u : U) (j : J) (v : V), dec u j = some v → enc u v = some (N u j) := by
  intro u
  induction u with
  | nat =>
    intro j v h
    match j, h with
    | .num n, h => simp only [dec, Option.some.injEq] at h; subst h; rfl
  | str =>
    intro j v h
    match j, h with
    | .str s, h => simp only [dec, Option.some.injEq] at h; subst h; rfl
  | empty =>
    intro j v h
    match j, h with
    | .obj kvs, h => simp only [dec, Option.some.injEq] at h; subst h; rfl
  | extend l t r iht ihr =>
    intro j v h
    match j, h with
    | .obj kvs, h =>
      simp only [dec] at h
      split at h
      · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
      · rename_i jl hfind
        split at h
        · rename_i x xs hx hxs
          simp only [Option.some.injEq] at h
          subst h
          obtain ⟨rest, hrest⟩ := N_obj_of_dec r kvs (.list xs) hxs
          have het := iht jl x hx
          have her := ihr (.obj kvs) (.list xs) hxs
          rw [hrest] at her
          simp only [enc, het, her, N, hfind, hrest]
        · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])

#print axioms dec_enc
#print axioms enc_dec

/-! ## Red controls -/

/-- `{ id: number }`. -/
def idRecord : U := .extend "id" .nat .empty

-- An object with an excess key and the keys in another order decodes (rc.112's default) ...
#guard (match dec idRecord (.obj [("name", .str "x"), ("id", .num 2)]) with
  | some (.list [.nat 2]) => true
  | _ => false)
-- ... and re-encodes to its normal form, not to itself: equality holds only modulo `N`.
#guard (match enc idRecord (.list [.nat 2]) with
  | some (.obj [("id", .num 2)]) => true
  | _ => false)

/-- Two fields under one label: not well-formed. -/
def dupRecord : U := .extend "a" .nat (.extend "a" .nat .empty)

-- Without well-formedness the retraction fails: `[1, 2]` encodes, and decodes to `[1, 1]`.
#guard (match enc dupRecord (.list [.nat 1, .nat 2]) with
  | some j => (match dec dupRecord j with | some (.list [.nat 1, .nat 1]) => true | _ => false)
  | none => false)

end Probe.RecordK2
