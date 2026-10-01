import Effect4.Machine.Term
import Effect4.Program.Ty

/-!
# Seat R, question 4: the boundary projection (route A) against the strict codec

Type-language probe, 2026-10-01. A model, not the tree. `MJson` is the tree's JSON carrier
(`Data/Json.lean:288-300`: objects as ordered entry lists that keep duplicates) with numbers as
naturals; `MTy` and positional record values are `Q1Positional.lean`'s.

One fold, `conv strict`, reads a JSON value at a type; at a record it asks, for each canonical
field, for exactly one entry of that name, and lays the values out in canonical order:
* `conv true` is the strict codec (`Schema/Codec.lean:74-82`, the S-3 contract's strict field
  set): it also refuses any entry the type does not name, so extra and duplicate keys refuse;
* `conv false` is the row adapter of route A (`host-boundary.md` §7): it drops entries the type
  does not name.

What it shows (proved unless marked):
1. the codec's acceptances are the adapter's, with the same value (`codec_sub_adapt`);
2. whatever the adapter accepts is a member of the row's type, which is what the session's reply
   check needs (`adapt_member`);
3. the paired control: one object with an extra key, stripped by the adapter and refused by the
   codec (`paired_control`); missing and duplicate declared keys are refused by both (tested);
4. the adapter is a projection, not an exact embedding: the stripped key does not come back
   (`adapter_not_exact`).
-/

set_option autoImplicit false

namespace SeatR.Boundary

open Effect4.Machine

/-! ## 1. Names, their order, the canonical field list -/

/-- The UTF-8 byte order on names: the key order `Ty.key` uses for a `lit` (`Ty.lean:155-176`). -/
def nameLt (a b : String) : Bool :=
  Effect4.Program.Ty.ltKey (Effect4.Program.Ty.key (.lit a)) (Effect4.Program.Ty.key (.lit b))

/-- Insert by name; an equal name already present wins, so a left fold keeps the first. -/
def ins {α : Type} (p : String × α) : List (String × α) → List (String × α)
  | [] => [p]
  | q :: qs => if nameLt p.1 q.1 then p :: q :: qs else if p.1 = q.1 then q :: qs else q :: ins p qs

/-- Canonical field order: ascending by name, the first of a repeated name kept. -/
def canon {α : Type} (xs : List (String × α)) : List (String × α) :=
  xs.foldl (fun acc p => ins p acc) []

theorem ins_map {α β : Type} (f : α → β) (p : String × α) (l : List (String × α)) :
    ins (p.1, f p.2) (l.map (fun q => (q.1, f q.2))) = (ins p l).map (fun q => (q.1, f q.2)) := by
  induction l with
  | nil => rfl
  | cons q qs ih =>
    by_cases h1 : nameLt p.1 q.1 = true
    · simp only [List.map_cons, ins, if_pos h1]
    · by_cases h2 : p.1 = q.1
      · simp only [List.map_cons, ins, if_neg h1, if_pos h2]
      · simp only [List.map_cons, ins, if_neg h1, if_neg h2, ih]

theorem foldl_ins_map {α β : Type} (f : α → β) (xs acc : List (String × α)) :
    (xs.map (fun q => (q.1, f q.2))).foldl (fun a p => ins p a) (acc.map (fun q => (q.1, f q.2))) =
      (xs.foldl (fun a p => ins p a) acc).map (fun q => (q.1, f q.2)) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [ins_map f x acc]
    exact ih (ins x acc)

/-- The canonicaliser is payload-polymorphic: it commutes with any map of the payloads. -/
theorem canon_map {α β : Type} (f : α → β) (xs : List (String × α)) :
    canon (xs.map (fun q => (q.1, f q.2))) = (canon xs).map (fun q => (q.1, f q.2)) :=
  foldl_ins_map f xs []

theorem mem_ins {α : Type} (p x : String × α) (l : List (String × α)) (h : x ∈ ins p l) :
    x = p ∨ x ∈ l := by
  induction l with
  | nil =>
    simp only [ins, List.mem_singleton] at h
    exact Or.inl h
  | cons q qs ih =>
    by_cases h1 : nameLt p.1 q.1 = true
    · simp only [ins, if_pos h1, List.mem_cons] at h
      rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons.mpr (Or.inl h))
      · exact Or.inr (List.mem_cons.mpr (Or.inr h))
    · by_cases h2 : p.1 = q.1
      · simp only [ins, if_neg h1, if_pos h2] at h
        exact Or.inr h
      · simp only [ins, if_neg h1, if_neg h2, List.mem_cons] at h
        rcases h with h | h
        · exact Or.inr (List.mem_cons.mpr (Or.inl h))
        · rcases ih h with h' | h'
          · exact Or.inl h'
          · exact Or.inr (List.mem_cons.mpr (Or.inr h'))

theorem mem_foldl_ins {α : Type} (x : String × α) (xs acc : List (String × α))
    (h : x ∈ xs.foldl (fun a p => ins p a) acc) : x ∈ acc ∨ x ∈ xs := by
  induction xs generalizing acc with
  | nil => exact Or.inl h
  | cons y ys ih =>
    simp only [List.foldl_cons] at h
    rcases ih (ins y acc) h with h' | h'
    · rcases mem_ins y x acc h' with h'' | h''
      · exact Or.inr (List.mem_cons.mpr (Or.inl h''))
      · exact Or.inl h''
    · exact Or.inr (List.mem_cons.mpr (Or.inr h'))

/-- Every field of the canonical list is a field of the input. -/
theorem mem_canon {α : Type} (x : String × α) (xs : List (String × α)) (h : x ∈ canon xs) :
    x ∈ xs := by
  rcases mem_foldl_ins x xs [] h with h' | h'
  · cases h'
  · exact h'

/-- The value of a name in a field list, first match. -/
def lookupName {α : Type} (n : String) : List (String × α) → Option α
  | [] => none
  | (m, a) :: rest => if m = n then some a else lookupName n rest


/-! ## 2. JSON, types, membership -/

inductive MJson where
  | null
  | bool (b : Bool)
  | num (n : Nat)
  | str (s : String)
  | arr (xs : List MJson)
  | obj (entries : List (String × MJson))

inductive MTy where
  | unit
  | nat
  | string
  | bool
  | lit (s : String)
  | record (fields : List (String × MTy))

/-- The nested eliminator (the `Json.ind`/`Val.ind` idiom; the data synthesis's `T.ind'`). -/
theorem MTy.ind' {motive : MTy → Prop} (unit : motive .unit) (nat : motive .nat)
    (string : motive .string) (bool : motive .bool) (lit : ∀ s, motive (.lit s))
    (record : ∀ fs, (∀ p ∈ fs, motive p.2) → motive (.record fs)) : ∀ t, motive t :=
  fun t =>
    MTy.rec (motive_1 := motive) (motive_2 := fun fs => ∀ p ∈ fs, motive p.2)
      (motive_3 := fun p => motive p.2)
      unit nat string bool lit record
      (by intro _ hmem; cases hmem)
      (fun _ _ ihHead ihTail => by
        intro _ hmem
        cases hmem with
        | head => exact ihHead
        | tail _ hmem' => exact ihTail _ hmem')
      (fun _ _ ih => ih)
      t

def fitPos : List Val → List (String × (Val → Bool)) → Bool
  | [], [] => true
  | v :: vs, (_, c) :: cs => c v && fitPos vs cs
  | _, _ => false

mutual
def hasTy : MTy → Val → Bool
  | .unit, v => match v with | .unit => true | _ => false
  | .nat, v => match v with | .nat _ => true | _ => false
  | .string, v => match v with | .str _ => true | _ => false
  | .bool, v => match v with | .bool _ => true | _ => false
  | .lit s, v => match v with | .str t => decide (t = s) | _ => false
  | .record fs, v => match v with | .ctor 0 vs => fitPos vs (canon (checks fs)) | _ => false
def checks : List (String × MTy) → List (String × (Val → Bool))
  | [] => []
  | (n, t) :: fs => (n, hasTy t) :: checks fs
end

theorem checks_eq_map (fs : List (String × MTy)) :
    checks fs = fs.map (fun p => (p.1, hasTy p.2)) := by
  induction fs with
  | nil => rfl
  | cons p fs ih =>
    obtain ⟨n, t⟩ := p
    simp only [checks, List.map_cons, ih]

/-! ## 3. One fold, two policies -/

/-- The entries of an object carrying one name. -/
def named (n : String) (entries : List (String × MJson)) : List MJson :=
  (entries.filter (fun e => decide (e.1 = n))).map Prod.snd

/-- The one entry of a list that must have exactly one. -/
def one : List MJson → Option MJson
  | [x] => some x
  | _ => none

theorem one_eq_some {xs : List MJson} {x : MJson} (h : one xs = some x) : xs = [x] := by
  unfold one at h
  split at h
  · simp only [Option.some.injEq] at h
    rw [h]
  · exact nomatch h

/-- Exactly one entry per canonical field, read by the field's reader. -/
def readFields (entries : List (String × MJson)) :
    List (String × (MJson → Option Val)) → Option (List Val)
  | [] => some []
  | (n, rd) :: rest => do
    let x ← one (named n entries)
    let v ← rd x
    let vs ← readFields entries rest
    some (v :: vs)

mutual
/-- `strict = true`: the codec. `strict = false`: the row adapter. -/
def conv (strict : Bool) : MTy → MJson → Option Val
  | .unit, j => match j with | .null => some .unit | _ => none
  | .nat, j => match j with | .num n => some (.nat n) | _ => none
  | .string, j => match j with | .str s => some (.str s) | _ => none
  | .bool, j => match j with | .bool b => some (.bool b) | _ => none
  | .lit s, j => match j with | .str t => if t = s then some (.str t) else none | _ => none
  | .record fs, j =>
    match j with
    | .obj entries =>
      if strict && entries.length != fs.length then none
      else (readFields entries (canon (readers strict fs))).map (.ctor 0)
    | _ => none
def readers (strict : Bool) : List (String × MTy) → List (String × (MJson → Option Val))
  | [] => []
  | (n, t) :: fs => (n, conv strict t) :: readers strict fs
end

def decode : MTy → MJson → Option Val := conv true
def adapt : MTy → MJson → Option Val := conv false

theorem readers_eq_map (strict : Bool) (fs : List (String × MTy)) :
    readers strict fs = fs.map (fun p => (p.1, conv strict p.2)) := by
  induction fs with
  | nil => rfl
  | cons p fs ih =>
    obtain ⟨n, t⟩ := p
    simp only [readers, List.map_cons, ih]

/-- `readFields` over a mapped list, position by position. -/
theorem readFields_map (entries : List (String × MJson)) (M : List (String × MTy))
    (rd : MTy → MJson → Option Val) (vs : List Val)
    (h : readFields entries (M.map (fun p => (p.1, rd p.2))) = some vs) :
    ∀ (i : Nat) (p : String × MTy), M[i]? = some p →
      ∃ x v, named p.1 entries = [x] ∧ rd p.2 x = some v ∧ vs[i]? = some v := by
  induction M generalizing vs with
  | nil => intro i p hp; simp only [List.getElem?_nil, reduceCtorEq] at hp
  | cons q M ih =>
    simp only [List.map_cons, readFields, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, v, hv, rest, hrest, hvs⟩ := h
    simp only [Option.some.injEq] at hvs
    subst hvs
    intro i p hp
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hp
      subst hp
      exact ⟨x, v, one_eq_some hx, hv, rfl⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at hp ⊢
      exact ih rest hrest i p hp

theorem fitPos_of_pointwise (M : List (String × MTy)) (vs : List Val)
    (hlen : vs.length = M.length)
    (h : ∀ (i : Nat) (p : String × MTy) (v : Val), M[i]? = some p → vs[i]? = some v → hasTy p.2 v = true) :
    fitPos vs (M.map (fun p => (p.1, hasTy p.2))) = true := by
  induction M generalizing vs with
  | nil =>
    cases vs with
    | nil => rfl
    | cons v vs => exact absurd hlen (Nat.succ_ne_zero _)
  | cons q M ih =>
    cases vs with
    | nil => exact absurd hlen (Nat.succ_ne_zero _).symm
    | cons v vs =>
      simp only [List.map_cons, fitPos, Bool.and_eq_true]
      refine ⟨h 0 q v rfl rfl, ih vs (Nat.succ.inj hlen) (fun i p w hp hw => h (i + 1) p w hp hw)⟩

theorem readFields_length (entries : List (String × MJson)) (L : List (String × (MJson → Option Val)))
    (vs : List Val) (h : readFields entries L = some vs) : vs.length = L.length := by
  induction L generalizing vs with
  | nil =>
    simp only [readFields, Option.some.injEq] at h
    subst h
    rfl
  | cons q L ih =>
    obtain ⟨n, rd⟩ := q
    simp only [readFields, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, v, _, rest, hrest, hvs⟩ := h
    simp only [Option.some.injEq] at hvs
    subst hvs
    simp only [List.length_cons, ih rest hrest]

/-! ## 4. The laws -/

/-- What either policy accepts is a member of the type: the session's reply check holds. -/
theorem conv_member (strict : Bool) : ∀ (t : MTy) (j : MJson) (v : Val),
    conv strict t j = some v → hasTy t v = true := by
  intro t
  induction t using MTy.ind' with
  | unit => intro j v h; cases j <;> simp only [conv, Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl
  | nat => intro j v h; cases j <;> simp only [conv, Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl
  | string => intro j v h; cases j <;> simp only [conv, Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl
  | bool => intro j v h; cases j <;> simp only [conv, Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl
  | lit s =>
    intro j v h
    cases j with
    | str t =>
      simp only [conv] at h
      split at h
      · rename_i hts
        simp only [Option.some.injEq] at h
        subst h
        simp only [hasTy, hts, decide_true]
      · exact nomatch h
    | _ => simp only [conv, reduceCtorEq] at h
  | record fs ih =>
    intro j v h
    cases j with
    | obj entries =>
      simp only [conv] at h
      split at h
      · exact nomatch h
      · obtain ⟨vs, hvs, rfl⟩ := Option.map_eq_some_iff.mp h
        rw [readers_eq_map, canon_map (conv strict) fs] at hvs
        simp only [hasTy, checks_eq_map, canon_map hasTy fs]
        have hpt := readFields_map entries (canon fs) (conv strict) vs hvs
        have hlen := readFields_length entries _ vs hvs
        rw [List.length_map] at hlen
        refine fitPos_of_pointwise (canon fs) vs hlen (fun i p w hp hw => ?_)
        obtain ⟨x, w', _, hw', hi⟩ := hpt i p hp
        rw [hw, Option.some.injEq] at hi
        subst hi
        exact ih p (mem_canon p fs (List.mem_of_getElem? hp)) x w hw'
    | _ => simp only [conv, reduceCtorEq] at h

theorem adapt_member (t : MTy) (j : MJson) (v : Val) (h : adapt t j = some v) : hasTy t v = true :=
  conv_member false t j v h

/-- `readFields` with pointwise-related readers. -/
theorem readFields_mono (entries : List (String × MJson)) (M : List (String × MTy))
    (rd₁ rd₂ : MTy → MJson → Option Val)
    (hrd : ∀ p ∈ M, ∀ x v, rd₁ p.2 x = some v → rd₂ p.2 x = some v) (vs : List Val)
    (h : readFields entries (M.map (fun p => (p.1, rd₁ p.2))) = some vs) :
    readFields entries (M.map (fun p => (p.1, rd₂ p.2))) = some vs := by
  induction M generalizing vs with
  | nil => exact h
  | cons q M ih =>
    simp only [List.map_cons, readFields, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨x, hx, v, hv, rest, hrest, hvs⟩ := h
    refine ⟨x, hx, v, hrd q (List.mem_cons_self) x v hv, rest, ?_, hvs⟩
    exact ih (fun p hp => hrd p (List.mem_cons_of_mem q hp)) rest hrest

/-- The codec's acceptances are the adapter's, with the same value. -/
theorem codec_sub_adapt : ∀ (t : MTy) (j : MJson) (v : Val), decode t j = some v → adapt t j = some v := by
  intro t
  induction t using MTy.ind' with
  | unit => intro j v h; exact h
  | nat => intro j v h; exact h
  | string => intro j v h; exact h
  | bool => intro j v h; exact h
  | lit s => intro j v h; exact h
  | record fs ih =>
    intro j v h
    cases j with
    | obj entries =>
      simp only [decode, adapt, conv] at h ⊢
      split at h
      · exact nomatch h
      · obtain ⟨vs, hvs, rfl⟩ := Option.map_eq_some_iff.mp h
        rw [readers_eq_map, canon_map (conv true) fs] at hvs
        simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, readers_eq_map,
          canon_map (conv false) fs]
        rw [readFields_mono entries (canon fs) (conv true) (conv false)
          (fun p hp x w hw => ih p (mem_canon p fs hp) x w hw) vs hvs]
        rfl
    | _ => simp only [decode, conv, reduceCtorEq] at h

/-! ## 5. The paired control, on p2's `User` -/

def userTy : MTy := .record [("id", .nat), ("name", .string), ("role", .string)]
def bob : Val := .ctor 0 [.nat 2, .str "bob", .str "member"]
/-- What rc.112's host hands back for a row of a wider table: one more column. -/
def wider : MJson := .obj [("role", .str "member"), ("id", .num 2), ("extra", .num 1), ("name", .str "bob")]
def exact : MJson := .obj [("name", .str "bob"), ("role", .str "member"), ("id", .num 2)]
def missing : MJson := .obj [("id", .num 2), ("name", .str "bob")]
def duplicate : MJson := .obj [("id", .num 2), ("name", .str "bob"), ("role", .str "member"), ("id", .num 3)]

/-- The adapter strips the extra key; the codec refuses it. -/
theorem paired_control : adapt userTy wider = some bob ∧ decode userTy wider = none := by
  constructor <;> rfl

-- the exact object in any order: both accept, with the same value
#guard (adapt userTy exact).isSome && (decode userTy exact).isSome
#guard (adapt userTy exact).map (fun v => hasTy userTy v) == some true
-- a missing declared key and a duplicated declared key: both refuse
#guard (adapt userTy missing).isNone && (decode userTy missing).isNone
#guard (adapt userTy duplicate).isNone && (decode userTy duplicate).isNone
-- a duplicated undeclared key: the adapter drops both, the codec refuses
#guard (adapt userTy (.obj [("id", .num 2), ("x", .num 0), ("name", .str "bob"), ("x", .num 1), ("role", .str "a")])).isSome
#guard (decode userTy (.obj [("id", .num 2), ("x", .num 0), ("name", .str "bob"), ("x", .num 1), ("role", .str "a")])).isNone
-- nesting: the adapter strips at every depth, the codec refuses at every depth
def resp : MTy := .record [("status", .nat), ("user", userTy)]
#guard adapt resp (.obj [("user", wider), ("status", .num 200)]) == some (.ctor 0 [.nat 200, bob])
#guard (decode resp (.obj [("user", wider), ("status", .num 200)])).isNone

/-! ## 6. The adapter is a projection, not an exact embedding -/

/-- The canonical object of a record value (the codec's encoder at a flat record of leaves). -/
def encodeLeaf : MTy → Val → Option MJson
  | .nat, .nat n => some (.num n)
  | .string, .str s => some (.str s)
  | _, _ => none

def encodeFlat (fs : List (String × MTy)) (v : Val) : Option MJson :=
  match v with
  | .ctor 0 vs => do
    let js ← ((canon fs).zip vs).mapM (fun p => encodeLeaf p.1.2 p.2)
    some (.obj ((canon fs).map Prod.fst |>.zip js))
  | _ => none

def keyCount : MJson → Nat
  | .obj entries => entries.length
  | _ => 0

def bobCanon : MJson := .obj [("id", .num 2), ("name", .str "bob"), ("role", .str "member")]

/-- What the adapter dropped does not come back: no normaliser of key order recovers `wider`. -/
theorem adapter_not_exact :
    (adapt userTy wider).bind (encodeFlat [("id", .nat), ("name", .string), ("role", .string)]) =
      some bobCanon ∧ keyCount bobCanon ≠ keyCount wider := by
  exact ⟨rfl, by decide⟩

end SeatR.Boundary

#print axioms SeatR.Boundary.MTy.ind'
#print axioms SeatR.Boundary.conv_member
#print axioms SeatR.Boundary.adapt_member
#print axioms SeatR.Boundary.codec_sub_adapt
#print axioms SeatR.Boundary.paired_control
#print axioms SeatR.Boundary.adapter_not_exact
