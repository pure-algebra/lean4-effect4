import OCaml5.Lib.Order

/-!
# `OCaml5.Lib.Map` — the carrier for `Base.Map`

Status: seat W4 of the 2026-09-04 wave. Plan: `docs/research/2026-09-04-ocaml-packages-plan.md`
§4.2. Report: `docs/research/2026-09-04-seat-w4-library-carriers.md`.

A `Base.Map.t` is a balanced binary tree; this carrier is the **strictly ascending association
list**, which is `Base.Map.to_alist` of that tree. The tree shape is deliberately not modelled:
nothing the avatar, the daemon or the codegen claims can observe it, and the plan's rule is that
a carrier states what we rely on and refuses the rest. The invariant is carried in the type
(`Map.wf`), so a `Map` **is** its canonical form and two maps with the same bindings are equal —
that is `Map.ext_find`, and it is what "insertion-independent canonical form" means here.

## Named properties (theorem names are stable; cite these)

* `Map.find_set_same` — `find (set m k v) k = some v`.
* `Map.find_set_other` — `k' ≠ k → find (set m k v) k' = find m k'`.
* `Map.find_remove_same` — `find (remove m k) k = none`.
* `Map.find_remove_other` — `k' ≠ k → find (remove m k) k' = find m k'`.
* `Map.find_empty` — `find empty k = none`.
* `Map.ext_find` — two maps that answer `find` alike are equal (canonical form).
* `Map.set_comm` — `set` at two distinct keys commutes (insertion independence).
* `Map.set_set_same` — the later `set` at one key wins.
* `Map.keys_sorted` — the key list is strictly ascending.
* `Map.keys_nodup` — hence every key occurs exactly once.
* `Map.fold_visits_keys_in_order` — `fold` accumulating the keys reproduces `keys`: each key
  once, in key order.
* `Map.fold_length` — `fold` performs exactly `length` steps.
* `Map.toAlist_sorted` — `to_alist` is strictly ascending by key.
* `Map.ofAlist_toAlist` — `of_alist ∘ to_alist = id`.
* `Map.find_toAlist` — `to_alist` carries the same bindings as `find`.
* `Map.find_merge` — `find (merge f m₁ m₂) k = f k (find m₁ k) (find m₂ k)`, given
  `f k none none = none`.

## What each definition stands for

| here | `Base` | the law we rely on |
| --- | --- | --- |
| `Map.empty` | `Map.empty ~comparator` | `find_empty` |
| `Map.find` | `Map.find : ('k,'v,_) t -> 'k -> 'v option` | `find_set_same`, `find_set_other` |
| `Map.set` | `Map.set : t -> key:'k -> data:'v -> t` | `find_set_same`, `find_set_other`, `set_comm` |
| `Map.remove` | `Map.remove : t -> 'k -> t` | `find_remove_same`, `find_remove_other` |
| `Map.fold` | `Map.fold : t -> init:'a -> f:(key:_ -> data:_ -> 'a -> 'a) -> 'a`, documented "in increasing order of key" | `fold_visits_keys_in_order` |
| `Map.toAlist` | `Map.to_alist ?key_order:\`Increasing` (the default) | `toAlist_sorted`, `find_toAlist` |
| `Map.ofAlist` | `Map.of_alist_reduce ~f:(fun _ later -> later)` — **not** `of_alist_exn`, which raises on a duplicate key; the carrier's total function keeps the *last* binding | `ofAlist_toAlist` |
| `Map.merge` | `Map.merge : t -> t -> f:(key:_ -> [`Left of _ | `Right of _ | `Both of _ * _] -> 'c option) -> 'c t`, here in its `Option`-pair form | `find_merge` |
| `Map.keys` | `Map.keys` (increasing) | `keys_sorted`, `keys_nodup` |
| `Map.length` | `Map.length` | `fold_length` |

## Refusals

* **`Map.min_elt` / `max_elt` / `nth` / `rank` / the `Tree` module.** No carrier; they expose the
  tree order beyond the key order. Refusal row `W4-MAP-TREE-ORDER`.
* **`Map.of_alist_exn` and the `` `Duplicate_key `` result.** The carrier is total, so the
  exception-raising and result-returning constructors are one total `ofAlist` with a stated
  tie-break. Code that needs the *rejection* must check for duplicates itself. Refusal row
  `W4-MAP-OF-ALIST-EXN`.
* **`Map.comparator_s` / the phantom comparator witness.** `LinOrd` is a class, not a value, so
  two maps at the same key type always share an order here; OCaml can hold two maps under two
  different comparators for one key type. Refusal row `W4-MAP-COMPARATOR-VALUE`.
* **Physical sharing / `Map.merge_skewed`'s complexity promise.** Not observable. Refusal row
  `W4-MAP-SHARING`.
-/

set_option autoImplicit false

namespace OCaml5.Lib

universe u v w z

variable {κ : Type u} {α : Type v} {β : Type w}

/-! ## The invariant, on the raw association list -/

/-- Strictly ascending by key: adjacent keys compare `lt`. -/
def strictAsc [LinOrd κ] : List (κ × α) → Bool
  | [] => true
  | [_] => true
  | a :: b :: r => decide (LinOrd.cmp a.1 b.1 = .lt) && strictAsc (b :: r)

/-- The head key is below the head key of the tail, if any. -/
def headLt [LinOrd κ] (k : κ) : List (κ × α) → Prop
  | [] => True
  | b :: _ => LinOrd.cmp k b.1 = .lt

variable [LinOrd κ]

theorem strictAsc_cons {e : κ × α} {r : List (κ × α)} :
    strictAsc (e :: r) = true ↔ headLt e.1 r ∧ strictAsc r = true := by
  cases r with
  | nil => simp [strictAsc, headLt]
  | cons b r' => simp [strictAsc, headLt]

theorem strictAsc_of_cons {e : κ × α} {r : List (κ × α)} (h : strictAsc (e :: r) = true) :
    strictAsc r = true := (strictAsc_cons.mp h).2

/-- The head key is strictly below **every** key of the tail: adjacent ascent plus transitivity.
-/
theorem strictAsc_head_lt :
    ∀ {e : κ × α} {r : List (κ × α)}, strictAsc (e :: r) = true →
      ∀ x ∈ r, LinOrd.cmp e.1 x.1 = .lt
  | _, [], _, _, hx => by cases hx
  | e, b :: r', h, x, hx => by
    have h' := strictAsc_cons.mp h
    have hb : LinOrd.cmp e.1 b.1 = .lt := h'.1
    cases hx with
    | head => exact hb
    | tail _ hx' => exact LinOrd.cmp_trans_lt hb (strictAsc_head_lt h'.2 x hx')

/-! ## Lookup on the raw list -/

/-- `Base.Map.find`, on the association list. -/
def findIn (k : κ) : List (κ × α) → Option α
  | [] => none
  | e :: r => if LinOrd.cmp k e.1 = .eq then some e.2 else findIn k r

theorem findIn_nil (k : κ) : findIn (α := α) k [] = none := rfl

theorem findIn_cons_eq {k : κ} {e : κ × α} {r : List (κ × α)}
    (h : LinOrd.cmp k e.1 = .eq) : findIn k (e :: r) = some e.2 := by
  simp [findIn, h]

theorem findIn_cons_ne {k : κ} {e : κ × α} {r : List (κ × α)}
    (h : LinOrd.cmp k e.1 ≠ .eq) : findIn k (e :: r) = findIn k r := by
  simp [findIn, h]

/-- A key below everything in the list is not in it. -/
theorem findIn_none_of_all_lt {k : κ} :
    ∀ {l : List (κ × α)}, (∀ x ∈ l, LinOrd.cmp k x.1 = .lt) → findIn k l = none
  | [], _ => rfl
  | e :: r, h => by
    have he : LinOrd.cmp k e.1 = .lt := h e (List.mem_cons_self ..)
    rw [findIn_cons_ne (by rw [he]; intro hc; cases hc)]
    exact findIn_none_of_all_lt fun x hx => h x (List.mem_cons_of_mem _ hx)

/-- A key above everything in the list is not in it. -/
theorem findIn_none_of_all_gt {k : κ} :
    ∀ {l : List (κ × α)}, (∀ x ∈ l, LinOrd.cmp k x.1 = .gt) → findIn k l = none
  | [], _ => rfl
  | e :: r, h => by
    have he : LinOrd.cmp k e.1 = .gt := h e (List.mem_cons_self ..)
    rw [findIn_cons_ne (by rw [he]; intro hc; cases hc)]
    exact findIn_none_of_all_gt fun x hx => h x (List.mem_cons_of_mem _ hx)

/-! ## Insertion and removal on the raw list -/

/-- `Base.Map.set`, on the association list: sorted insert, replacing an equal key. -/
def insertIn (k : κ) (v : α) : List (κ × α) → List (κ × α)
  | [] => [(k, v)]
  | e :: r =>
    match LinOrd.cmp k e.1 with
    | .lt => (k, v) :: e :: r
    | .eq => (k, v) :: r
    | .gt => e :: insertIn k v r

/-- `Base.Map.remove`, on the association list. -/
def removeIn (k : κ) : List (κ × α) → List (κ × α)
  | [] => []
  | e :: r =>
    match LinOrd.cmp k e.1 with
    | .lt => e :: r
    | .eq => r
    | .gt => e :: removeIn k r

theorem insertIn_nil (k : κ) (v : α) : insertIn k v ([] : List (κ × α)) = [(k, v)] := rfl

theorem insertIn_cons_lt {k : κ} {v : α} {e : κ × α} {r : List (κ × α)}
    (h : LinOrd.cmp k e.1 = .lt) : insertIn k v (e :: r) = (k, v) :: e :: r := by
  simp only [insertIn, h]

theorem insertIn_cons_eq {k : κ} {v : α} {e : κ × α} {r : List (κ × α)}
    (h : LinOrd.cmp k e.1 = .eq) : insertIn k v (e :: r) = (k, v) :: r := by
  simp only [insertIn, h]

theorem insertIn_cons_gt {k : κ} {v : α} {e : κ × α} {r : List (κ × α)}
    (h : LinOrd.cmp k e.1 = .gt) : insertIn k v (e :: r) = e :: insertIn k v r := by
  simp only [insertIn, h]

theorem headLt_insertIn {j k : κ} {v : α} (hjk : LinOrd.cmp j k = .lt) :
    ∀ {l : List (κ × α)}, headLt j l → headLt j (insertIn k v l)
  | [], _ => hjk
  | e :: r, h => by
    unfold insertIn
    cases hk : LinOrd.cmp k e.1 with
    | lt => exact hjk
    | eq => exact hjk
    | gt => exact h

theorem strictAsc_insertIn (k : κ) (v : α) :
    ∀ {l : List (κ × α)}, strictAsc l = true → strictAsc (insertIn k v l) = true
  | [], _ => rfl
  | e :: r, h => by
    have h' := strictAsc_cons.mp h
    unfold insertIn
    cases hk : LinOrd.cmp k e.1 with
    | lt => exact strictAsc_cons.mpr ⟨hk, h⟩
    | eq =>
      have : e.1 = k := (LinOrd.eq_of_cmp_eq hk).symm
      exact strictAsc_cons.mpr ⟨this ▸ h'.1, h'.2⟩
    | gt =>
      refine strictAsc_cons.mpr ⟨?_, strictAsc_insertIn k v h'.2⟩
      exact headLt_insertIn (by rw [LinOrd.cmp_swap, hk]; rfl) h'.1

theorem headLt_removeIn {j k : κ} :
    ∀ {l : List (κ × α)}, strictAsc l = true → headLt j l → headLt j (removeIn k l)
  | [], _, h => h
  | e :: r, hs, h => by
    unfold removeIn
    cases hk : LinOrd.cmp k e.1 with
    | lt => exact h
    | eq =>
      cases r with
      | nil => exact True.intro
      | cons b r' =>
        have hb : LinOrd.cmp e.1 b.1 = .lt := (strictAsc_cons.mp hs).1
        exact LinOrd.cmp_trans_lt h hb
    | gt => exact h

theorem strictAsc_removeIn (k : κ) :
    ∀ {l : List (κ × α)}, strictAsc l = true → strictAsc (removeIn k l) = true
  | [], _ => rfl
  | e :: r, h => by
    have h' := strictAsc_cons.mp h
    unfold removeIn
    cases hk : LinOrd.cmp k e.1 with
    | lt => exact h
    | eq => exact h'.2
    | gt =>
      exact strictAsc_cons.mpr
        ⟨headLt_removeIn h'.2 h'.1, strictAsc_removeIn k h'.2⟩

theorem findIn_insertIn_same (k : κ) (v : α) :
    ∀ l : List (κ × α), findIn k (insertIn k v l) = some v
  | [] => by simp [insertIn, findIn, LinOrd.cmp_self]
  | e :: r => by
    unfold insertIn
    cases hk : LinOrd.cmp k e.1 with
    | lt => simp [findIn, LinOrd.cmp_self]
    | eq => simp [findIn, LinOrd.cmp_self]
    | gt =>
      rw [findIn_cons_ne (by rw [hk]; intro hc; cases hc)]
      exact findIn_insertIn_same k v r

theorem findIn_insertIn_other {k k' : κ} (v : α) (h : LinOrd.cmp k' k ≠ .eq) :
    ∀ l : List (κ × α), findIn k' (insertIn k v l) = findIn k' l
  | [] => by simp [insertIn, findIn, h]
  | e :: r => by
    unfold insertIn
    cases hk : LinOrd.cmp k e.1 with
    | lt => rw [findIn_cons_ne h]
    | eq =>
      have hek : e.1 = k := (LinOrd.eq_of_cmp_eq hk).symm
      rw [findIn_cons_ne h, findIn_cons_ne (by rw [hek]; exact h)]
    | gt =>
      by_cases he : LinOrd.cmp k' e.1 = .eq
      · rw [findIn_cons_eq he, findIn_cons_eq he]
      · rw [findIn_cons_ne he, findIn_cons_ne he]
        exact findIn_insertIn_other v h r

theorem findIn_removeIn_same (k : κ) :
    ∀ {l : List (κ × α)}, strictAsc l = true → findIn k (removeIn k l) = none
  | [], _ => rfl
  | e :: r, hs => by
    unfold removeIn
    cases hk : LinOrd.cmp k e.1 with
    | lt =>
      refine findIn_none_of_all_lt (fun x hx => ?_)
      cases hx with
      | head => exact hk
      | tail _ hx' => exact LinOrd.cmp_trans_lt hk (strictAsc_head_lt hs x hx')
    | eq =>
      have hek : e.1 = k := (LinOrd.eq_of_cmp_eq hk).symm
      refine findIn_none_of_all_lt (fun x hx => ?_)
      have := strictAsc_head_lt hs x hx
      rwa [hek] at this
    | gt =>
      rw [findIn_cons_ne (by rw [hk]; intro hc; cases hc)]
      exact findIn_removeIn_same k (strictAsc_of_cons hs)

theorem findIn_removeIn_other {k k' : κ} (h : LinOrd.cmp k' k ≠ .eq) :
    ∀ l : List (κ × α), findIn k' (removeIn k l) = findIn k' l
  | [] => rfl
  | e :: r => by
    unfold removeIn
    cases hk : LinOrd.cmp k e.1 with
    | lt => rfl
    | eq =>
      have hek : e.1 = k := (LinOrd.eq_of_cmp_eq hk).symm
      rw [findIn_cons_ne (by rw [hek]; exact h)]
    | gt =>
      by_cases he : LinOrd.cmp k' e.1 = .eq
      · rw [findIn_cons_eq he, findIn_cons_eq he]
      · rw [findIn_cons_ne he, findIn_cons_ne he]
        exact findIn_removeIn_other h r

/-- **Canonical form, on the raw list.** Two strictly ascending association lists that answer
`findIn` alike are the same list. -/
theorem entries_ext :
    ∀ {l₁ l₂ : List (κ × α)}, strictAsc l₁ = true → strictAsc l₂ = true →
      (∀ k, findIn k l₁ = findIn k l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], b :: r₂, _, _, h => by
    have := h b.1
    rw [findIn_nil, findIn_cons_eq (LinOrd.cmp_self b.1)] at this
    cases this
  | a :: r₁, [], _, _, h => by
    have := h a.1
    rw [findIn_nil, findIn_cons_eq (LinOrd.cmp_self a.1)] at this
    cases this
  | a :: r₁, b :: r₂, h₁, h₂, h => by
    have key : LinOrd.cmp a.1 b.1 = .eq := by
      rcases LinOrd.cmp_total a.1 b.1 with hc | hc | hc
      · exfalso
        have hnone : findIn a.1 (b :: r₂) = none := by
          refine findIn_none_of_all_lt (fun x hx => ?_)
          cases hx with
          | head => exact hc
          | tail _ hx' => exact LinOrd.cmp_trans_lt hc (strictAsc_head_lt h₂ x hx')
        have := h a.1
        rw [findIn_cons_eq (LinOrd.cmp_self a.1), hnone] at this
        cases this
      · exact hc
      · exfalso
        have hba : LinOrd.cmp b.1 a.1 = .lt := by
          rw [LinOrd.cmp_swap, hc]; rfl
        have hnone : findIn b.1 (a :: r₁) = none := by
          refine findIn_none_of_all_lt (fun x hx => ?_)
          cases hx with
          | head => exact hba
          | tail _ hx' => exact LinOrd.cmp_trans_lt hba (strictAsc_head_lt h₁ x hx')
        have := h b.1
        rw [findIn_cons_eq (LinOrd.cmp_self b.1), hnone] at this
        cases this
    have hkey : a.1 = b.1 := LinOrd.eq_of_cmp_eq key
    have hdata : a.2 = b.2 := by
      have := h a.1
      rw [findIn_cons_eq (LinOrd.cmp_self a.1),
        findIn_cons_eq (show LinOrd.cmp a.1 b.1 = .eq from key)] at this
      exact Option.some.inj this
    have hab : a = b := Prod.ext hkey hdata
    subst hab
    refine congrArg (a :: ·) (entries_ext (strictAsc_of_cons h₁) (strictAsc_of_cons h₂) ?_)
    intro k
    by_cases hk : LinOrd.cmp k a.1 = .eq
    · have hka : k = a.1 := LinOrd.eq_of_cmp_eq hk
      subst hka
      rw [findIn_none_of_all_lt (strictAsc_head_lt h₁),
        findIn_none_of_all_lt (strictAsc_head_lt h₂)]
    · have := h k
      rwa [findIn_cons_ne hk, findIn_cons_ne hk] at this

/-! ## The bundled carrier -/

/-- `Base.Map.t`, as its `to_alist`: a strictly ascending association list, with the invariant in
the type. The invariant is a decidable `Prop`, so proof irrelevance makes a `Map` equal to
another exactly when its entries are. -/
structure Map (κ : Type u) (α : Type v) [LinOrd κ] : Type (max u v) where
  /-- `Base.Map.to_alist ~key_order:`Increasing`. -/
  entries : List (κ × α)
  /-- Strictly ascending by key. -/
  wf : strictAsc entries = true

namespace Map

variable {κ : Type u} {α : Type v} {β : Type w} [LinOrd κ]

@[ext] theorem ext {m₁ m₂ : Map κ α} (h : m₁.entries = m₂.entries) : m₁ = m₂ := by
  cases m₁; cases m₂; cases h; rfl

instance [DecidableEq κ] [DecidableEq α] : DecidableEq (Map κ α) := fun m₁ m₂ =>
  if h : m₁.entries = m₂.entries then .isTrue (ext h)
  else .isFalse fun he => h (congrArg Map.entries he)

/-- `Base.Map.empty`. -/
def empty : Map κ α := ⟨[], rfl⟩

/-- `Base.Map.find`. -/
def find (m : Map κ α) (k : κ) : Option α := findIn k m.entries

/-- `Base.Map.set ~key ~data`. -/
def set (m : Map κ α) (k : κ) (v : α) : Map κ α :=
  ⟨insertIn k v m.entries, strictAsc_insertIn k v m.wf⟩

/-- `Base.Map.remove`. -/
def remove (m : Map κ α) (k : κ) : Map κ α :=
  ⟨removeIn k m.entries, strictAsc_removeIn k m.wf⟩

/-- `Base.Map.to_alist ~key_order:`Increasing` (the default). -/
def toAlist (m : Map κ α) : List (κ × α) := m.entries

/-- `Base.Map.keys`, in increasing order. -/
def keys (m : Map κ α) : List κ := m.entries.map (·.1)

/-- `Base.Map.data`, in increasing key order. -/
def data (m : Map κ α) : List α := m.entries.map (·.2)

/-- `Base.Map.length`. -/
def length (m : Map κ α) : Nat := m.entries.length

/-- `Base.Map.mem`. -/
def mem (m : Map κ α) (k : κ) : Bool := (m.find k).isSome

/-- `Base.Map.fold ~init ~f`, documented "in increasing order of key". -/
def fold (m : Map κ α) (init : β) (f : κ → α → β → β) : β :=
  m.entries.foldl (fun acc e => f e.1 e.2 acc) init

/-- `Base.Map.of_alist_reduce ~f:(fun _ later -> later)`: a total constructor whose tie-break is
"the last binding wins". -/
def ofAlist (l : List (κ × α)) : Map κ α :=
  l.foldl (fun m e => m.set e.1 e.2) empty

/-! ### The laws -/

@[simp] theorem find_empty (k : κ) : (empty : Map κ α).find k = none := rfl

@[simp] theorem entries_empty : (empty : Map κ α).entries = [] := rfl

@[simp] theorem find_set_same (m : Map κ α) (k : κ) (v : α) : (m.set k v).find k = some v :=
  findIn_insertIn_same k v m.entries

theorem find_set_other (m : Map κ α) (k k' : κ) (v : α) (h : k' ≠ k) :
    (m.set k v).find k' = m.find k' :=
  findIn_insertIn_other v (fun hc => h (LinOrd.eq_of_cmp_eq hc)) m.entries

@[simp] theorem find_remove_same (m : Map κ α) (k : κ) : (m.remove k).find k = none :=
  findIn_removeIn_same k m.wf

theorem find_remove_other (m : Map κ α) (k k' : κ) (h : k' ≠ k) :
    (m.remove k).find k' = m.find k' :=
  findIn_removeIn_other (fun hc => h (LinOrd.eq_of_cmp_eq hc)) m.entries

/-- **Canonical form.** Two maps that answer `find` alike are equal: the carrier has no room for
an insertion order. -/
theorem ext_find {m₁ m₂ : Map κ α} (h : ∀ k, m₁.find k = m₂.find k) : m₁ = m₂ :=
  ext (entries_ext m₁.wf m₂.wf h)

/-- **Insertion independence.** `set` at two distinct keys commutes. -/
theorem set_comm (m : Map κ α) {k₁ k₂ : κ} (v₁ v₂ : α) (h : k₁ ≠ k₂) :
    (m.set k₁ v₁).set k₂ v₂ = (m.set k₂ v₂).set k₁ v₁ := by
  refine ext_find fun k => ?_
  by_cases h₁ : k = k₁
  · subst h₁
    rw [find_set_other _ _ _ _ h, find_set_same, find_set_same]
  · by_cases h₂ : k = k₂
    · subst h₂
      rw [find_set_same, find_set_other _ _ _ _ (fun hc => h₁ hc), find_set_same]
    · rw [find_set_other _ _ _ _ h₂, find_set_other _ _ _ _ h₁,
        find_set_other _ _ _ _ h₁, find_set_other _ _ _ _ h₂]

/-- The later `set` at one key wins. -/
theorem set_set_same (m : Map κ α) (k : κ) (v₁ v₂ : α) :
    (m.set k v₁).set k v₂ = m.set k v₂ := by
  refine ext_find fun k' => ?_
  by_cases h : k' = k
  · subst h; rw [find_set_same, find_set_same]
  · rw [find_set_other _ _ _ _ h, find_set_other _ _ _ _ h, find_set_other _ _ _ _ h]

/-! ### `keys`, `fold`, `to_alist` -/

theorem keys_sorted (m : Map κ α) : ∀ e ∈ m.entries, ∀ x ∈ m.entries,
    e.1 = x.1 ∨ LinOrd.cmp e.1 x.1 = .lt ∨ LinOrd.cmp x.1 e.1 = .lt := by
  intro e _ x _
  rcases LinOrd.cmp_total e.1 x.1 with h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl (LinOrd.eq_of_cmp_eq h)
  · exact Or.inr (Or.inr (by rw [LinOrd.cmp_swap, h]; rfl))

/-- **The key list is strictly ascending**, which is `Map.keys`' documented order. -/
theorem entries_strictAsc (m : Map κ α) : strictAsc m.entries = true := m.wf

private theorem nodup_of_strictAsc :
    ∀ {l : List (κ × α)}, strictAsc l = true → (l.map (·.1)).Nodup
  | [], _ => List.nodup_nil
  | e :: r, h => by
    refine List.nodup_cons.mpr ⟨?_, nodup_of_strictAsc (strictAsc_of_cons h)⟩
    intro hmem
    obtain ⟨x, hx, hxe⟩ := List.mem_map.mp hmem
    have := strictAsc_head_lt h x hx
    rw [hxe, LinOrd.cmp_self] at this
    cases this

/-- **Every key occurs exactly once.** -/
theorem keys_nodup (m : Map κ α) : m.keys.Nodup := nodup_of_strictAsc m.wf

omit [LinOrd κ] in
private theorem foldl_snoc_eq :
    ∀ (l : List (κ × α)) (acc : List κ),
      l.foldl (fun a e => a ++ [e.1]) acc = acc ++ l.map (·.1)
  | [], acc => by simp
  | e :: r, acc => by
    simp only [List.foldl_cons, List.map_cons]
    rw [foldl_snoc_eq r (acc ++ [e.1])]
    simp

/-- **`fold` visits each key exactly once, in key order.** Accumulating the visited keys
reproduces `keys`, which `keys_nodup` says has no repeat. -/
theorem fold_visits_keys_in_order (m : Map κ α) :
    m.fold ([] : List κ) (fun k _ acc => acc ++ [k]) = m.keys := by
  simp [fold, keys, foldl_snoc_eq m.entries []]

/-- **`fold` performs exactly `length` steps.** -/
theorem fold_length (m : Map κ α) : m.fold 0 (fun _ _ n => n + 1) = m.length := by
  simp only [fold, length]
  suffices h : ∀ (l : List (κ × α)) (n : Nat),
      l.foldl (fun acc (e : κ × α) => (fun _ _ (x : Nat) => x + 1) e.1 e.2 acc) n
        = n + l.length by
    simp [h m.entries 0]
  intro l
  induction l with
  | nil => intro n; simp
  | cons e r ih => intro n; simp [ih]; omega

/-- **`to_alist` is strictly ascending by key.** -/
theorem toAlist_sorted (m : Map κ α) : strictAsc m.toAlist = true := m.wf

/-- `to_alist` carries exactly the bindings `find` answers. -/
theorem find_toAlist (m : Map κ α) (k : κ) : findIn k m.toAlist = m.find k := rfl

/-! ### `of_alist ∘ to_alist = id` -/

private theorem insertIn_snoc {k : κ} {v : α} :
    ∀ {l : List (κ × α)}, (∀ x ∈ l, LinOrd.cmp x.1 k = .lt) → insertIn k v l = l ++ [(k, v)]
  | [], _ => rfl
  | e :: r, h => by
    have he : LinOrd.cmp e.1 k = .lt := h e (List.mem_cons_self ..)
    have hk : LinOrd.cmp k e.1 = .gt := by rw [LinOrd.cmp_swap, he]; rfl
    unfold insertIn
    rw [hk]
    exact congrArg (e :: ·) (insertIn_snoc fun x hx => h x (List.mem_cons_of_mem _ hx))

private theorem strictAsc_append_head :
    ∀ {acc : List (κ × α)} {e : κ × α} {r : List (κ × α)},
      strictAsc (acc ++ e :: r) = true → ∀ x ∈ acc, LinOrd.cmp x.1 e.1 = .lt
  | [], _, _, _, _, hx => by cases hx
  | a :: acc', e, r, h, x, hx => by
    have hcons : strictAsc (a :: (acc' ++ e :: r)) = true := h
    have h' := strictAsc_cons.mp hcons
    cases hx with
    | head => exact strictAsc_head_lt hcons e (by simp)
    | tail _ hx' => exact strictAsc_append_head h'.2 x hx'

private theorem foldl_set_eq :
    ∀ (l : List (κ × α)) (acc : List (κ × α)) (hacc : strictAsc acc = true)
      (h : strictAsc (acc ++ l) = true),
      l.foldl (fun m e => m.set e.1 e.2) (⟨acc, hacc⟩ : Map κ α) = ⟨acc ++ l, h⟩
  | [], acc, hacc, h => by simp
  | e :: r, acc, hacc, h => by
    have hsnoc : insertIn e.1 e.2 acc = acc ++ [e] :=
      insertIn_snoc (strictAsc_append_head h)
    have hacc' : strictAsc (acc ++ [e]) = true := by
      rw [← hsnoc]; exact strictAsc_insertIn e.1 e.2 hacc
    have h' : strictAsc ((acc ++ [e]) ++ r) = true := by
      simp only [List.append_assoc, List.cons_append, List.nil_append]
      exact h
    have step : (⟨acc, hacc⟩ : Map κ α).set e.1 e.2 = ⟨acc ++ [e], hacc'⟩ :=
      ext (by simpa [Map.set] using hsnoc)
    simp only [List.foldl_cons, step]
    rw [foldl_set_eq r (acc ++ [e]) hacc' h']
    exact ext (by simp)

/-- **`of_alist ∘ to_alist = id`.** -/
theorem ofAlist_toAlist (m : Map κ α) : ofAlist m.toAlist = m := by
  have := foldl_set_eq (κ := κ) (α := α) m.entries [] rfl (by simpa using m.wf)
  simp only [ofAlist, toAlist, empty] at *
  rw [this]
  exact ext (by simp)

/-! ### `merge` -/

/-- One step of `merge`: the key's answer, inserted when it is `Some`. -/
private def mergeStep {γ : Type z} (f : κ → Option α → Option β → Option γ)
    (m₁ : Map κ α) (m₂ : Map κ β) (k' : κ) (acc : Map κ γ) : Map κ γ :=
  match f k' (m₁.find k') (m₂.find k') with
  | some v => acc.set k' v
  | none => acc

/-- `Base.Map.merge`, in the `Option`-pair form: `f` sees the key and both sides. `` `Left ``,
`` `Right `` and `` `Both `` are `(some, none)`, `(none, some)` and `(some, some)`; the
`(none, none)` case never arises in `Base` and is required to answer `none` here. -/
def merge {γ : Type z} (f : κ → Option α → Option β → Option γ)
    (m₁ : Map κ α) (m₂ : Map κ β) : Map κ γ :=
  (m₁.keys ++ m₂.keys).foldr (mergeStep f m₁ m₂) empty

/-- The key predicate `merge`'s law is stated against. -/
private def keyIn (k : κ) (ks : List κ) : Bool :=
  ks.any (fun k' => decide (LinOrd.cmp k k' = Ordering.eq))

private theorem findIn_none_of_not_keyIn {k : κ} :
    ∀ {l : List (κ × α)}, keyIn k (l.map (·.1)) = false → findIn k l = none
  | [], _ => rfl
  | e :: r, h => by
    simp only [keyIn, List.map_cons, List.any_cons, Bool.or_eq_false_iff,
      decide_eq_false_iff_not] at h
    rw [findIn_cons_ne h.1]
    exact findIn_none_of_not_keyIn (by simpa [keyIn] using h.2)

/-- A key not among the map's keys is not bound. -/
theorem find_eq_none_of_not_mem_keys (m : Map κ α) (k : κ) (h : keyIn k m.keys = false) :
    m.find k = none :=
  findIn_none_of_not_keyIn h

private theorem find_merge_foldr {γ : Type z} (f : κ → Option α → Option β → Option γ)
    (m₁ : Map κ α) (m₂ : Map κ β) (k : κ) :
    ∀ ks : List κ,
      Map.find (ks.foldr (mergeStep f m₁ m₂) empty) k
        = if keyIn k ks then f k (m₁.find k) (m₂.find k) else none
  | [] => by simp [keyIn]
  | k' :: r => by
    have ih := find_merge_foldr f m₁ m₂ k r
    by_cases hk : LinOrd.cmp k k' = Ordering.eq
    · have hkk : k = k' := LinOrd.eq_of_cmp_eq hk
      subst hkk
      have hany : keyIn k (k :: r) = true := by
        simp [keyIn, LinOrd.cmp_self]
      simp only [List.foldr_cons, mergeStep, hany, if_true]
      cases hf : f k (m₁.find k) (m₂.find k) with
      | some v => simp
      | none =>
        simp only []
        rw [ih]
        split <;> simp [hf]
    · have hne : k ≠ k' := fun hc => hk (by rw [hc]; exact LinOrd.cmp_self k')
      have hany : keyIn k (k' :: r) = keyIn k r := by
        simp [keyIn, hk]
      simp only [List.foldr_cons, mergeStep, hany]
      cases hf : f k' (m₁.find k') (m₂.find k') with
      | some v =>
        simp only []
        rw [find_set_other _ _ _ _ hne, ih]
      | none =>
        simp only []
        exact ih

/-- **`merge` is pointwise.** `f k none none = none` is `Base`'s standing assumption: `merge`
never calls `f` on a key present in neither map. -/
theorem find_merge {γ : Type z} (f : κ → Option α → Option β → Option γ)
    (m₁ : Map κ α) (m₂ : Map κ β) (k : κ) (hf : f k none none = none) :
    (merge f m₁ m₂).find k = f k (m₁.find k) (m₂.find k) := by
  rw [merge, find_merge_foldr f m₁ m₂ k]
  by_cases hin : keyIn k (m₁.keys ++ m₂.keys) = true
  · rw [if_pos hin]
  · have hno : keyIn k (m₁.keys ++ m₂.keys) = false := by
      simpa using hin
    rw [if_neg (by simp [hno])]
    have hsplit : keyIn k m₁.keys = false ∧ keyIn k m₂.keys = false := by
      simpa [keyIn, List.any_append, Bool.or_eq_false_iff] using hno
    have h₁ : keyIn k m₁.keys = false := hsplit.1
    have h₂ : keyIn k m₂.keys = false := hsplit.2
    rw [find_eq_none_of_not_mem_keys m₁ k h₁, find_eq_none_of_not_mem_keys m₂ k h₂, hf]

end Map

end OCaml5.Lib
