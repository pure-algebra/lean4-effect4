import OCaml5.Lib.Order
import OCaml5.Ml.Reflect

/-!
# `OCaml5.Lib.Sexp` — the carrier for `Sexplib.Sexp.t` and for `[@@deriving sexp]`

Status: seat W4 of the 2026-09-04 wave. Plan: `docs/research/2026-09-04-ocaml-packages-plan.md`
§2 (sexps are the daemon's human wire) and §4.2/§4.4. Report:
`docs/research/2026-09-04-seat-w4-library-carriers.md`.

`Sexplib.Sexp.t = Atom of string | List of t list` is transcribed literally. The printer is the
**quoted-atom canonical form**: every atom is printed inside `"…"` with `\` and `"` escaped, and
a list is `(` then its elements, juxtaposed, then `)`. No whitespace is emitted and none is
accepted; the grammar is prefix-determined, which is what makes the round trip an equality
rather than a normalisation.

## Named properties (theorem names are stable; cite these)

* `Sexp.parse_print` — **exactly-once round trip**: `parse (print s) = some s`, and the parser
  consumes exactly `print s` and nothing of what follows it (`parse_print_append`).
* `Sexp.print_inj` — `print` is injective, so a sexp is determined by its text.
* `Sexp.beq_iff` / the `DecidableEq Sexp` instance — hand-written, because the inductive is
  nested (`List Sexp`) and no deriving handler applies.
* `Sexp.cmp` (`instLinOrdSexp`) — a total order on sexps, obtained from `print_inj`; this is the
  order `OCaml5.Lib.Derived` uses to specify a derived `compare`.
* `SexpOf.record_shape` / `SexpOf.variant_shape` — the shapes `[@@deriving sexp]` produces.
* `SexpOf.record_inj` — a record's sexp determines its field values (fields in declaration
  order).
* `SexpOf.variant_inj` — a variant's sexp determines its constructor and arguments, given that
  the description's constructor names are distinct (`SexpOf.ctorNamesNodup`).

## What each definition stands for

| here | OCaml | the law |
| --- | --- | --- |
| `Sexp` | `Sexplib.Sexp.t` | — |
| `Sexp.print` | the canonical (machine) printer, `Sexp.to_string_mach`'s role | `parse_print` |
| `Sexp.parse` | `Sexp.of_string` | `parse_print` |
| `SexpOf.record` | what `ppx_sexp_conv` emits for a record: `List` of `(Atom field, value)` pairs, in **declaration order** | `record_inj` |
| `SexpOf.variant` | what `ppx_sexp_conv` emits for a variant: `Atom C` with no argument, `List (Atom C :: args)` otherwise | `variant_inj` |
| `SexpOf.ofStruct` / `ofInductive` | the same, driven by W3's `OCaml5.Ml.Reflect.TypeDesc` | `record_inj`, `variant_inj` |

## Refusals

* **`Sexp.to_string_hum` and whitespace-tolerant parsing.** The human printer's line breaking and
  the reader's comment/whitespace handling are a normalisation, not a bijection: two texts can
  read to one sexp. Only the canonical form is modelled. Refusal row `W4-SEXP-HUM`.
* **Bare (unquoted) atoms.** `Sexplib` prints an atom without quotes when it needs none; that is
  the same normalisation. The carrier always quotes. Refusal row `W4-SEXP-BARE-ATOM`.
* **`bin_prot`.** The plan §2 lists `bin_prot` as the fast wire. It has no carrier here: its
  format is a byte layout, not a term, and nothing we claim depends on it. Refusal row
  `W4-SEXP-BINPROT`.
* **`sexp_of` for abstract and functional types.** `ppx_sexp_conv` emits `<fun>` / `<opaque>` for
  those, which is not injective. Any carrier the daemon serialises must be first-order. Refusal
  row `W4-SEXP-OPAQUE`.
-/

set_option autoImplicit false

namespace OCaml5.Lib

/-- `Sexplib.Sexp.t`. A nested inductive: `DecidableEq` is written by hand below. -/
inductive Sexp where
  /-- `Sexp.Atom`. -/
  | atom (s : String)
  /-- `Sexp.List`. -/
  | list (xs : List Sexp)
deriving Repr, Inhabited

namespace Sexp

/-! ## Decidable equality, by hand -/

mutual

/-- Structural equality on sexps. -/
def beq : Sexp → Sexp → Bool
  | .atom a, .atom b => a == b
  | .list a, .list b => beqL a b
  | .atom _, .list _ => false
  | .list _, .atom _ => false

/-- Structural equality on sexp lists. -/
def beqL : List Sexp → List Sexp → Bool
  | [], [] => true
  | x :: r, y :: s => beq x y && beqL r s
  | [], _ :: _ => false
  | _ :: _, [] => false

end

mutual

theorem eq_of_beq : ∀ {a b : Sexp}, beq a b = true → a = b
  | .atom _, .atom _, h => by simp [beq] at h; simp [h]
  | .list a, .list b, h => by
    have : beqL a b = true := by simpa [beq] using h
    exact congrArg Sexp.list (eq_of_beqL this)
  | .atom _, .list _, h => by simp [beq] at h
  | .list _, .atom _, h => by simp [beq] at h

theorem eq_of_beqL : ∀ {a b : List Sexp}, beqL a b = true → a = b
  | [], [], _ => rfl
  | x :: r, y :: s, h => by
    have h' : beq x y = true ∧ beqL r s = true := by simpa [beqL] using h
    rw [eq_of_beq h'.1, eq_of_beqL h'.2]
  | [], _ :: _, h => by simp [beqL] at h
  | _ :: _, [], h => by simp [beqL] at h

end

mutual

theorem beq_self : ∀ a : Sexp, beq a a = true
  | .atom _ => by simp [beq]
  | .list a => by simpa [beq] using beqL_self a

theorem beqL_self : ∀ a : List Sexp, beqL a a = true
  | [] => rfl
  | x :: r => by simp [beqL, beq_self x, beqL_self r]

end

/-- **Structural equality is decided by `beq`.** -/
theorem beq_iff {a b : Sexp} : beq a b = true ↔ a = b :=
  ⟨eq_of_beq, fun h => h ▸ beq_self a⟩

instance : DecidableEq Sexp := fun a b =>
  if h : beq a b = true then .isTrue (eq_of_beq h)
  else .isFalse fun he => h (he ▸ beq_self a)

/-! ## Size, for the parser's fuel -/

mutual

/-- Node count. -/
def size : Sexp → Nat
  | .atom _ => 1
  | .list xs => 1 + sizeL xs

/-- Node count of a list, counting the closing paren as one. -/
def sizeL : List Sexp → Nat
  | [] => 1
  | x :: r => size x + sizeL r

end

mutual

theorem size_pos : ∀ s : Sexp, 1 ≤ size s
  | .atom _ => Nat.le_refl 1
  | .list xs => by simp [size]

theorem sizeL_pos : ∀ xs : List Sexp, 1 ≤ sizeL xs
  | [] => Nat.le_refl 1
  | x :: r => by
    have := size_pos x
    have := sizeL_pos r
    simp only [sizeL]
    omega

end

/-! ## The canonical printer -/

/-- `\` and `"` are escaped; nothing else is. -/
def escape : List Char → List Char
  | [] => []
  | c :: r =>
    if c = '"' then '\\' :: '"' :: escape r
    else if c = '\\' then '\\' :: '\\' :: escape r
    else c :: escape r

mutual

/-- The canonical text of a sexp, as characters. -/
def printC : Sexp → List Char
  | .atom s => '"' :: (escape s.toList ++ ['"'])
  | .list xs => '(' :: (printL xs ++ [')'])

/-- The canonical text of a sexp list, juxtaposed. -/
def printL : List Sexp → List Char
  | [] => []
  | x :: r => printC x ++ printL r

end

/-- The canonical text of a sexp. -/
def print (s : Sexp) : String := String.ofList (printC s)

/-! ## The parser -/

/-- Read the body of a quoted atom, up to the closing quote. -/
def readAtom : List Char → Option (List Char × List Char)
  | [] => none
  | c :: r =>
    if c = '"' then some ([], r)
    else if c = '\\' then
      match r with
      | [] => none
      | c' :: r' => (readAtom r').map fun p => (c' :: p.1, p.2)
    else (readAtom r).map fun p => (c :: p.1, p.2)

theorem readAtom_quote (r : List Char) : readAtom ('"' :: r) = some ([], r) := by
  rw [readAtom.eq_def]; simp

theorem readAtom_esc (c : Char) (r : List Char) :
    readAtom ('\\' :: c :: r) = (readAtom r).map (fun p => (c :: p.1, p.2)) := by
  rw [readAtom.eq_def]; simp

theorem readAtom_plain (c : Char) (r : List Char) (h₁ : c ≠ '"') (h₂ : c ≠ '\\') :
    readAtom (c :: r) = (readAtom r).map (fun p => (c :: p.1, p.2)) := by
  rw [readAtom.eq_def]; simp [h₁, h₂]

mutual

/-- Parse one sexp, fuel-bounded. -/
def parseC : Nat → List Char → Option (Sexp × List Char)
  | 0, _ => none
  | _ + 1, [] => none
  | n + 1, c :: r =>
    if c = '"' then (readAtom r).map fun p => (Sexp.atom (String.ofList p.1), p.2)
    else if c = '(' then (parseL n r).map fun p => (Sexp.list p.1, p.2)
    else none

/-- Parse a sexp list up to its closing paren, fuel-bounded. -/
def parseL : Nat → List Char → Option (List Sexp × List Char)
  | 0, _ => none
  | _ + 1, [] => none
  | n + 1, c :: r =>
    if c = ')' then some ([], r)
    else (parseC n (c :: r)).bind fun p =>
      (parseL n p.2).map fun q => (p.1 :: q.1, q.2)

end

theorem parseC_quote (n : Nat) (r : List Char) :
    parseC (n + 1) ('"' :: r)
      = (readAtom r).map (fun p => (Sexp.atom (String.ofList p.1), p.2)) := by
  rw [parseC.eq_def]; simp

theorem parseC_lparen (n : Nat) (r : List Char) :
    parseC (n + 1) ('(' :: r) = (parseL n r).map (fun p => (Sexp.list p.1, p.2)) := by
  rw [parseC.eq_def]; simp

theorem parseL_rparen (n : Nat) (r : List Char) : parseL (n + 1) (')' :: r) = some ([], r) := by
  rw [parseL.eq_def]; simp

theorem parseL_cons (n : Nat) (c : Char) (r : List Char) (h : c ≠ ')') :
    parseL (n + 1) (c :: r)
      = (parseC n (c :: r)).bind fun p => (parseL n p.2).map fun q => (p.1 :: q.1, q.2) := by
  rw [parseL.eq_def]; simp [h]

/-- `Sexp.of_string`: parse a whole string, requiring that nothing is left over. -/
def parse (t : String) : Option Sexp :=
  let cs := t.toList
  match parseC (cs.length + 1) cs with
  | some (s, []) => some s
  | _ => none

/-! ## The round trip -/

theorem readAtom_escape : ∀ (cs rest : List Char),
    readAtom (escape cs ++ '"' :: rest) = some (cs, rest)
  | [], rest => by simpa [escape] using readAtom_quote rest
  | c :: r, rest => by
    have ih := readAtom_escape r rest
    by_cases h₁ : c = '"'
    · subst h₁; simp [escape, readAtom_esc, ih]
    · by_cases h₂ : c = '\\'
      · subst h₂; simp [escape, readAtom_esc, ih]
      · simp [escape, h₁, h₂, readAtom_plain c _ h₁ h₂, ih]

/-- The text of a sexp starts with `"` or `(`; in particular never with `)`. -/
theorem printC_head : ∀ s : Sexp, ∃ c t, printC s = c :: t ∧ c ≠ ')'
  | .atom a => ⟨'"', escape a.toList ++ ['"'], rfl, by decide⟩
  | .list xs => ⟨'(', printL xs ++ [')'], rfl, by decide⟩

private theorem printC_atom_append (a : String) (rest : List Char) :
    printC (Sexp.atom a) ++ rest = '"' :: (escape a.toList ++ '"' :: rest) := by
  simp [printC]

private theorem printC_list_append (xs : List Sexp) (rest : List Char) :
    printC (Sexp.list xs) ++ rest = '(' :: (printL xs ++ ')' :: rest) := by
  simp [printC]

private theorem parse_print_aux : ∀ n : Nat,
    (∀ (s : Sexp) (rest : List Char), size s ≤ n →
      parseC n (printC s ++ rest) = some (s, rest)) ∧
    (∀ (xs : List Sexp) (rest : List Char), sizeL xs ≤ n →
      parseL n (printL xs ++ ')' :: rest) = some (xs, rest))
  | 0 => by
    constructor
    · intro s _ h; exact absurd h (by have := size_pos s; omega)
    · intro xs _ h; exact absurd h (by have := sizeL_pos xs; omega)
  | n + 1 => by
    have ih := parse_print_aux n
    constructor
    · intro s rest h
      cases s with
      | atom a =>
        rw [printC_atom_append, parseC_quote, readAtom_escape]
        simp
      | list xs =>
        have hxs : sizeL xs ≤ n := by
          have hsz : size (Sexp.list xs) = 1 + sizeL xs := rfl
          omega
        rw [printC_list_append, parseC_lparen, ih.2 xs rest hxs]
        simp
    · intro xs rest h
      cases xs with
      | nil =>
        show parseL (n + 1) (')' :: rest) = _
        rw [parseL_rparen]
      | cons x r =>
        obtain ⟨c, t, hct, hcne⟩ := printC_head x
        have hsz : sizeL (x :: r) = size x + sizeL r := rfl
        have hx : size x ≤ n := by have := sizeL_pos r; omega
        have hr : sizeL r ≤ n := by have := size_pos x; omega
        have heq : printL (x :: r) ++ ')' :: rest
            = c :: (t ++ (printL r ++ ')' :: rest)) := by
          show (printC x ++ printL r) ++ ')' :: rest = _
          rw [hct]; simp
        have hback : c :: (t ++ (printL r ++ ')' :: rest))
            = printC x ++ (printL r ++ ')' :: rest) := by
          rw [hct]; simp
        rw [heq, parseL_cons n c _ hcne, hback, ih.1 x _ hx]
        simp only [Option.bind_some]
        rw [ih.2 r rest hr]
        rfl

/-- **The round trip, with a suffix.** The parser consumes exactly the printed sexp. -/
theorem parse_print_append (s : Sexp) (rest : List Char) (n : Nat) (h : size s ≤ n) :
    parseC n (printC s ++ rest) = some (s, rest) :=
  (parse_print_aux n).1 s rest h

mutual

theorem size_le_printC : ∀ s : Sexp, size s ≤ (printC s).length
  | .atom a => by simp [size, printC]
  | .list xs => by
    have := sizeL_le_printL xs
    simp only [size, printC, List.length_cons, List.length_append]
    omega

theorem sizeL_le_printL : ∀ xs : List Sexp, sizeL xs ≤ (printL xs).length + 1
  | [] => by simp [sizeL, printL]
  | x :: r => by
    have h₁ := size_le_printC x
    have h₂ := sizeL_le_printL r
    simp only [sizeL, printL, List.length_append]
    omega

end

/-- **Exactly-once round trip.** -/
theorem parse_print (s : Sexp) : parse (print s) = some s := by
  have h := parse_print_append s [] ((printC s).length + 1)
    (by have := size_le_printC s; omega)
  rw [List.append_nil] at h
  simp only [parse, print, String.toList_ofList, h]

/-- **`print` is injective**, which is what makes the text a name for the sexp. -/
theorem print_inj {s₁ s₂ : Sexp} (h : printC s₁ = printC s₂) : s₁ = s₂ := by
  have h₁ : parseC (size s₁ + size s₂) (printC s₁ ++ []) = some (s₁, []) :=
    parse_print_append s₁ [] _ (by omega)
  have h₂ : parseC (size s₁ + size s₂) (printC s₂ ++ []) = some (s₂, []) :=
    parse_print_append s₂ [] _ (by omega)
  rw [h, h₂] at h₁
  exact (congrArg Prod.fst (Option.some.inj h₁)).symm

/-- **A total order on sexps**: the lexicographic order of the canonical text. This is *a* total
order consistent with structural equality, which is all `OCaml5.Lib.Derived` relies on; it is not
claimed to be `ppx_compare`'s order (refusal `W4-DERIVED-COMPARE-ORDER`). -/
instance : LinOrd Sexp := LinOrd.onKey printC (fun {_ _} h => print_inj h)

end Sexp

/-! ## `[@@deriving sexp]` as a description

`ppx_sexp_conv` emits, for a record `{a; b}`, `List [List [Atom "a"; va]; List [Atom "b"; vb]]`
in **declaration order**, and for a variant `C of x * y`, `Atom "C"` when the constructor takes
no argument and `List [Atom "C"; vx; vy]` otherwise. Both shapes are functions of W3's
`OCaml5.Ml.Reflect.TypeDesc`, so a generated carrier's wire is fixed by its description. -/

namespace SexpOf

open OCaml5.Ml

/-- The record shape: `(field value)` pairs, in declaration order. -/
def record (fields : List (String × Sexp)) : Sexp :=
  .list (fields.map fun f => .list [.atom f.1, f.2])

/-- The variant shape. -/
def variant (ctor : String) (args : List Sexp) : Sexp :=
  match args with
  | [] => .atom ctor
  | _ => .list (.atom ctor :: args)

/-- The rendered (OCaml) field names of a structure description, in declaration order. This is
what `ppx_sexp_conv` keys the record on. -/
def structFields (d : StructDesc) : List String :=
  (d.fields.filter fun f => f.kind.rendered).map FieldDesc.ocaml

/-- The OCaml constructor names of an inductive description, in declaration order. -/
def ctorNames (d : InductiveDesc) : List String :=
  d.ctors.map (CtorDesc.ocaml d.ctorPrefix)

/-- The sexp of a record value, given its field values positionally. -/
def ofStruct (d : StructDesc) (values : List Sexp) : Sexp :=
  record (List.zip (structFields d) values)

/-- The sexp of a variant value, given the constructor's index and its argument sexps. -/
def ofInductive (d : InductiveDesc) (index : Nat) (args : List Sexp) : Option Sexp :=
  ((ctorNames d)[index]?).map fun c => variant c args

/-! ### The shapes, and their injectivity -/

theorem record_shape (fields : List (String × Sexp)) :
    record fields = .list (fields.map fun f => .list [.atom f.1, f.2]) := rfl

theorem variant_shape_nullary (c : String) : variant c [] = .atom c := rfl

theorem variant_shape_args (c : String) (a : Sexp) (args : List Sexp) :
    variant c (a :: args) = .list (.atom c :: a :: args) := rfl

private theorem zip_inj : ∀ (ks : List String) (v₁ v₂ : List Sexp),
    v₁.length = ks.length → v₂.length = ks.length →
    List.zip ks v₁ = List.zip ks v₂ → v₁ = v₂
  | [], [], [], _, _, _ => rfl
  | _ :: _, [], _, h, _, _ => by simp at h
  | _ :: _, _ :: _, [], _, h, _ => by simp at h
  | k :: ks, a :: v₁, b :: v₂, h₁, h₂, h => by
    simp only [List.zip_cons_cons, List.cons.injEq, Prod.mk.injEq] at h
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h₁ h₂
    rw [h.1.2, zip_inj ks v₁ v₂ h₁ h₂ h.2]

/-- **A record's sexp determines its field values**, given the description's arity. -/
theorem record_inj (d : StructDesc) (v₁ v₂ : List Sexp)
    (h₁ : v₁.length = (structFields d).length) (h₂ : v₂.length = (structFields d).length)
    (h : ofStruct d v₁ = ofStruct d v₂) : v₁ = v₂ := by
  simp only [ofStruct, record, Sexp.list.injEq] at h
  refine zip_inj (structFields d) v₁ v₂ h₁ h₂ ?_
  have hmap : ∀ (l₁ l₂ : List (String × Sexp)),
      (l₁.map fun f => Sexp.list [Sexp.atom f.1, f.2])
        = (l₂.map fun f => Sexp.list [Sexp.atom f.1, f.2]) → l₁ = l₂ := by
    intro l₁
    induction l₁ with
    | nil => intro l₂ hl; cases l₂ with
      | nil => rfl
      | cons _ _ => simp at hl
    | cons e r ih =>
      intro l₂ hl
      cases l₂ with
      | nil => simp at hl
      | cons e' r' =>
        simp only [List.map_cons, List.cons.injEq, Sexp.list.injEq, List.cons.injEq,
          Sexp.atom.injEq] at hl
        obtain ⟨⟨he₁, he₂, _⟩, hr⟩ := hl
        rw [ih r' hr, Prod.ext he₁ he₂]
  exact hmap _ _ h

private theorem nodup_index_unique {α : Type} :
    ∀ {l : List α}, l.Nodup → ∀ {i j : Nat} {a : α}, l[i]? = some a → l[j]? = some a → i = j
  | [], _, _, _, _, h₁, _ => by simp at h₁
  | x :: r, hnd, i, j, a, h₁, h₂ => by
    have hnd' := List.nodup_cons.mp hnd
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j' =>
        exfalso
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h₁
        simp only [List.getElem?_cons_succ] at h₂
        exact hnd'.1 (h₁ ▸ List.mem_of_getElem? h₂)
    | succ i' =>
      cases j with
      | zero =>
        exfalso
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h₂
        simp only [List.getElem?_cons_succ] at h₁
        exact hnd'.1 (h₂ ▸ List.mem_of_getElem? h₁)
      | succ j' =>
        simp only [List.getElem?_cons_succ] at h₁ h₂
        exact congrArg (· + 1) (nodup_index_unique hnd'.2 h₁ h₂)

/-- The constructor names of a description are distinct. Not automatic: it is a fact about the
description, and `OCaml5.Ml.Check` is where a generator is made to guarantee it. -/
def ctorNamesNodup (d : InductiveDesc) : Prop := (ctorNames d).Nodup

/-- **A variant's sexp determines its constructor and arguments**, given distinct constructor
names. -/
theorem variant_inj (d : InductiveDesc) (hnd : ctorNamesNodup d)
    (i₁ i₂ : Nat) (a₁ a₂ : List Sexp) (s : Sexp)
    (h₁ : ofInductive d i₁ a₁ = some s) (h₂ : ofInductive d i₂ a₂ = some s) :
    i₁ = i₂ ∧ a₁ = a₂ := by
  simp only [ofInductive, Option.map_eq_some_iff] at h₁ h₂
  obtain ⟨c₁, hc₁, hs₁⟩ := h₁
  obtain ⟨c₂, hc₂, hs₂⟩ := h₂
  have hname : c₁ = c₂ ∧ a₁ = a₂ := by
    subst hs₁
    cases a₁ with
    | nil =>
      cases a₂ with
      | nil => exact ⟨(by simpa [variant] using hs₂ : c₂ = c₁).symm, rfl⟩
      | cons b bs => simp [variant] at hs₂
    | cons b bs =>
      cases a₂ with
      | nil => simp [variant] at hs₂
      | cons b' bs' =>
        simp only [variant, Sexp.list.injEq, List.cons.injEq, Sexp.atom.injEq] at hs₂
        exact ⟨hs₂.1.symm, by rw [hs₂.2.1, hs₂.2.2]⟩
  refine ⟨?_, hname.2⟩
  exact nodup_index_unique hnd hc₁ (hname.1 ▸ hc₂)

end SexpOf

end OCaml5.Lib
