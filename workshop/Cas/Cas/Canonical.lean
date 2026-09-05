import Cas.Shape

/-!
# Cas.Canonical

Owner: the trait a stored carrier implements, and everything derived from it once.

A carrier is canonical when it is an isomorphic image of the value tree: `toVal` writes it as a
`Val` of a stated `shape`, `ofVal` reads it back, and the three laws say the image is exact
(`ofVal_toVal`), the reading accepts nothing outside the image (`ofVal_exact`), and every image
fits the shape (`fits`). That is the facts note's Q2 as ratified: the class keeps the name
`Canonical`, `LawfulCanonical` retires because the laws are fields, and nothing lands unlawful.

Everything else is derived here once, for every instance: the bytes (`encode = Val.encode ∘
toVal`), the exact decoder (`decode`), its two laws (`decode_encode` under well-formedness,
`decode_exact`), injectivity, the payload digest (`digest = sha256 ∘ encode`, the address of a
foreign or pinned payload; the node address is lane S2's), and the direction that needs no law
(`ne_of_encode_ne`). The instances below are the primitives of `src/Effect4/Store/Canonical.lean:
88-112` with their bytes unchanged (`Test/Store/StoreContract.lean:39-47`), plus the four the
facts note found missing: `Int` as two constructors over `nat`, `UInt8` and `UInt64` as `nat`
under a named scalar shape (so their spec renders `number` with an identifier), and `Digest`
as `bytes` with the length checked in `ofVal`. `Bytes` is declared after `List α` so that
`List UInt8` still frames as `bytes`, the way it did before `UInt8` had an instance.
-/

set_option autoImplicit false

namespace Effect4.Store

/-- The canonical trait: an exact image in the value tree, with its shape. -/
class Canonical (α : Type) where
  /-- The shape every image fits; the spec and the printer derive from it. -/
  shape : ShapeDoc
  /-- The value tree of a carrier. -/
  toVal : α → Val
  /-- The carrier of a value tree, when it is one. -/
  ofVal : Val → Option α
  /-- Every image reads back. -/
  ofVal_toVal : ∀ a, ofVal (toVal a) = some a
  /-- Nothing outside the image reads. -/
  ofVal_exact : ∀ {v a}, ofVal v = some a → v = toVal a
  /-- Every image fits the shape. -/
  fits : ∀ a, shape.accepts (toVal a) = true

export Canonical (shape toVal ofVal ofVal_toVal ofVal_exact fits)

namespace Canonical

variable {α : Type} [Canonical α]

/-- Exactness makes the image injective. -/
theorem toVal_injective {a b : α} (h : toVal a = toVal b) : a = b := by
  have h1 := ofVal_toVal (α := α) a
  rw [h, ofVal_toVal] at h1
  exact (Option.some.inj h1).symm

/-- The canonical bytes of a carrier: the bytes of its value tree. -/
def encode (a : α) : Bytes := Val.encode (toVal a)

/-- The exact decoder: the whole byte string is one value tree, and that tree is a carrier. -/
def decode (b : Bytes) : Option α := (Val.decode b).bind ofVal

/-- Forward correctness, for a carrier whose value tree is well-formed (every frame's payload
shorter than `2^64`). -/
theorem decode_encode (a : α) (h : (toVal a).WF) : decode (encode a) = some a := by
  unfold decode encode
  rw [Val.decode_encode _ h, Option.bind_some, ofVal_toVal]

/-- Image exactness: whatever decodes was the carrier's bytes, and its tree is well-formed. -/
theorem decode_exact {b : Bytes} {a : α} (h : decode b = some a) :
    b = encode a ∧ (toVal a).WF := by
  unfold decode at h
  obtain ⟨v, hv, ha⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hb, hwf⟩ := Val.decode_exact hv
  have hva := ofVal_exact ha
  subst hva
  exact ⟨hb, hwf⟩

/-- One byte string per well-formed carrier. -/
theorem encode_injective {a b : α} (ha : (toVal a).WF) (hb : (toVal b).WF)
    (h : encode a = encode b) : a = b :=
  toVal_injective (Val.encode_injective ha hb h)

/-- Two carriers whose bytes differ are different: the direction that needs no law. -/
theorem ne_of_encode_ne {a b : α} (h : encode a ≠ encode b) : a ≠ b :=
  fun e => h (congrArg encode e)

/-- The payload digest: SHA-256 of the canonical bytes. The address of a foreign or pinned
payload; a node's address adds the version, kind and spec (lane S2). -/
def digest (a : α) : Digest := sha256 (encode a)

/-- Equal carriers have equal digests; the converse is `encode_injective` plus the absence of
a collision, and is never assumed. -/
theorem digest_congr {a b : α} (h : a = b) : digest a = digest b := congrArg digest h

/-- The spec of a carrier's shape. -/
def document (α : Type) [Canonical α] : Effect4.Document := (shape α).document

/-- The JSON of a carrier, read off its shape. -/
def print (a : α) : Effect4.Json := (shape α).print (toVal a)

end Canonical

/-! ## Helpers the instances share -/

/-- A shape that is not `named` accepts exactly what `acceptsAt` says. -/
theorem accepts_mk_of_not_named (root : Shape) (defs : List (String × Shape)) (v : Val)
    (h : ∀ n, root ≠ .named n) :
    (ShapeDoc.mk root defs).accepts v = acceptsAt defs v root :=
  acceptsIn_of_not_named defs root v h

/-- A list fits an item shape when every element does. -/
theorem acceptsList_of_forall (defs : List (String × Shape)) (item : Shape) :
    ∀ vs : List Val, (∀ v ∈ vs, acceptsIn defs item v = true) → acceptsList defs item vs = true
  | [], _ => rfl
  | v :: vs, h => by
    simp only [acceptsList, Bool.and_eq_true]
    exact ⟨h v (by simp), acceptsList_of_forall defs item vs fun w hw => h w (by simp [hw])⟩

/-! The shape lemmas a generated `fits` proof applies, one per rendering rule: a struct is
constructor 0 with fitting fields, a case of a sum is its index with fitting fields, a field
list is checked head by head, a `named` shape with one binding is that binding, and a fit in a
table survives in any table that contains it. -/

theorem acceptsFields_nil (defs : List (String × Shape)) : acceptsFields defs [] [] = true := rfl

theorem acceptsFields_cons (defs : List (String × Shape)) (n : String) (s : Shape)
    (fields : List (String × Shape)) (a : Val) (args : List Val)
    (h1 : acceptsIn defs s a = true) (h2 : acceptsFields defs fields args = true) :
    acceptsFields defs ((n, s) :: fields) (a :: args) = true := by
  simp only [acceptsFields, Bool.and_eq_true]
  exact ⟨h1, h2⟩

theorem acceptsAt_struct (defs : List (String × Shape)) (name : String)
    (fields : List (String × Shape)) (args : List Val)
    (h : acceptsFields defs fields args = true) :
    acceptsAt defs (.ctor 0 args) (.struct name fields) = true := by
  simp [acceptsAt, h]

theorem accepts_struct (defs : List (String × Shape)) (name : String)
    (fields : List (String × Shape)) (args : List Val)
    (h : acceptsFields defs fields args = true) :
    acceptsIn defs (.struct name fields) (.ctor 0 args) = true := by
  rw [acceptsIn_of_not_named defs (.struct name fields) (.ctor 0 args) (fun _ h => nomatch h)]
  exact acceptsAt_struct defs name fields args h

theorem acceptsAt_sum (defs : List (String × Shape)) (name : String)
    (cases : List (String × List (String × Shape))) (i : Nat) (caseName : String)
    (fields : List (String × Shape)) (args : List Val)
    (hi : cases[i]? = some (caseName, fields)) (h : acceptsFields defs fields args = true) :
    acceptsAt defs (.ctor i args) (.sum name cases) = true := by
  simp only [acceptsAt, hi]
  exact h

theorem accepts_sum (defs : List (String × Shape)) (name : String)
    (cases : List (String × List (String × Shape))) (i : Nat) (caseName : String)
    (fields : List (String × Shape)) (args : List Val)
    (hi : cases[i]? = some (caseName, fields)) (h : acceptsFields defs fields args = true) :
    acceptsIn defs (.sum name cases) (.ctor i args) = true := by
  rw [acceptsIn_of_not_named defs (.sum name cases) (.ctor i args) (fun _ h => nomatch h)]
  exact acceptsAt_sum defs name cases i caseName fields args hi h

theorem acceptsIn_named (defs : List (String × Shape)) (n : String) (s : Shape) (v : Val)
    (h : lookupAll n defs = [s]) : acceptsIn defs (.named n) v = acceptsAt defs v s := by
  unfold acceptsIn
  show (lookupAll n defs).any (acceptsAt defs v) = acceptsAt defs v s
  rw [h]
  simp

theorem accepts_option_none (defs : List (String × Shape)) (item : Shape) :
    acceptsIn defs (.option item) .none = true := by
  rw [acceptsIn_of_not_named defs (.option item) .none (fun _ h => nomatch h)]
  rfl

theorem accepts_option_some (defs : List (String × Shape)) (item : Shape) (a : Val)
    (h : acceptsIn defs item a = true) : acceptsIn defs (.option item) (.some a) = true := by
  rw [acceptsIn_of_not_named defs (.option item) (.some a) (fun _ h => nomatch h)]
  exact h

theorem accepts_list (defs : List (String × Shape)) (item : Shape) (vs : List Val)
    (h : ∀ v ∈ vs, acceptsIn defs item v = true) : acceptsIn defs (.list item) (.list vs) = true := by
  rw [acceptsIn_of_not_named defs (.list item) (.list vs) (fun _ h => nomatch h)]
  exact acceptsList_of_forall defs item vs h

theorem accepts_pair (defs : List (String × Shape)) (f g : Shape) (a b : Val)
    (ha : acceptsIn defs f a = true) (hb : acceptsIn defs g b = true) :
    acceptsIn defs (.pair f g) (.pair a b) = true := by
  rw [acceptsIn_of_not_named defs (.pair f g) (.pair a b) (fun _ h => nomatch h)]
  show ((candidates defs f).any (acceptsAt defs a) && (candidates defs g).any (acceptsAt defs b)) = true
  rw [Bool.and_eq_true]
  exact ⟨ha, hb⟩

theorem mem_lookupAll (n : String) (s' : Shape) :
    ∀ d : List (String × Shape), s' ∈ lookupAll n d ↔ (n, s') ∈ d
  | [] => by simp [lookupAll]
  | (m, t) :: rest => by
    simp only [lookupAll, List.mem_cons, Prod.mk.injEq]
    split
    · next hm =>
      subst hm
      simp only [List.mem_cons, mem_lookupAll m s' rest, true_and]
    · next hm =>
      rw [mem_lookupAll n s' rest]
      constructor
      · intro h
        exact Or.inr h
      · intro h
        rcases h with ⟨hn, _⟩ | h
        · exact absurd hn.symm hm
        · exact h

theorem mem_candidates_of_subset {d1 d2 : List (String × Shape)} (h : ∀ p ∈ d1, p ∈ d2)
    {s s' : Shape} (hm : s' ∈ candidates d1 s) : s' ∈ candidates d2 s := by
  cases s
  case named n =>
    simp only [candidates] at hm ⊢
    exact (mem_lookupAll n s' d2).mpr (h _ ((mem_lookupAll n s' d1).mp hm))
  all_goals exact hm

/-- A fit in a table is a fit in any table containing it: how a generated `fits` lifts a field
type's law into the enclosing document's table. -/
theorem acceptsIn_mono_of_subset {d1 d2 : List (String × Shape)} (h : ∀ p ∈ d1, p ∈ d2)
    (s : Shape) (v : Val) (hv : acceptsIn d1 s v = true) : acceptsIn d2 s v = true :=
  acceptsIn_mono (fun _ _ hm => mem_candidates_of_subset h hm) s v hv

/-- Membership in an appended table, left half: the step a generated table-subset proof takes. -/
theorem mem_append_of_left {α : Type} {a : α} {l₁ l₂ : List α} (h : a ∈ l₁) : a ∈ l₁ ++ l₂ :=
  List.mem_append.mpr (Or.inl h)

/-- Membership in an appended table, right half. -/
theorem mem_append_of_right {α : Type} {a : α} {l₁ l₂ : List α} (h : a ∈ l₂) : a ∈ l₁ ++ l₂ :=
  List.mem_append.mpr (Or.inr h)

/-- A value fits a `named` shape when it fits one of the name's bindings: the form a generated
`fits` uses for a recursive or mutual type, since the binding's membership in the table is a
`simp` fact and never a string comparison. -/
theorem accepts_named_of_mem (defs : List (String × Shape)) (n : String) (s : Shape) (v : Val)
    (h : (n, s) ∈ defs) (hv : acceptsAt defs v s = true) : acceptsIn defs (.named n) v = true := by
  unfold acceptsIn
  exact List.any_eq_true.mpr ⟨s, (mem_lookupAll n s defs).mpr h, hv⟩

/-! The re-encode guard: exactness by construction from any left inverse. The Wire's `readString`
bought its string frame's exactness this way (`Wire.lean:254-262`), and `Surface/Annotate.lean`'s
`markKey` its key's. A carrier whose structural exactness proof is disproportionate (the `Eff`
family, fifty constructors) reads through `guarded toVal raw`: `raw` is the structural reader,
the guard compares the re-encoding, `guarded_toVal` needs only `raw (toVal a) = some a`, and
`guarded_exact` is free. The price is one re-encoding per decode. -/

/-- A reader made exact by re-encoding what it read. -/
def guarded {α : Type} (toVal : α → Val) (raw : Val → Option α) (v : Val) : Option α :=
  match raw v with
  | some a => if toVal a = v then some a else none
  | none => none

theorem guarded_toVal {α : Type} (toVal : α → Val) (raw : Val → Option α) (a : α)
    (hraw : raw (toVal a) = some a) : guarded toVal raw (toVal a) = some a := by
  unfold guarded
  rw [hraw]
  show (if toVal a = toVal a then some a else none) = some a
  rw [if_pos rfl]

theorem guarded_exact {α : Type} {toVal : α → Val} {raw : Val → Option α} {v : Val} {a : α}
    (h : guarded toVal raw v = some a) : v = toVal a := by
  unfold guarded at h
  split at h
  · next b hb =>
    split at h
    · next heq =>
      injection h with h
      subst h
      exact heq.symm
    · exact nomatch h
  · exact nomatch h

/-! ## The primitives -/

instance instCanonicalUnit : Canonical Unit where
  shape := ⟨.unit, []⟩
  toVal _ := .unit
  ofVal
    | .unit => some ()
    | _ => none
  ofVal_toVal _ := rfl
  ofVal_exact := by
    intro v a h
    cases v
    case unit => rfl
    all_goals exact nomatch h
  fits _ := rfl

instance instCanonicalBool : Canonical Bool where
  shape := ⟨.bool, []⟩
  toVal b := .bool b
  ofVal
    | .bool b => some b
    | _ => none
  ofVal_toVal _ := rfl
  ofVal_exact := by
    intro v a h
    cases v
    case bool b =>
      injection h with h
      subst h
      rfl
    all_goals exact nomatch h
  fits _ := rfl

instance instCanonicalNat : Canonical Nat where
  shape := ⟨.nat, []⟩
  toVal n := .nat n
  ofVal
    | .nat n => some n
    | _ => none
  ofVal_toVal _ := rfl
  ofVal_exact := by
    intro v a h
    cases v
    case nat n =>
      injection h with h
      subst h
      rfl
    all_goals exact nomatch h
  fits _ := rfl

instance instCanonicalString : Canonical String where
  shape := ⟨.string, []⟩
  toVal s := .str s
  ofVal
    | .str s => some s
    | _ => none
  ofVal_toVal _ := rfl
  ofVal_exact := by
    intro v a h
    cases v
    case str s =>
      injection h with h
      subst h
      rfl
    all_goals exact nomatch h
  fits _ := rfl

/-! ## `Int`: two constructors over `nat` -/

namespace IntCanonical

/-- `Int.ofNat n` is constructor 0, `Int.negSucc n` constructor 1, as the generator would
write a two-case sum. -/
def toVal : Int → Val
  | .ofNat n => .ctor 0 [.nat n]
  | .negSucc n => .ctor 1 [.nat n]

def ofVal : Val → Option Int
  | .ctor 0 [.nat n] => some (.ofNat n)
  | .ctor 1 [.nat n] => some (.negSucc n)
  | _ => none

def shapeDoc : ShapeDoc :=
  ⟨.sum "Int" [("ofNat", [("n", .nat)]), ("negSucc", [("n", .nat)])], []⟩

theorem ofVal_toVal (a : Int) : ofVal (toVal a) = some a := by
  cases a <;> rfl

theorem ofVal_exact {v : Val} {a : Int} (h : ofVal v = some a) : v = toVal a := by
  unfold ofVal at h
  split at h
  all_goals first
    | (injection h with h; subst h; rfl)
    | exact nomatch h

theorem fits (a : Int) : shapeDoc.accepts (toVal a) = true := by
  cases a <;> rfl

end IntCanonical

instance instCanonicalInt : Canonical Int where
  shape := IntCanonical.shapeDoc
  toVal := IntCanonical.toVal
  ofVal := IntCanonical.ofVal
  ofVal_toVal := IntCanonical.ofVal_toVal
  ofVal_exact := IntCanonical.ofVal_exact
  fits := IntCanonical.fits

/-! ## Fixed-width scalars: `nat` under a named shape -/

instance instCanonicalUInt8 : Canonical UInt8 where
  shape := ⟨.named "UInt8", [("UInt8", .nat)]⟩
  toVal x := .nat x.toNat
  ofVal
    | .nat n => if n < 256 then some (UInt8.ofNat n) else none
    | _ => none
  ofVal_toVal x := by
    show (if x.toNat < 256 then some (UInt8.ofNat x.toNat) else none) = some x
    rw [if_pos (UInt8.toNat_lt x), UInt8.ofNat_toNat]
  ofVal_exact := by
    intro v a h
    cases v
    case nat n =>
      change (if n < 256 then some (UInt8.ofNat n) else none) = some a at h
      split at h
      · next hn =>
        injection h with h
        subst h
        show Val.nat n = Val.nat (UInt8.ofNat n).toNat
        rw [UInt8.toNat_ofNat_of_lt' hn]
      · exact nomatch h
    all_goals exact nomatch h
  fits _ := rfl

instance instCanonicalUInt64 : Canonical UInt64 where
  shape := ⟨.named "UInt64", [("UInt64", .nat)]⟩
  toVal x := .nat x.toNat
  ofVal
    | .nat n => if n < 2 ^ 64 then some (UInt64.ofNat n) else none
    | _ => none
  ofVal_toVal x := by
    show (if x.toNat < 2 ^ 64 then some (UInt64.ofNat x.toNat) else none) = some x
    rw [if_pos (UInt64.toNat_lt x), UInt64.ofNat_toNat]
  ofVal_exact := by
    intro v a h
    cases v
    case nat n =>
      change (if n < 2 ^ 64 then some (UInt64.ofNat n) else none) = some a at h
      split at h
      · next hn =>
        injection h with h
        subst h
        show Val.nat n = Val.nat (UInt64.ofNat n).toNat
        rw [UInt64.toNat_ofNat_of_lt' hn]
      · exact nomatch h
    all_goals exact nomatch h
  fits _ := rfl

/-! ## `Digest`: `bytes`, thirty-two of them -/

instance instCanonicalDigest : Canonical Digest where
  shape := ⟨.digest, []⟩
  toVal d := .bytes d.bytes
  ofVal
    | .bytes bs => if h : bs.length = 32 then some ⟨bs, h⟩ else none
    | _ => none
  ofVal_toVal d := by
    cases d with
    | mk bs hl =>
      show (if h : bs.length = 32 then some (Digest.mk bs h) else none) = some (Digest.mk bs hl)
      rw [dif_pos hl]
  ofVal_exact := by
    intro v a h
    cases v
    case bytes bs =>
      change (if h : bs.length = 32 then some (Digest.mk bs h) else none) = some a at h
      split at h
      · next hl =>
        injection h with h
        subst h
        rfl
      · exact nomatch h
    all_goals exact nomatch h
  fits d := by
    show acceptsIn [] .digest (.bytes d.bytes) = true
    simp [acceptsIn, candidates, acceptsAt, d.length_eq]

/-! ## The containers -/

section Containers

variable {α : Type} [Canonical α]

theorem mapM_ofVal_map_toVal (xs : List α) : (xs.map toVal).mapM (ofVal (α := α)) = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.mapM_cons, ofVal_toVal, ih]

theorem mapM_ofVal_exact : ∀ (vs : List Val) (xs : List α),
    vs.mapM (ofVal (α := α)) = some xs → vs = xs.map toVal
  | [], xs, h => by
    simp only [List.mapM_nil] at h
    injection h with h
    subst h
    rfl
  | v :: vs, xs, h => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨a, ha, as, has, hx⟩ := h
    subst hx
    rw [List.map_cons, ← ofVal_exact ha, ← mapM_ofVal_exact vs as has]

instance instCanonicalList : Canonical (List α) where
  shape := ⟨.list (shape α).root, (shape α).defs⟩
  toVal xs := .list (xs.map toVal)
  ofVal
    | .list vs => vs.mapM ofVal
    | _ => none
  ofVal_toVal xs := mapM_ofVal_map_toVal xs
  ofVal_exact := by
    intro v a h
    cases v
    case list vs =>
      change vs.mapM ofVal = some a at h
      show Val.list vs = Val.list (a.map toVal)
      rw [mapM_ofVal_exact vs a h]
    all_goals exact nomatch h
  fits xs := by
    show acceptsIn (shape α).defs (.list (shape α).root) (.list (xs.map toVal)) = true
    rw [acceptsIn_of_not_named (shape α).defs (.list (shape α).root) (.list (xs.map toVal))
      (fun _ h => nomatch h)]
    show acceptsList (shape α).defs (shape α).root (xs.map toVal) = true
    apply acceptsList_of_forall
    intro v hv
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hv
    exact fits x

instance instCanonicalOption : Canonical (Option α) where
  shape := ⟨.option (shape α).root, (shape α).defs⟩
  toVal
    | none => .none
    | some a => .some (toVal a)
  ofVal
    | .none => some none
    | .some v => (ofVal v).map some
    | _ => none
  ofVal_toVal
    | none => rfl
    | some a => by
      show (ofVal (toVal a)).map some = some (some a)
      rw [ofVal_toVal]
      rfl
  ofVal_exact := by
    intro v a h
    cases v
    case none =>
      injection h with h
      subst h
      rfl
    case some w =>
      change (ofVal w).map some = some a at h
      obtain ⟨b, hb, hba⟩ := Option.map_eq_some_iff.mp h
      subst hba
      show Val.some w = Val.some (toVal b)
      rw [ofVal_exact hb]
    all_goals exact nomatch h
  fits
    | none => by
      show acceptsIn (shape α).defs (.option (shape α).root) .none = true
      rw [acceptsIn_of_not_named (shape α).defs (.option (shape α).root) .none
        (fun _ h => nomatch h)]
      rfl
    | some a => by
      show acceptsIn (shape α).defs (.option (shape α).root) (.some (toVal a)) = true
      rw [acceptsIn_of_not_named (shape α).defs (.option (shape α).root) (.some (toVal a))
        (fun _ h => nomatch h)]
      exact fits a

end Containers

section Pairs

variable {α β : Type} [Canonical α] [Canonical β]

instance instCanonicalProd : Canonical (α × β) where
  shape := ⟨.pair (shape α).root (shape β).root, (shape α).defs ++ (shape β).defs⟩
  toVal p := .pair (toVal p.1) (toVal p.2)
  ofVal
    | .pair a b =>
      match ofVal (α := α) a, ofVal (α := β) b with
      | some x, some y => some (x, y)
      | _, _ => none
    | _ => none
  ofVal_toVal p := by
    obtain ⟨x, y⟩ := p
    show (match ofVal (α := α) (toVal x), ofVal (α := β) (toVal y) with
      | some x, some y => some (x, y)
      | _, _ => none) = some (x, y)
    rw [ofVal_toVal, ofVal_toVal]
  ofVal_exact := by
    intro v p h
    cases v
    case pair a b =>
      change (match ofVal (α := α) a, ofVal (α := β) b with
        | some x, some y => some (x, y)
        | _, _ => none) = some p at h
      split at h
      · next x y hx hy =>
        injection h with h
        subst h
        show Val.pair a b = Val.pair (toVal x) (toVal y)
        rw [ofVal_exact hx, ofVal_exact hy]
      · exact nomatch h
    all_goals exact nomatch h
  fits p := by
    obtain ⟨x, y⟩ := p
    show acceptsIn ((shape α).defs ++ (shape β).defs) (.pair (shape α).root (shape β).root)
      (.pair (toVal x) (toVal y)) = true
    rw [acceptsIn_of_not_named ((shape α).defs ++ (shape β).defs)
      (.pair (shape α).root (shape β).root) (.pair (toVal x) (toVal y)) (fun _ h => nomatch h)]
    show ((candidates ((shape α).defs ++ (shape β).defs) (shape α).root).any
        (acceptsAt ((shape α).defs ++ (shape β).defs) (toVal x)) &&
      (candidates ((shape α).defs ++ (shape β).defs) (shape β).root).any
        (acceptsAt ((shape α).defs ++ (shape β).defs) (toVal y))) = true
    rw [Bool.and_eq_true]
    exact ⟨acceptsIn_append_right _ _ _ _ (fits x), acceptsIn_append_left _ _ _ _ (fits y)⟩

end Pairs

/-! ## `Bytes`, last so that `List UInt8` frames as `bytes` -/

instance instCanonicalBytes : Canonical Bytes where
  shape := ⟨.bytes, []⟩
  toVal bs := .bytes bs
  ofVal
    | .bytes bs => some bs
    | _ => none
  ofVal_toVal _ := rfl
  ofVal_exact := by
    intro v a h
    cases v
    case bytes bs =>
      injection h with h
      subst h
      rfl
    all_goals exact nomatch h
  fits _ := rfl

/-! ## Byte identity, guarded: `Test/Store/StoreContract.lean:39-47` on the trait -/

open Canonical in
#guard encode () = [9, 0, 0, 0, 0, 0, 0, 0, 0]
open Canonical in
#guard encode true = [1, 0, 0, 0, 0, 0, 0, 0, 1, 1]
open Canonical in
#guard encode (0 : Nat) = [2, 0, 0, 0, 0, 0, 0, 0, 0]
open Canonical in
#guard encode (256 : Nat) = [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0]
open Canonical in
#guard encode "A" = [3, 0, 0, 0, 0, 0, 0, 0, 1, 65]
open Canonical in
#guard encode "é" = [3, 0, 0, 0, 0, 0, 0, 0, 2, 0xc3, 0xa9]
open Canonical in
#guard encode ([] : List Nat) = [4, 0, 0, 0, 0, 0, 0, 0, 0]
open Canonical in
#guard (encode ["a", "b"]).length = 9 + 2 * (9 + 1)
open Canonical in
#guard encode ([1, 2] : Bytes) = [8, 0, 0, 0, 0, 0, 0, 0, 2, 1, 2]
open Canonical in
#guard encode ([1, 2] : List UInt8) = [8, 0, 0, 0, 0, 0, 0, 0, 2, 1, 2]
open Canonical in
#guard encode (some (3 : Nat)) ≠ encode [(3 : Nat)]
open Canonical in
#guard encode ((1 : Nat), "a") ≠ encode ("a", (1 : Nat))
open Canonical in
#guard encode (-1 : Int) = [10, 0, 0, 0, 0, 0, 0, 0, 19, 2, 0, 0, 0, 0, 0, 0, 0, 1, 1,
  2, 0, 0, 0, 0, 0, 0, 0, 0]
open Canonical in
#guard encode (255 : UInt8) = encode (255 : Nat)
open Canonical in
#guard encode (sha256 []) = [8, 0, 0, 0, 0, 0, 0, 0, 32] ++ (sha256 []).bytes
open Canonical in
#guard decode (encode ((7 : Nat), (some "x", [true, false]))) = some ((7 : Nat), (some "x", [true, false]))
open Canonical in
#guard decode (α := Nat) (encode "7") = none
open Canonical in
#guard decode (α := Digest) (encode ([1, 2, 3] : Bytes)) = none
open Canonical in
#guard decode (α := UInt8) (encode (256 : Nat)) = none
open Canonical in
#guard decode (α := Int) (encode (-1 : Int)) = some (-1 : Int)
open Canonical in
#guard (digest (sha256 [])).hex ≠ (sha256 []).hex
-- The address of a string is the address of its bytes: today's `digestOf "Effect.gen"`.
open Canonical in
#guard digest "Effect.gen" = sha256 (Val.encode (.str "Effect.gen"))
open Canonical in
#guard print (some (3 : Nat), "x") = Effect4.Json.arr [Json.ofNat 3, .str "x"]
open Canonical in
#guard (Canonical.document UInt64).references.length = 1

/-! ## Receipts -/

#print axioms Canonical.toVal_injective
#print axioms Canonical.encode
#print axioms Canonical.decode
#print axioms Canonical.decode_encode
#print axioms Canonical.decode_exact
#print axioms Canonical.encode_injective
#print axioms Canonical.ne_of_encode_ne
#print axioms Canonical.digest
#print axioms Canonical.document
#print axioms Canonical.print
#print axioms accepts_mk_of_not_named
#print axioms acceptsList_of_forall
#print axioms acceptsFields_cons
#print axioms accepts_struct
#print axioms accepts_sum
#print axioms acceptsIn_named
#print axioms accepts_option_some
#print axioms accepts_list
#print axioms accepts_pair
#print axioms mem_lookupAll
#print axioms acceptsIn_mono_of_subset
#print axioms accepts_named_of_mem
#print axioms guarded
#print axioms guarded_toVal
#print axioms guarded_exact
#print axioms instCanonicalUnit
#print axioms instCanonicalBool
#print axioms instCanonicalNat
#print axioms instCanonicalString
#print axioms IntCanonical.ofVal_exact
#print axioms IntCanonical.fits
#print axioms instCanonicalInt
#print axioms instCanonicalUInt8
#print axioms instCanonicalUInt64
#print axioms instCanonicalDigest
#print axioms mapM_ofVal_map_toVal
#print axioms mapM_ofVal_exact
#print axioms instCanonicalList
#print axioms instCanonicalOption
#print axioms instCanonicalProd
#print axioms instCanonicalBytes

end Effect4.Store
