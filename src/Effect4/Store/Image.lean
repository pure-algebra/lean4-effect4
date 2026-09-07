import Effect4.Store.Val

/-!
# Store.Image

Owner: the exact-image trait of a carrier in the value tree *without* a shape, the byte codec
derived from it once, and the combinators that build the image of a compound carrier from the
images of its parts.

`Canonical` (`Store/Canonical.lean`) is this trait plus a `shape` and its `fits` law, and every
`Canonical` carrier is an `Image` (`Canonical.image`, declared there). The Machine layer cannot
name a `Shape` without importing the Schema plane (`Store/Shape.lean` imports
`Effect4.Schema.Authoring`), so the runtime's views of the shared carrier — the handle kinds,
exits, causes, contexts and configuration results of
`docs/research/2026-09-07-u0-value-foundation.md` — are stated at this level, over `Val` alone.
The laws are `Canonical`'s two: every image reads back (`ofVal_toVal`), and nothing outside
the image reads (`ofVal_exact`). An `Image` is a structure, not a class: a carrier may have
more than one image (a fiber identity is a `ctor` inside a cause and a `handle` as a value),
and the choice is written at the use site.

The byte codec is derived as `Canonical`'s is: `encode = Val.encode ∘ toVal`, `decode` reads
one tree and then the carrier, `decode_encode` under the tree's well-formedness,
`decode_exact` unconditionally, and the checked `encode?`, which answers bytes only for a
well-formed tree, so a `some` answer is itself the receipt that the bytes read back
(review R5: handle validity says nothing about payload sizes; the size check is explicit).

The combinators write the frames the generated `Canonical` instances write
(`src/Effect4/Program/Derived.lean`): `Option` as `none`/`some`, a list as `list`, a product as
`pair`, a structure as `ctor 0 [fields…]`, a case of a sum as `ctor i [args…]`. A hand-written
image built from them is therefore byte-identical to the instance the generator would emit for
the same declaration, which is what lets the OCaml side share one decoder.
-/

set_option autoImplicit false

namespace Effect4.Store

/-- An exact image in the value tree: the writer, the reader, and the two laws. -/
structure Image (α : Type) where
  /-- The value tree of a carrier. -/
  toVal : α → Val
  /-- The carrier of a value tree, when it is one. -/
  ofVal : Val → Option α
  /-- Every image reads back. -/
  ofVal_toVal : ∀ a, ofVal (toVal a) = some a
  /-- Nothing outside the image reads. -/
  ofVal_exact : ∀ {v a}, ofVal v = some a → v = toVal a

namespace Image

variable {α β γ : Type}

/-- Exactness makes the image injective. -/
theorem toVal_injective (I : Image α) {a b : α} (h : I.toVal a = I.toVal b) : a = b := by
  have h1 := I.ofVal_toVal a
  rw [h, I.ofVal_toVal] at h1
  exact (Option.some.inj h1).symm

/-- The reader is a function of the writer: two images with one writer read alike. -/
theorem ofVal_eq_of_toVal_eq (I J : Image α) (h : ∀ a, I.toVal a = J.toVal a) (v : Val) :
    I.ofVal v = J.ofVal v := by
  cases hI : I.ofVal v with
  | none =>
    cases hJ : J.ofVal v with
    | none => rfl
    | some a =>
      have := I.ofVal_toVal a
      rw [h a, ← J.ofVal_exact hJ, hI] at this
      exact nomatch this
  | some a =>
    rw [I.ofVal_exact hI, h a, J.ofVal_toVal]

/-! ## Bytes, derived once -/

/-- The canonical bytes of a carrier: the bytes of its value tree. -/
def encode (I : Image α) (a : α) : Bytes := Val.encode (I.toVal a)

/-- The exact decoder: the whole byte string is one value tree, and that tree is a carrier. -/
def decode (I : Image α) (b : Bytes) : Option α := (Val.decode b).bind I.ofVal

/-- The checked encoder: bytes only when the tree is well-formed. -/
def encode? (I : Image α) (a : α) : Option Bytes := Val.encode? (I.toVal a)

theorem decode_encode (I : Image α) (a : α) (h : (I.toVal a).WF) :
    I.decode (I.encode a) = some a := by
  unfold decode encode
  rw [Val.decode_encode _ h, Option.bind_some, I.ofVal_toVal]

theorem decode_exact (I : Image α) {b : Bytes} {a : α} (h : I.decode b = some a) :
    b = I.encode a ∧ (I.toVal a).WF := by
  unfold decode at h
  obtain ⟨v, hv, ha⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hb, hwf⟩ := Val.decode_exact hv
  have hva := I.ofVal_exact ha
  subst hva
  exact ⟨hb, hwf⟩

/-- A `some` answer of the checked encoder reads back, with no side condition. -/
theorem decode_encode? (I : Image α) {a : α} {b : Bytes} (h : I.encode? a = some b) :
    I.decode b = some a := by
  unfold decode
  rw [Val.decode_encode? h, Option.bind_some, I.ofVal_toVal]

/-- Whatever decodes is what the checked encoder answers for its carrier. -/
theorem encode?_of_decode (I : Image α) {b : Bytes} {a : α} (h : I.decode b = some a) :
    I.encode? a = some b := by
  unfold decode at h
  obtain ⟨v, hv, ha⟩ := Option.bind_eq_some_iff.mp h
  have hva := I.ofVal_exact ha
  subst hva
  exact Val.encode?_of_decode hv

/-! ## Primitive images: the frames `Canonical`'s instances write -/

def ofUnit : Val → Option Unit
  | .unit => some ()
  | _ => none

/-- `Unit` as the `unit` frame. -/
def unit : Image Unit where
  toVal _ := .unit
  ofVal := ofUnit
  ofVal_toVal _ := rfl
  ofVal_exact := by
    intro v a h
    unfold ofUnit at h
    split at h
    · rfl
    · exact nomatch h

def ofBool : Val → Option Bool
  | .bool b => some b
  | _ => none

/-- `Bool` as the `bool` frame. -/
def bool : Image Bool where
  toVal b := .bool b
  ofVal := ofBool
  ofVal_toVal _ := rfl
  ofVal_exact := by
    intro v a h
    unfold ofBool at h
    split at h
    · injection h with h
      subst h
      rfl
    · exact nomatch h

def ofNat : Val → Option Nat
  | .nat n => some n
  | _ => none

/-- `Nat` as the `nat` frame. -/
def nat : Image Nat where
  toVal n := .nat n
  ofVal := ofNat
  ofVal_toVal _ := rfl
  ofVal_exact := by
    intro v a h
    unfold ofNat at h
    split at h
    · injection h with h
      subst h
      rfl
    · exact nomatch h

def ofString : Val → Option String
  | .str s => some s
  | _ => none

/-- `String` as the `string` frame. -/
def string : Image String where
  toVal s := .str s
  ofVal := ofString
  ofVal_toVal _ := rfl
  ofVal_exact := by
    intro v a h
    unfold ofString at h
    split at h
    · injection h with h
      subst h
      rfl
    · exact nomatch h

/-! ## Combinators -/

section combinators

/-- `Option.map_eq_some_iff`'s forward direction, by cases: the core lemma reaches
`Quot.sound`, and an image's reader is part of the runtime's definitions, whose axiom
receipts the coverage snapshot pins. -/
theorem map_eq_some_inv {α β : Type} {f : α → β} {o : Option α} {b : β} (h : o.map f = some b) :
    ∃ a, o = some a ∧ f a = b := by
  cases o with
  | none => exact nomatch h
  | some a => exact ⟨a, rfl, Option.some.inj h⟩

variable (I : Image α) (J : Image β) (K : Image γ)

/-- Transport an image along an isomorphism of carriers. -/
def equiv (f : α → β) (g : β → α) (hfg : ∀ b, f (g b) = b) (hgf : ∀ a, g (f a) = a) :
    Image β where
  toVal b := I.toVal (g b)
  ofVal v := (I.ofVal v).map f
  ofVal_toVal b := by
    show (I.ofVal (I.toVal (g b))).map f = some b
    rw [I.ofVal_toVal, Option.map_some, hfg]
  ofVal_exact := by
    intro v b h
    obtain ⟨a, ha, hb⟩ := map_eq_some_inv h
    subst hb
    show v = I.toVal (g (f a))
    rw [hgf, I.ofVal_exact ha]

/-- Restrict an image to the carriers a decidable predicate admits: the reader refuses the
rest. A structure with a `Prop` field is this image transported along its projection. -/
def subtype (p : α → Prop) [DecidablePred p] : Image {a // p a} where
  toVal s := I.toVal s.val
  ofVal v :=
    match I.ofVal v with
    | some a => if h : p a then some ⟨a, h⟩ else none
    | none => none
  ofVal_toVal s := by
    show (match I.ofVal (I.toVal s.val) with
      | some a => if h : p a then some ⟨a, h⟩ else none
      | none => none) = some s
    rw [I.ofVal_toVal]
    show (if h : p s.val then some (⟨s.val, h⟩ : {a // p a}) else none) = some s
    rw [dif_pos s.property]
  ofVal_exact := by
    intro v s h
    split at h
    · next a ha =>
      split at h
      · next hp =>
        injection h with h
        subst h
        exact I.ofVal_exact ha
      · exact nomatch h
    · exact nomatch h

def toOption : Option α → Val
  | none => .none
  | some a => .some (I.toVal a)

def ofOption : Val → Option (Option α)
  | .none => some none
  | .some v => (I.ofVal v).map some
  | _ => none

/-- `Option` as `none`/`some`. -/
def option : Image (Option α) where
  toVal := toOption I
  ofVal := ofOption I
  ofVal_toVal := by
    intro a
    cases a with
    | none => rfl
    | some a =>
      show (I.ofVal (I.toVal a)).map some = some (some a)
      rw [I.ofVal_toVal, Option.map_some]
  ofVal_exact := by
    intro v a h
    unfold ofOption at h
    split at h
    · injection h with h
      subst h
      rfl
    · next w =>
      obtain ⟨x, hx, hj⟩ := map_eq_some_inv h
      subst hj
      show Val.some w = Val.some (I.toVal x)
      rw [I.ofVal_exact hx]
    · exact nomatch h

def toPair : α × β → Val := fun p => .pair (I.toVal p.1) (J.toVal p.2)

def ofPair : Val → Option (α × β)
  | .pair a b =>
    match I.ofVal a, J.ofVal b with
    | some x, some y => some (x, y)
    | _, _ => none
  | _ => none

/-- A product as `pair`. -/
def pair : Image (α × β) where
  toVal := toPair I J
  ofVal := ofPair I J
  ofVal_toVal := by
    intro p
    show ofPair I J (.pair (I.toVal p.1) (J.toVal p.2)) = some p
    simp only [ofPair, I.ofVal_toVal, J.ofVal_toVal]
  ofVal_exact := by
    intro v p h
    unfold ofPair at h
    split at h
    · next a b =>
      split at h
      · next x y hx hy =>
        injection h with h
        subst h
        show Val.pair a b = Val.pair (I.toVal x) (J.toVal y)
        rw [I.ofVal_exact hx, J.ofVal_exact hy]
      · exact nomatch h
    · exact nomatch h

def toList : List α → Val := fun xs => .list (xs.map I.toVal)

def ofListAux : List Val → Option (List α)
  | [] => some []
  | v :: vs =>
    match I.ofVal v, ofListAux vs with
    | some x, some xs => some (x :: xs)
    | _, _ => none

def ofList : Val → Option (List α)
  | .list vs => ofListAux I vs
  | _ => none

theorem ofListAux_map (xs : List α) : ofListAux I (xs.map I.toVal) = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    show (match I.ofVal (I.toVal x), ofListAux I (xs.map I.toVal) with
      | some x, some xs => some (x :: xs)
      | _, _ => none) = some (x :: xs)
    rw [I.ofVal_toVal, ih]

theorem ofListAux_exact : ∀ {vs : List Val} {xs : List α},
    ofListAux I vs = some xs → vs = xs.map I.toVal := by
  intro vs
  induction vs with
  | nil =>
    intro xs h
    unfold ofListAux at h
    injection h with h
    subst h
    rfl
  | cons v vs ih =>
    intro xs h
    unfold ofListAux at h
    split at h
    · next x xs' hx hxs =>
      injection h with h
      subst h
      simp only [List.map_cons]
      rw [I.ofVal_exact hx, ih hxs]
    · exact nomatch h

/-- A list as `list`. -/
def list : Image (List α) where
  toVal := toList I
  ofVal := ofList I
  ofVal_toVal xs := ofListAux_map I xs
  ofVal_exact := by
    intro v xs h
    unfold ofList at h
    split at h
    · next vs =>
      show Val.list vs = Val.list (xs.map I.toVal)
      rw [ofListAux_exact I h]
    · exact nomatch h

def ofCtor1 (i : Nat) : Val → Option α
  | .ctor j [a] => if j = i then I.ofVal a else none
  | _ => none

/-- One field under constructor `i`: a one-field structure (`i = 0`) or a one-field case. -/
def ctor1 (i : Nat) : Image α where
  toVal a := .ctor i [I.toVal a]
  ofVal := ofCtor1 I i
  ofVal_toVal a := by
    show (if i = i then I.ofVal (I.toVal a) else none) = some a
    rw [if_pos rfl, I.ofVal_toVal]
  ofVal_exact := by
    intro v a h
    unfold ofCtor1 at h
    split at h
    · next j w =>
      split at h
      · next hj =>
        show Val.ctor j [w] = Val.ctor i [I.toVal a]
        rw [hj, I.ofVal_exact h]
      · exact nomatch h
    · exact nomatch h

def ofCtor2 (i : Nat) : Val → Option (α × β)
  | .ctor j [a, b] =>
    if j = i then
      match I.ofVal a, J.ofVal b with
      | some x, some y => some (x, y)
      | _, _ => none
    else none
  | _ => none

/-- Two fields under constructor `i`. -/
def ctor2 (i : Nat) : Image (α × β) where
  toVal p := .ctor i [I.toVal p.1, J.toVal p.2]
  ofVal := ofCtor2 I J i
  ofVal_toVal p := by
    show (if i = i then
      match I.ofVal (I.toVal p.1), J.ofVal (J.toVal p.2) with
      | some x, some y => some (x, y)
      | _, _ => none
      else none) = some p
    rw [if_pos rfl, I.ofVal_toVal, J.ofVal_toVal]
  ofVal_exact := by
    intro v p h
    unfold ofCtor2 at h
    split at h
    · next j a b =>
      split at h
      · next hj =>
        split at h
        · next x y hx hy =>
          injection h with h
          subst h
          show Val.ctor j [a, b] = Val.ctor i [I.toVal x, J.toVal y]
          rw [hj, I.ofVal_exact hx, J.ofVal_exact hy]
        · exact nomatch h
      · exact nomatch h
    · exact nomatch h

def ofCtor3 (i : Nat) : Val → Option (α × β × γ)
  | .ctor j [a, b, c] =>
    if j = i then
      match I.ofVal a, J.ofVal b, K.ofVal c with
      | some x, some y, some z => some (x, y, z)
      | _, _, _ => none
    else none
  | _ => none

/-- Three fields under constructor `i`. -/
def ctor3 (i : Nat) : Image (α × β × γ) where
  toVal p := .ctor i [I.toVal p.1, J.toVal p.2.1, K.toVal p.2.2]
  ofVal := ofCtor3 I J K i
  ofVal_toVal p := by
    show (if i = i then
      match I.ofVal (I.toVal p.1), J.ofVal (J.toVal p.2.1), K.ofVal (K.toVal p.2.2) with
      | some x, some y, some z => some (x, y, z)
      | _, _, _ => none
      else none) = some p
    rw [if_pos rfl, I.ofVal_toVal, J.ofVal_toVal, K.ofVal_toVal]
  ofVal_exact := by
    intro v p h
    unfold ofCtor3 at h
    split at h
    · next j a b c =>
      split at h
      · next hj =>
        split at h
        · next x y z hx hy hz =>
          injection h with h
          subst h
          show Val.ctor j [a, b, c] = Val.ctor i [I.toVal x, J.toVal y, K.toVal z]
          rw [hj, I.ofVal_exact hx, J.ofVal_exact hy, K.ofVal_exact hz]
        · exact nomatch h
      · exact nomatch h
    · exact nomatch h

end combinators

/-! ## Handle-freedom

A tree with no `handle` frame is content. The primitive images write none, and every
combinator writes exactly the handles of its parts; the runtime views use these to show that
a cause carries none, which is `Val.keys`'s "a reified failed exit carries a cause only"
(`src/Effect4/Machine/Handles.lean`) on the shared carrier. -/

/-- No handle under any image of the carrier. -/
def HandleFree (I : Image α) : Prop := ∀ a, (I.toVal a).handles = []

theorem unit_handleFree : HandleFree unit := fun _ => rfl
theorem bool_handleFree : HandleFree bool := fun _ => rfl
theorem nat_handleFree : HandleFree nat := fun _ => rfl
theorem string_handleFree : HandleFree string := fun _ => rfl

theorem equiv_handleFree (I : Image α) (f : α → β) (g : β → α) (hfg : ∀ b, f (g b) = b)
    (hgf : ∀ a, g (f a) = a) (h : HandleFree I) : HandleFree (I.equiv f g hfg hgf) :=
  fun b => h (g b)

theorem subtype_handleFree (I : Image α) (p : α → Prop) [DecidablePred p] (h : HandleFree I) :
    HandleFree (I.subtype p) :=
  fun s => h s.val

theorem option_handleFree (I : Image α) (h : HandleFree I) : HandleFree (option I) := by
  intro a
  cases a with
  | none => rfl
  | some a =>
    show (Val.some (I.toVal a)).handles = []
    rw [Val.handles, h a]

theorem pair_handleFree (I : Image α) (J : Image β) (hI : HandleFree I) (hJ : HandleFree J) :
    HandleFree (pair I J) := by
  intro p
  show (Val.pair (I.toVal p.1) (J.toVal p.2)).handles = []
  rw [Val.handles, hI, hJ]
  rfl

theorem handlesList_map_eq_nil (I : Image α) (h : HandleFree I) (xs : List α) :
    Val.handlesList (xs.map I.toVal) = [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.map_cons, Val.handlesList_cons, h x, ih]
    rfl

theorem list_handleFree (I : Image α) (h : HandleFree I) : HandleFree (list I) := by
  intro xs
  show (Val.list (xs.map I.toVal)).handles = []
  rw [Val.handles]
  exact handlesList_map_eq_nil I h xs

theorem ctor1_handleFree (I : Image α) (i : Nat) (h : HandleFree I) : HandleFree (ctor1 I i) := by
  intro a
  show (Val.ctor i [I.toVal a]).handles = []
  rw [Val.handles, Val.handlesList_cons, h a, Val.handlesList_nil]
  rfl

theorem ctor2_handleFree (I : Image α) (J : Image β) (i : Nat) (hI : HandleFree I)
    (hJ : HandleFree J) : HandleFree (ctor2 I J i) := by
  intro p
  show (Val.ctor i [I.toVal p.1, J.toVal p.2]).handles = []
  rw [Val.handles, Val.handlesList_cons, Val.handlesList_cons, hI, hJ, Val.handlesList_nil]
  rfl

theorem ctor3_handleFree (I : Image α) (J : Image β) (K : Image γ) (i : Nat) (hI : HandleFree I)
    (hJ : HandleFree J) (hK : HandleFree K) : HandleFree (ctor3 I J K i) := by
  intro p
  show (Val.ctor i [I.toVal p.1, J.toVal p.2.1, K.toVal p.2.2]).handles = []
  rw [Val.handles, Val.handlesList_cons, Val.handlesList_cons, Val.handlesList_cons, hI, hJ, hK,
    Val.handlesList_nil]
  rfl

end Image

/-! ## Receipts -/

#print axioms Image.toVal_injective
#print axioms Image.ofVal_eq_of_toVal_eq
#print axioms Image.decode_encode
#print axioms Image.decode_exact
#print axioms Image.decode_encode?
#print axioms Image.encode?_of_decode
#print axioms Image.equiv
#print axioms Image.subtype
#print axioms Image.option
#print axioms Image.pair
#print axioms Image.list
#print axioms Image.ctor1
#print axioms Image.ctor2
#print axioms Image.ctor3
#print axioms Image.list_handleFree
#print axioms Image.ctor3_handleFree

end Effect4.Store
