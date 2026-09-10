import Effect4.Program.Typed
import Conform.Effect4.Models

/-!
# Conform.Effect4.Membership — the membership adapter: an image's values inhabit a `Ty`

**What it is.** Codex's "membership adapter" (`2026-09-09-type-tooling-design.md` §4: *a typed
value model must additionally connect that representation to `Val.hasTy` at the relevant
allocation environment*), for the images this tree has. Each theorem has the shape

> `Val.hasTy (I.toVal a) ty allocated = true`

and each names its premises: the element's own membership where the image is a container, the
allocation table where a handle is involved. Nothing here assumes an allocation.

**What it finds.** Stating the adapter turned three gaps into theorems rather than prose:

* **`Store.Image.pair` and `Val.hasTy .prod` disagree.** `Image.pair` writes `Val.pair a b`
  (`src/Effect4/Store/Image.lean:276`); `Val.hasTy (.prod ta tb)` accepts only a two-element
  `Val.list` — `Val.tuple`, what `Program.Native` builds
  (`src/Effect4/Program/Typed.lean:60-63`, `src/Effect4/Program/Native.lean:33`). So no value
  of `Image.pair` ever inhabits a `.prod`: `pair_never_hasTy_prod`. The repair is
  `pairTuple` below — the same two element images under the frame `Val.hasTy` reads — and its
  membership theorem is `hasTy_pairTuple`.
* **`Ty.int`, `Ty.except` and `Ty.causeOf` are uninhabited by `Val.hasTy` today.** They fall to its
  final `| _ => false` (`Typed.lean:73`), so no image can have a membership theorem at them at
  all: `hasTy_int_false`, `hasTy_except_false`, `hasTy_causeOf_false`. That is DI-09/DI-17 as a
  theorem; the obligation rows below carry it into the report.
* **A handle needs the allocation premise**, which no image can supply: `handleObligations`.

**Depends on.** `Conform.Effect4.Models`.
-/

set_option autoImplicit false

namespace Conform.Effect4.Membership

open _root_.Effect4 _root_.Effect4.Store _root_.Effect4.Program

/-- `Effect4.Program.Val.hasTy`, spelled once. `Val` here is the store's type, so the dot
notation `Val.hasTy` would look for `Effect4.Store.Val.hasTy`, which does not exist. -/
abbrev hasTy (v : Val) (ty : Ty) (allocated : List String := []) : Bool :=
  _root_.Effect4.Program.Val.hasTy v ty allocated

variable {α β : Type}

/-! ## The scalars -/

theorem hasTy_nat (n : Nat) (allocated : List String) :
    hasTy (Image.nat.toVal n) .nat allocated = true := rfl

theorem hasTy_bool (b : Bool) (allocated : List String) :
    hasTy (Image.bool.toVal b) .bool allocated = true := rfl

theorem hasTy_string (s : String) (allocated : List String) :
    hasTy (Image.string.toVal s) .string allocated = true := rfl

theorem hasTy_unit (u : Unit) (allocated : List String) :
    hasTy (Image.unit.toVal u) .unit allocated = true := rfl

/-! ## The containers, each under its element's membership -/

theorem hasTy_option (I : Image α) (ty : Ty) (allocated : List String)
    (hI : ∀ a, hasTy (I.toVal a) ty allocated = true) (v : Option α) :
    hasTy ((Image.option I).toVal v) (.option ty) allocated = true := by
  cases v with
  | none => rfl
  | some a => exact hI a

theorem hasTy_listAux (I : Image α) (ty : Ty) (allocated : List String)
    (hI : ∀ a, hasTy (I.toVal a) ty allocated = true) :
    ∀ xs : List α, (xs.map I.toVal).all (fun x => hasTy x ty allocated) = true
  | [] => rfl
  | x :: xs => by
    rw [List.map_cons, List.all_cons, hI x, hasTy_listAux I ty allocated hI xs]
    rfl

theorem hasTy_list (I : Image α) (ty : Ty) (allocated : List String)
    (hI : ∀ a, hasTy (I.toVal a) ty allocated = true) (xs : List α) :
    hasTy ((Image.list I).toVal xs) (.list ty) allocated = true :=
  hasTy_listAux I ty allocated hI xs

/-! ## The pair: the image the tree has, and the image `Val.hasTy` reads

`Image.pair` writes `Val.pair`; `Val.hasTy (.prod ta tb)` reads `Val.tuple` (a two-element
`Val.list`). The first theorem is the refusal, the second is the repair. -/

/-- **No value of `Store.Image.pair` inhabits a `.prod`.** -/
theorem pair_never_hasTy_prod (I : Image α) (J : Image β) (ta tb : Ty)
    (allocated : List String) (p : α × β) :
    hasTy ((Image.pair I J).toVal p) (.prod ta tb) allocated = false := rfl

def ofPairTuple (I : Image α) (J : Image β) : Val → Option (α × β)
  | .list [a, b] =>
    match I.ofVal a, J.ofVal b with
    | some x, some y => some (x, y)
    | _, _ => none
  | _ => none

/-- The product under the frame `Val.hasTy` reads: `Val.tuple [a, b]`, which is `Program.Native`'s
own spelling (`Native.lean:33`). Built from the same two element images and the same two laws;
no new codec class. -/
def pairTuple (I : Image α) (J : Image β) : Image (α × β) where
  toVal p := .list [I.toVal p.1, J.toVal p.2]
  ofVal := ofPairTuple I J
  ofVal_toVal p := by
    show (match I.ofVal (I.toVal p.1), J.ofVal (J.toVal p.2) with
      | some x, some y => some (x, y)
      | _, _ => none) = some p
    rw [I.ofVal_toVal, J.ofVal_toVal]
  ofVal_exact := by
    intro v p h
    unfold ofPairTuple at h
    split at h
    · next a b =>
      split at h
      · next x y hx hy =>
        injection h with h
        subst h
        show Val.list [a, b] = Val.list [I.toVal x, J.toVal y]
        rw [I.ofVal_exact hx, J.ofVal_exact hy]
      · exact nomatch h
    · exact nomatch h

theorem hasTy_pairTuple (I : Image α) (J : Image β) (ta tb : Ty) (allocated : List String)
    (hI : ∀ a, hasTy (I.toVal a) ta allocated = true)
    (hJ : ∀ b, hasTy (J.toVal b) tb allocated = true) (p : α × β) :
    hasTy ((pairTuple I J).toVal p) (.prod ta tb) allocated = true := by
  show (hasTy (I.toVal p.1) ta allocated && hasTy (J.toVal p.2) tb allocated) = true
  rw [hI, hJ]
  rfl

/-! ## The types no image can inhabit today

Three of `Ty`'s fifteen constructors fall to `Val.hasTy`'s final `| _ => false`
(`src/Effect4/Program/Typed.lean:73`). A membership theorem at any of them is therefore not
merely unproved: it is false, for every value. -/

theorem hasTy_never_false (v : Val) (allocated : List String) :
    hasTy v .never allocated = false := rfl

theorem hasTy_int_false (v : Val) (allocated : List String) :
    hasTy v .int allocated = false := rfl

theorem hasTy_except_false (v : Val) (e a : Ty) (allocated : List String) :
    hasTy v (.except e a) allocated = false := rfl

theorem hasTy_causeOf_false (v : Val) (e : Ty) (allocated : List String) :
    hasTy v (.causeOf e) allocated = false := rfl

/-! ## The membership of the four composed models

`Option (Option Nat)` and `List (Option Ty)` are the two the containers reach. `Ty` itself has
no `Ty` to be a member of — a `Ty` is a *type*, not a value of the native cut — so
`tyImage`'s membership is not a gap but a category error, and it is recorded as such below
rather than as an obligation. -/

theorem hasTy_optOptNat (allocated : List String) (v : Option (Option Nat)) :
    hasTy (Models.optOptNat.toVal v) (.option (.option .nat)) allocated = true :=
  hasTy_option _ _ allocated (fun a => hasTy_option _ _ allocated (fun n => hasTy_nat n allocated) a) v

/-! ## What remains, as obligations -/

open Conform in
/-- One row per image whose membership needs a premise the model cannot supply, or whose target
type is uninhabited today. -/
def obligations : Array Obligation :=
  #[ { kind := "representation.membership-missing"
       subject := { kind := "image", path := ["Store.Image", "handle"] }
       status := .unsupported
       profile := "hasTy"
       statement := "`Val.hasTy v (.handle target) allocated` needs `allocated[index]? = some \
target` for an external handle (Typed.lean:51); no image carries an allocation table, so the \
membership theorem for a handle image is stated only under an explicit allocation premise \
supplied by the caller" }
   , { kind := "representation.membership-missing"
       subject := { kind := "type", path := ["Effect4.Program.Ty", "int"] }
       status := .refuted
       profile := "hasTy"
       statement := "`Ty.int` is uninhabited by `Val.hasTy` (it falls to the final `_ => false`, \
Typed.lean:73), and `hasTy_int_false` proves it, while `Ty.render` still spells it `number` \
(Eff.lean:73) — a type the checker admits and the value admission never accepts" }
   , { kind := "representation.membership-missing"
       subject := { kind := "type", path := ["Effect4.Program.Ty", "except"] }
       status := .refuted
       profile := "hasTy"
       statement := "`Ty.except` is uninhabited by `Val.hasTy` (`hasTy_except_false`); DI-17" }
   , { kind := "representation.membership-missing"
       subject := { kind := "type", path := ["Effect4.Program.Ty", "causeOf"] }
       status := .refuted
       profile := "hasTy"
       statement := "`Ty.causeOf` is uninhabited by `Val.hasTy` (`hasTy_causeOf_false`); DI-09. \
A cause reaches `Val.hasTy` only inside `.exitOf`, through `causeImage.ofVal` (Typed.lean:58)" }
   , { kind := "representation.law-missing"
       subject := { kind := "image", path := ["Store.Image", "pair"] }
       status := .refuted
       profile := "hasTy"
       statement := "`Store.Image.pair` writes `Val.pair`, and `Val.hasTy (.prod ta tb)` accepts \
only a two-element `Val.list`; `pair_never_hasTy_prod` proves no value of that image inhabits a \
product type. `Conform.Effect4.Membership.pairTuple` is the same composition under the frame \
`Val.hasTy` reads, with `hasTy_pairTuple`" } ]

/-! ## Receipts -/

#print axioms hasTy_nat
#print axioms hasTy_bool
#print axioms hasTy_string
#print axioms hasTy_unit
#print axioms hasTy_option
#print axioms hasTy_listAux
#print axioms hasTy_list
#print axioms pair_never_hasTy_prod
#print axioms pairTuple
#print axioms hasTy_pairTuple
#print axioms hasTy_never_false
#print axioms hasTy_int_false
#print axioms hasTy_except_false
#print axioms hasTy_causeOf_false
#print axioms hasTy_optOptNat

end Conform.Effect4.Membership
