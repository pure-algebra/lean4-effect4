import Effect4.Store.Image.Containers
import Effect4.Program.Typed
import Effect4.Schema.Codec

/-! Concrete values connected to the existing program value image. The storage
Image/Canonical instances and their bytes do not change. Refined images describe a
subset of a program type; no completeness of arbitrary schema materialization is implied. -/
set_option autoImplicit false
namespace Effect4.Schema
open Effect4 Effect4.Program
open Effect4.Store (Image)

structure ProgramImage (α : Type) (t : Ty) extends Image α where
  fits : ∀ a, Val.hasTy (toVal a) t = true

namespace ProgramImage
variable {α β : Type} {a b : Ty}

def nat : ProgramImage Nat .nat := ⟨Image.nat, fun _ => rfl⟩
def string : ProgramImage String .string := ⟨Image.string, fun _ => rfl⟩
def bool : ProgramImage Bool .bool := ⟨Image.bool, fun _ => rfl⟩
def unit : ProgramImage Unit .unit := ⟨Image.unit, fun _ => rfl⟩

def pair (I : ProgramImage α a) (J : ProgramImage β b) :
    ProgramImage (α × β) (.prod a b) where
  toImage := I.toImage.tuple2 J.toImage
  fits p := by simp [Image.tuple2, Val.hasTy, I.fits, J.fits]

def option (I : ProgramImage α a) : ProgramImage (Option α) (.option a) where
  toImage := I.toImage.option
  fits v := by cases v <;> simp [Image.option, Image.toOption, Val.hasTy, I.fits]

def list (I : ProgramImage α a) : ProgramImage (List α) (.list a) where
  toImage := I.toImage.list
  fits xs := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [Image.list, Image.toList, Val.hasTy, I.fits]

def imap (I : ProgramImage α a) (f : α → β) (g : β → α)
    (fg : ∀ b, f (g b) = b) (gf : ∀ a, g (f a) = a) : ProgramImage β a where
  toImage := I.toImage.equiv f g fg gf
  fits b := I.fits (g b)

def refine (I : ProgramImage α a) (p : α → Prop) [DecidablePred p] :
    ProgramImage {x // p x} a where
  toImage := I.toImage.subtype p
  fits x := I.fits x.val

/-- Concrete JSON encoding remains fallible on the S-3 exact-value domain. -/
def encode (I : ProgramImage α a) (value : α) : Option Json :=
  Schema.encode a (I.toVal value)

/-- Refinements are checked by the concrete image after program-level decoding. -/
def decode (I : ProgramImage α a) (wire : Json) : Option α :=
  (Schema.decode a wire).bind I.ofVal
end ProgramImage
end Effect4.Schema
