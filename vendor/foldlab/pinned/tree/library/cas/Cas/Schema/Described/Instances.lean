import Cas.Schema.Described.Core

/-!
# Primitive described types

Only carriers represented exactly by the current schema universe receive
instances. In particular, unrestricted `Nat` and top-level `Option`
do not.
-/

namespace Cas.Schema

instance : Described Unit where
  code := .null
  wf := by trivial
  toEl := id
  ofEl := id
  ofEl_toEl := by intro x; rfl
  toEl_ofEl := by intro x; rfl

instance : Described Bool where
  code := .bool
  wf := by trivial
  toEl := id
  ofEl := id
  ofEl_toEl := by intro x; rfl
  toEl_ofEl := by intro x; rfl

instance : Described SafeInt where
  code := .int
  wf := by trivial
  toEl := id
  ofEl := id
  ofEl_toEl := by intro x; rfl
  toEl_ofEl := by intro x; rfl

instance : Described String where
  code := .str
  wf := by trivial
  toEl := id
  ofEl := id
  ofEl_toEl := by intro x; rfl
  toEl_ofEl := by intro x; rfl

instance {tag : UInt8} : Described (StoreRef tag) where
  code := .ref tag
  wf := by trivial
  toEl := id
  ofEl := id
  ofEl_toEl := by intro x; rfl
  toEl_ofEl := by intro x; rfl

instance {α : Type u} [d : Described α] : Described (List α) where
  code := .arr d.code
  wf := d.wf
  toEl := List.map d.toEl
  ofEl := List.map d.ofEl
  ofEl_toEl := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      change d.ofEl (d.toEl x) :: List.map d.ofEl (List.map d.toEl xs) = x :: xs
      rw [d.ofEl_toEl x, ih]
  toEl_ofEl := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      change d.toEl (d.ofEl x) :: List.map d.toEl (List.map d.ofEl xs) = x :: xs
      rw [d.toEl_ofEl x, ih]

end Cas.Schema
