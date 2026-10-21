import Effect4.Laws.Api.Object

/-! Probe: the object's stored-data claims are two exact embeddings and their composite.
An exact embedding in the dictionary's sense (§3.5): write, read, retraction on its domain,
exactness. The normaliser is the identity. -/

set_option autoImplicit false
namespace Probe
open Effect4 Effect4.Program Effect4.Store

/-- The dictionary's exact embedding: total on its domain, retraction there, exact everywhere. -/
structure Exact (α β : Type) where
  write : α → β
  read : β → Option α
  dom : α → Prop
  retract : ∀ a, dom a → read (write a) = some a
  exact : ∀ {b a}, read b = some a → b = write a

/-- Exact embeddings compose: write forward, read backward through both. -/
def Exact.comp {α β γ : Type} (f : Exact α β) (g : Exact β γ) : Exact α γ where
  write a := g.write (f.write a)
  read c := (g.read c).bind f.read
  dom a := f.dom a ∧ g.dom (f.write a)
  retract a h := by
    rw [g.retract _ h.2, Option.bind_some, f.retract a h.1]
  exact := by
    intro c a h
    obtain ⟨b, hb, ha⟩ := Option.bind_eq_some_iff.mp h
    rw [g.exact hb, f.exact ha]

/-- `Built ↪ Object`: forget the certificate; read back by admission. Total. -/
def builtObject : Exact Api.Built Object where
  write := Object.ofBuilt
  read o := o.open.toOption
  dom _ := True
  retract b _ := by
    rw [Object.open_ofBuilt]
    rfl
  exact := by
    intro o b h
    cases ho : o.open with
    | error e =>
      rw [ho] at h
      cases h
    | ok c =>
      rw [ho] at h
      cases h
      exact (Object.ofBuilt_of_open ho).symm

/-- `Object ↪ Bytes`: the store node. Total on the storable objects (`Val.WF`). -/
def objectBytes : Exact Object Bytes where
  write := Object.bytes
  read bs := (Object.read bs).toOption
  dom o := (toVal o).WF
  retract o h := by
    rw [Object.read_bytes o h]
    rfl
  exact := by
    intro bs o h
    cases hr : Object.read bs with
    | error e =>
      rw [hr] at h
      cases h
    | ok p =>
      rw [hr] at h
      cases h
      exact (Object.read_exact hr).1

/-- `load` is the composite's reader, pointwise. -/
theorem load_toOption (bs : Bytes) :
    (Object.load bs).toOption = (builtObject.comp objectBytes).read bs := by
  show (Object.load bs).toOption = ((Object.read bs).toOption.bind fun o => o.open.toOption)
  unfold Object.load
  cases hr : Object.read bs with
  | error e => rfl
  | ok o =>
    dsimp only
    show (Except.mapError Object.LoadRefusal.admission o.open).toOption = o.open.toOption
    cases o.open <;> rfl

/-- So `load_bytes` is the composite's retraction, and `load_exact` its exactness. -/
example (b : Api.Built) (h : (toVal (Object.ofBuilt b)).WF) :
    (Object.load (Object.bytes (Object.ofBuilt b))).toOption = some b := by
  rw [load_toOption]
  exact (builtObject.comp objectBytes).retract b ⟨trivial, h⟩

example {bs : Bytes} {b : Api.Built} (h : Object.load bs = .ok b) :
    bs = Object.bytes (Object.ofBuilt b) := by
  have h' : (Object.load bs).toOption = some b := by rw [h]; rfl
  rw [load_toOption] at h'
  exact (builtObject.comp objectBytes).exact h'

end Probe
