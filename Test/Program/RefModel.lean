import Effect4.Laws.Library.Ref.Operations

/-! Readers of Ref's one-cell laws at numeric and handle values.
Controls distinguish reply from next value, absent cells, malformed callback shapes,
and optional no-write from modifySome's write-back.
These readers establish no whole run or host behavior. -/
set_option autoImplicit false
namespace Test.Program.RefModel
open Effect4.Machine Effect4.Program
open Effect4.Store (Image)
open Effect4.Ref

def stores : Stores := { Stores.empty with refs := [Val.nat 5] }
def inc : Term := .app "succ" (.cons (.var 0) .nil)
def optionalInc : Term := .app "some" (.cons inc .nil)
def noUpdate : Term := .app "none" .nil
-- A separate Boolean reply exercises both components of the model's observation.
def change : Term := .app "pair" (.cons (.lit (.bool true)) (.cons inc .nil))
def optionalChange : Term :=
  .app "pair" (.cons (.lit (.bool true)) (.cons optionalInc .nil))
def unchanged : Term := .app "pair" (.cons (.lit (.bool true)) (.cons noUpdate .nil))

example : syncOpStep (.refMake (Val.nat 3)) stores =
    some ({ stores with refs := [Val.nat 5, Val.nat 3] }, Val.cell ⟨1⟩) :=
  make_agrees Image.nat 3 stores

example : syncOpStep (.refGet ⟨0⟩) stores = some (stores, Val.nat 5) :=
  get_agrees Image.nat 5 rfl

example : syncOpStep (.refSet ⟨0⟩ (Val.nat 6)) stores =
    some ({ stores with refs := [Val.nat 6] }, Val.cell ⟨0⟩) :=
  set_agrees Image.nat 5 rfl 6

example : syncOpStep (.refGetAndSet ⟨0⟩ (Val.nat 6)) stores =
    some ({ stores with refs := [Val.nat 6] }, Val.nat 5) :=
  getAndSet_agrees Image.nat 5 rfl 6

example : syncOpStep (.refSetAndGet ⟨0⟩ (Val.nat 6)) stores =
    some ({ stores with refs := [Val.nat 6] }, Val.nat 6) :=
  setAndGet_agrees Image.nat 5 rfl 6

example : syncOpStep (.refUpdate ⟨0⟩ inc []) stores =
    some ({ stores with refs := [Val.nat 6] }, Val.unit) :=
  update_agrees Image.nat 5 rfl (fun n => n + 1) inc [] rfl

example : syncOpStep (.refGetAndUpdate ⟨0⟩ inc []) stores =
    some ({ stores with refs := [Val.nat 6] }, Val.nat 5) :=
  getAndUpdate_agrees Image.nat 5 rfl (fun n => n + 1) inc [] rfl

example : syncOpStep (.refUpdateAndGet ⟨0⟩ inc []) stores =
    some ({ stores with refs := [Val.nat 6] }, Val.nat 6) :=
  updateAndGet_agrees Image.nat 5 rfl (fun n => n + 1) inc [] rfl

example : syncOpStep (.refUpdateSome ⟨0⟩ optionalInc []) stores =
    some ({ stores with refs := [Val.nat 6] }, Val.unit) :=
  updateSome_agrees Image.nat 5 rfl (fun n => some (n + 1)) optionalInc [] rfl

example : syncOpStep (.refUpdateSome ⟨0⟩ noUpdate []) stores =
    some (stores, Val.unit) :=
  updateSome_agrees Image.nat 5 rfl (fun _ => none) noUpdate [] rfl

example : syncOpStep (.refGetAndUpdateSome ⟨0⟩ optionalInc []) stores =
    some ({ stores with refs := [Val.nat 6] }, Val.nat 5) :=
  getAndUpdateSome_agrees Image.nat 5 rfl (fun n => some (n + 1)) optionalInc [] rfl

example : syncOpStep (.refGetAndUpdateSome ⟨0⟩ noUpdate []) stores =
    some (stores, Val.nat 5) :=
  getAndUpdateSome_agrees Image.nat 5 rfl (fun _ => none) noUpdate [] rfl

example : syncOpStep (.refUpdateSomeAndGet ⟨0⟩ optionalInc []) stores =
    some ({ stores with refs := [Val.nat 6] }, Val.nat 6) :=
  updateSomeAndGet_agrees Image.nat 5 rfl (fun n => some (n + 1)) optionalInc [] rfl

example : syncOpStep (.refUpdateSomeAndGet ⟨0⟩ noUpdate []) stores =
    some (stores, Val.nat 5) :=
  updateSomeAndGet_agrees Image.nat 5 rfl (fun _ => none) noUpdate [] rfl

example : syncOpStep (.refModify ⟨0⟩ change []) stores =
    some ({ stores with refs := [Val.nat 6] }, Val.bool true) :=
  modify_agrees Image.nat Image.bool 5 rfl (fun n => (true, n + 1)) change [] rfl

example : syncOpStep (.refModifySome ⟨0⟩ optionalChange []) stores =
    some ({ stores with refs := [Val.nat 6] }, Val.bool true) :=
  modifySome_agrees Image.nat Image.bool 5 rfl
    (fun n => (true, some (n + 1))) optionalChange [] rfl

example : syncOpStep (.refModifySome ⟨0⟩ unchanged []) stores =
    some (stores, Val.bool true) :=
  modifySome_agrees Image.nat Image.bool 5 rfl (fun _ => (true, none)) unchanged [] rfl

-- Reader at an actual handle value, with no numeric carrier assumption.
example : syncOpStep (.refGet ⟨0⟩)
    { Stores.empty with refs := [Val.promise ⟨7⟩] } =
      some ({ Stores.empty with refs := [Val.promise ⟨7⟩] }, Val.promise ⟨7⟩) :=
  get_agrees Image.ident (Val.promise ⟨7⟩) rfl

-- Reader: the allocation premise fails beyond the cell heap.
example (v : Val) : syncOpStep (.refSet ⟨1⟩ v) stores = none ∧
    syncOpStep (.refGet ⟨1⟩) stores = none :=
  syncOpStep_ref_unallocated (by decide) v

-- Control: set's backing identity is not unit.
#guard (syncOpStep (.refSet ⟨0⟩ (Val.nat 6)) stores).map Prod.snd != some Val.unit

-- Controls: neither a scalar optional callback nor a scalar modify callback has the row's shape.
#guard syncOpStep (.refUpdateSome ⟨0⟩ inc []) stores == none
#guard syncOpStep (.refModify ⟨0⟩ inc []) stores == none

-- Control: changing only the next value cannot pass a reply-and-store observation.
def wrongNext : Term :=
  .app "pair" (.cons (.lit (.bool true)) (.cons (.lit (.nat 99)) .nil))
#guard (syncOpStep (.refModify ⟨0⟩ wrongNext []) stores).map Prod.snd ==
  (syncOpStep (.refModify ⟨0⟩ change []) stores).map Prod.snd
#guard (syncOpStep (.refModify ⟨0⟩ wrongNext []) stores).map Prod.fst !=
  (syncOpStep (.refModify ⟨0⟩ change []) stores).map Prod.fst

-- Control: optional-update None skips writing; modifySome None writes the old value.
#guard (Model.updateSome (fun _ : Nat => none) 5).write == none
#guard (Model.modifySome (fun _ : Nat => (true, none)) 5).write == some 5

end Test.Program.RefModel
