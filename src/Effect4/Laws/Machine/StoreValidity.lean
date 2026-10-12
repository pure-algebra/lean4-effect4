import Effect4.Machine.Stores

/-!
# The store allocation predicate and the value validity definitions

Placement: store-typing, R4. These existing definitions serve the name relation's
`validIn_iff_diag` and the store validity laws in `StoresLaws.lean`.
The declarations move without changing their bodies, statements or namespaces.
The list lemma is the shared list fold used by the generated value-fold adapter.
No machine operation, schedule or host judgment changes.
-/

set_option autoImplicit false
namespace Effect4.Machine

/-- One handle's kind byte and index against the store (plan §3.1, ENSURES 12): a cell byte
needs a heap index (`Stores.lean` `refPeek`), a promise byte a Deferred cell index
(`cellAt`), a scope byte a scope entry (`entryAt`); a fiber byte is the machine's, not the
store's, and is accepted; a `memoMap` byte a memo map (`MemoWorld.mapAt`, the join); an
unregistered byte names nothing this store holds. -/
def Stores.handleValid (s : Stores) (kind : UInt8) (index : Nat) : Bool :=
  match HandleKind.ofByte? kind with
  | some .fiber => true
  | some .cell => index < s.refs.length
  | some .promise => index < s.deferreds.cells.length
  | some .scope => (s.scopes.entryAt index).isSome
  | some .memoMap => (s.memo.mapAt ⟨index⟩).isSome
  | some .external => index < s.externals.allocated.length
  | none => false

mutual
/-- A value's handles exist in the store (plan §3.1, ENSURES 12): every `handle` frame the
carrier carries, through `Stores.handleValid` — a `Val.cell` names a heap index, a
`Val.promise` a Deferred cell, a `Val.scopeHandle` a scope entry, a context its ambient scope;
a reified exit, a snapshot and a list are valid when their parts are; a tree with no handle
(a number, a reified failed exit, whose cause writes none) is valid everywhere.
`Val.validIn_eq_handles` is the fold over `Store.Val.handles`. -/
def Val.validIn (s : Stores) : Val → Bool
  | .handle kind index => s.handleValid kind index
  | .list values => Val.validInList s values
  | .pair a b => Val.validIn s a && Val.validIn s b
  | .some a => Val.validIn s a
  | .ctor _ args => Val.validInList s args
  | _ => true
/-- Every value of a list is valid. -/
def Val.validInList (s : Stores) : List Val → Bool
  | [] => true
  | value :: rest => Val.validIn s value && Val.validInList s rest
end

theorem Val.validInList_eq_all (s : Stores) (values : List Val) :
    Val.validInList s values = values.all (Val.validIn s) := by
  induction values with
  | nil => rfl
  | cons value rest ih => rw [Val.validInList, ih, List.all_cons]


end Effect4.Machine
