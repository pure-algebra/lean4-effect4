module

public import Effect4.Store.Domain.Store
public import Effect4.Store.Domain.Read
public import Effect4.Store.Domain.Transaction

/-!
# Reached stores and typed reads

`CasOf replay` contains a store reached by its named event interpreter.
ST1b fixes that parameter to atomic transactions and interrupted publication.
This module claims no admission or atomicity property of an arbitrary interpreter.

Placement: exact-codecs, stored-carrier exact reading, requirement R13.
Question: `cas-get-exact`, compatibility; `Cas.get_exact` is the claim pointer.
Reach: successful typed reading names the exact resident node, including the genesis spec.
Exclusions: collision resistance, disk integrity, and properties of an arbitrary replay parameter.
Consumer: session-chain loading in ST4.
-/

@[expose] public section
set_option autoImplicit false
namespace Effect4.Store
open Effect4 (Document)

/-- Transaction failures preserve the failing node index or root name. -/
inductive TxnRefusal where
  | node (index : Nat) (why : Admission)
  | noRoot (name : String)
  | staleRoot (name : String) (expected actual : Option (Head Digest))
  | pinned (name : String)
  | target (name : String) (why : Admission)
  | fork (name : String) (head target : Digest)
  deriving DecidableEq, Repr

/-- A store with evidence of its own event interpreter's successful replay. -/
structure CasOf (replay : List Event → Except TxnRefusal Store) where
  private mk ::
  store : Store
  reached : ∃ events, replay events = .ok store

/-- Construction runs the stated replay. No caller supplies an unchecked store. -/
@[no_expose] def CasOf.ofReplay (replay : List Event → Except TxnRefusal Store) (events : List Event) :
    Except TxnRefusal (CasOf replay) :=
  match h : replay events with
  | .error why => .error why
  | .ok store => .ok (CasOf.mk store ⟨events, h⟩)

namespace Cas
variable [Content Document]

/-- Read by address, then check version, kind, per-value spec, and exact payload. -/
def get {replay : List Event → Except TxnRefusal Store} {α : Type} [Content α]
    (cas : CasOf replay) (ref : Ref α) : Except ReadRefusal α :=
  match cas.store.find ref.digest with
  | none => .error (.missing ref.digest)
  | some node => node.readContent

/-- `cas-get-exact`: a successful read gives the resident carrier's exact node.
The replay parameter remains explicit; this law assumes no hash injectivity or host persistence. -/
theorem get_exact {replay : List Event → Except TxnRefusal Store} {α : Type} [Content α]
    {cas : CasOf replay} {ref : Ref α} {value : α} (h : get cas ref = .ok value) :
    cas.store.find ref.digest = some (nodeOf value) := by
  unfold get at h
  split at h
  · exact nomatch h
  · next node found =>
    have exactNode := Node.readContent_exact h
    rw [exactNode] at found
    exact found

/-- Helper for `cas-get-exact`: reading the exact resident image returns its carrier. -/
theorem get_nodeOf {replay : List Event → Except TxnRefusal Store} {α : Type} [Content α]
    {cas : CasOf replay} {ref : Ref α} (value : α)
    (found : cas.store.find ref.digest = some (nodeOf value)) : get cas ref = .ok value := by
  unfold get
  rw [found]
  exact Node.readContent_nodeOf value

/-- Helper for `cas-get-exact`: an accepted non-conflicting put returns its exact carrier.
`Test.Store.ProgramContent` consumes this law at programs. -/
theorem get_put {replay : List Event → Except TxnRefusal Store}
    {α : Type} [Content α] {a : α} {before : Store} {after : CasOf replay}
    {o : Outcome} {r : Ref α} (h : before.put a = .ok (o, r, after.store))
    (hc : ∀ m, o ≠ .conflict m) : get after r = .ok a :=
  get_nodeOf a (putNode_find (put_ok h).1 hc)

/-- Helper for `cas-get-exact`: a put retains the exact resident behind an earlier read.
`trait_get_preserves` consumes this fact at annotations. -/
theorem get_preserves {replay : List Event → Except TxnRefusal Store}
    {α β : Type} [Content α] [Content β] {a : α} {before after : CasOf replay}
    {o : Outcome} {r : Ref α} {q : Ref β} {b : β} (hg : get before q = .ok b)
    (h : before.store.put a = .ok (o, r, after.store)) : get after q = .ok b :=
  get_nodeOf b (put_preserves (get_exact hg) h)

end Cas
end Effect4.Store
