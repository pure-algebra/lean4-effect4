module

public import Effect4.Store.Domain.NodeRead

/-!
# Typed node reading

The reader checks version, kind, spec, then the canonical payload.
The genesis uses `specFor`, so its zero spec remains valid.

Placement: exact-codecs, typed stored-carrier exactness, R13.
Question: `cas-get-exact`, compatibility; `Node.readContent_exact` is its helper.
Reach: successful reading gives exactly `nodeOf` of the returned carrier.
Exclusions: hash injectivity, graph closure, host persistence, and program admission.
Consumer: `Cas.get_exact` and session-chain loading.
-/

@[expose] public section
set_option autoImplicit false
namespace Effect4.Store
open Effect4 (Document)
variable [Content Document]

inductive ReadRefusal where
  | missing (digest : Digest)
  | kind (expected actual : Kind)
  | spec
  | version (found : Nat)
  | payload
deriving DecidableEq, Repr

def Node.expectedSpec (α : Type) [Content α] (payload : Val) : Digest :=
  if Content.kind α = .schema ∧ payload = toVal metaSchema then zeroDigest else specOf α

def Node.readContent {α : Type} [Content α] (n : Node) : Except Effect4.Store.ReadRefusal α :=
  if n.version = 0 then
    if n.kind = Content.kind α then
      if n.spec = Node.expectedSpec α n.payload then
        match ofVal n.payload with
        | some a => .ok a
        | none => .error .payload
      else .error .spec
    else .error (.kind (Content.kind α) n.kind)
  else .error (.version n.version.toNat)

theorem Node.expectedSpec_toVal {α : Type} [Content α] (a : α) :
    Node.expectedSpec α (toVal a) = specFor a := rfl

theorem Node.readContent_exact {α : Type} [Content α] {n : Node} {a : α}
    (h : Node.readContent n = .ok a) : n = nodeOf a := by
  unfold Node.readContent at h
  split at h
  · next hv =>
    split at h
    · next hk =>
      split at h
      · next hs =>
        split at h
        · next a' hp =>
          injection h with he
          subst a'
          have hp' := ofVal_exact hp
          have hs' : n.spec = specFor a := by
            rw [hp', Node.expectedSpec_toVal] at hs
            exact hs
          cases n
          cases hv
          cases hk
          cases hs'
          cases hp'
          rfl
        · exact nomatch h
      · exact nomatch h
    · exact nomatch h
  · exact nomatch h

theorem Node.readContent_nodeOf {α : Type} [Content α] (a : α) : Node.readContent (nodeOf a) = .ok a := by
  unfold Node.readContent nodeOf
  rw [if_pos rfl, if_pos rfl, Node.expectedSpec_toVal, if_pos rfl, ofVal_toVal]

end Effect4.Store
