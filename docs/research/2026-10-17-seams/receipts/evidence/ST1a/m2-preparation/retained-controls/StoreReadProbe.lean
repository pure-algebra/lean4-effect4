import Effect4.Store.Domain.Genesis

/-!
ST1a scout placement, before proof:
Concept: exact-codecs, stored-carrier exact reading; requirement R13.
Question: proposed `cas-get-exact`; the implementation's `Cas.get_exact` consumes `readNode_exact`.
Reach: a version-zero resident Node, expected Content kind and specFor, successful canonical payload read.
Exclusions: no program admission, collision resistance, graph closure, disk integrity, or host refinement.
Consumer: ST1a checked read; ST4 session-chain loading uses its exact stored carrier.
This isolated probe proves the payload reader, not the Cas reachability wrapper.
-/

set_option autoImplicit false
namespace StoreReadProbe
open Effect4 Effect4.Store

inductive ReadRefusal where
  | kind (expected actual : Kind)
  | spec
  | version (found : UInt8)
  | payload
deriving DecidableEq, Repr

def expectedSpec (α : Type) [Content α] (payload : Val) : Digest :=
  if Content.kind α = .schema ∧ payload = toVal metaSchema then zeroDigest else specOf α

def readNode {α : Type} [Content α] (n : Node) : Except ReadRefusal α :=
  if n.version = 0 then
    if n.kind = Content.kind α then
      if n.spec = expectedSpec α n.payload then
        match ofVal n.payload with
        | some a => .ok a
        | none => .error .payload
      else .error .spec
    else .error (.kind (Content.kind α) n.kind)
  else .error (.version n.version)

theorem expectedSpec_toVal {α : Type} [Content α] (a : α) :
    expectedSpec α (toVal a) = specFor a := rfl

theorem readNode_exact {α : Type} [Content α] {n : Node} {a : α}
    (h : readNode n = .ok a) : n = nodeOf a := by
  unfold readNode at h
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
            rw [hp', expectedSpec_toVal] at hs
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

theorem readNode_nodeOf {α : Type} [Content α] (a : α) : readNode (nodeOf a) = .ok a := by
  unfold readNode nodeOf
  rw [if_pos rfl, if_pos rfl, expectedSpec_toVal, if_pos rfl, ofVal_toVal]

def isRunRelative : Kind → Bool
  | .tape | .log | .exits | .checkpoint => true
  | _ => false

def handleInContent (n : Node) : Bool := !isRunRelative n.kind && !n.payload.handles.isEmpty

def oldRead {α : Type} [Content α] (n : Node) : Option α :=
  if n.kind = Content.kind α then ofVal n.payload else none

def naïveSpecRead {α : Type} [Content α] (n : Node) : Option α :=
  if n.spec = specOf α then ofVal n.payload else none

-- The old byte-independent payload reader accepts bad version and wrong spec.
-- The new reader rejects both; kind precedes spec, which precedes payload.
instance : Content Nat where kind := .«export»

def refuses {α : Type} (result : Except ReadRefusal α) (why : ReadRefusal) : Bool :=
  match result with
  | .ok _ => false
  | .error e => decide (e = why)

#guard oldRead (α := Nat) ⟨1, .«export», zeroDigest, .nat 7⟩ = some 7
#guard refuses (readNode (α := Nat) ⟨1, .«export», zeroDigest, .nat 7⟩) (.version 1)
#guard oldRead (α := Nat) ⟨0, .«export», zeroDigest, .nat 7⟩ = some 7
#guard refuses (readNode (α := Nat) ⟨0, .«export», zeroDigest, .nat 7⟩) .spec
#guard refuses (readNode (α := Nat) ⟨0, .tree, zeroDigest, .unit⟩) (.kind .«export» .tree)
#guard refuses (readNode (α := Nat) ⟨0, .«export», zeroDigest, .unit⟩) .spec
#guard (readNode (α := Nat) (nodeOf (7 : Nat))).toOption = some 7
#guard refuses (readNode (α := Nat) ⟨0, .«export», specOf Nat, .unit⟩) .payload

-- The genesis uses zero, so an always-specOf reader rejects its own carrier.
#guard naïveSpecRead (α := Document) genesisNode = none
#guard (readNode (α := Document) genesisNode).toOption = some metaSchema

-- The smallest M2 counterexample has no payload reference or spec edge.
def handleGenesis : Node := ⟨0, .schema, zeroDigest, .handle 2 7⟩
#guard handleGenesis.payload.wf
#guard !handleGenesis.malformedRef
#guard handleGenesis.checkedEdges = []
#guard handleInContent handleGenesis
#guard match Store.empty.putNode handleGenesis with
  | .ok (.fresh, _, _) => true
  | _ => false
#guard !handleInContent ⟨0, .tape, zeroDigest, .handle 2 7⟩

end StoreReadProbe

#eval IO.println "StoreReadProbe: exact typed node reader, genesis and old M2 controls pass"
