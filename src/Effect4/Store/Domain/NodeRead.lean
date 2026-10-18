module

public import Effect4.Store.Domain.Node

/-!
# Node byte reading

`Node.decode` owns accepted bytes. This module reports the first failure when that decoder refuses.
The diagnostic walk never produces a node. It scans only framed children, and treats bytes as leaves.

Placement: exact-codecs, stored-carrier exact reading, requirement R13.
Question: `cas-node-read-exact`, compatibility; `Node.read_exact` is the claim pointer.
Reach: every byte list, exactly the image of `Node.decode` with its formation and version facts.
Exclusions: graph admission, M2, hash identity, host capacity, and persistence.
Consumer: the raw byte entrance before ordered node admission.
-/

@[expose] public section
set_option autoImplicit false
namespace Effect4.Store.Node

/-- The first failed node-byte check, before store admission. -/
inductive ReadRefusal where
  | shortSpec
  | badVersion (found : UInt8)
  | unregisteredKind (found : UInt8)
  | badFrame
  | trailing
  | unknownTag (found : UInt8)
deriving DecidableEq, Repr

/-- Failure diagnosis only. `none` reports no diagnostic, never a decoded value. -/
def regionError : Nat → Option Nat → Bytes → Option ReadRefusal
  | 0, _, _ => some .badFrame
  | fuel + 1, count, bytes =>
    if count = some 0 then
      if bytes.isEmpty then none else some .trailing
    else if bytes.isEmpty then
      if count = none then none else some .badFrame
    else
      match readFrame bytes with
      | none => some .badFrame
      | some (tag, payload, rest) =>
        let childError := match Tag.ofByte tag with
          | none => some (.unknownTag tag)
          | some .list => regionError fuel none payload
          | some .pair => regionError fuel (some 2) payload
          | some .some => regionError fuel (some 1) payload
          | some .ctor =>
            match readFrame payload with
            | some (indexTag, digits, args) =>
              if indexTag = Tag.nat ∧ digits.head? ≠ some 0 then
                regionError fuel none args
              else some .badFrame
            | none => some .badFrame
          | some _ =>
            if (decodeBody (fun _ => none) tag payload).isSome then none
            else some .badFrame
        match childError with
        | some why => some why
        | none => regionError fuel (count.map Nat.pred) rest

def failure : Bytes → ReadRefusal
  | version :: kind :: rest =>
    if version = 0 then
      match Kind.ofByte? kind with
      | none => .unregisteredKind kind
      | some _ =>
        if rest.length < 32 then .shortSpec
        else
          let payload := rest.drop 32
          (regionError (payload.length + 1) (some 1) payload).getD .badFrame
    else .badVersion version
  | _ => .shortSpec

/-- Read the existing exact decoder; the second walk diagnoses refusal only. -/
def read (bytes : Bytes) : Except ReadRefusal Node :=
  match decode bytes with
  | some n => .ok n
  | none => .error (failure bytes)

/-- Helper for `cas-node-read-exact`: successful reads are exactly the existing decoder. -/
theorem read_ok_iff {bytes : Bytes} {n : Node} :
    read bytes = .ok n ↔ decode bytes = some n := by
  unfold read
  cases hd : decode bytes with
  | none =>
    constructor
    · intro h
      exact nomatch h
    · intro h
      exact nomatch h
  | some m =>
    constructor
    · intro h
      injection h with he
      cases he
      rfl
    · intro h
      injection h with he
      cases he
      rfl

/-- `cas-node-read-exact`, exact-codecs, R13: bytes, payload formation, and node version.
This establishes neither graph admission nor disk integrity. -/
theorem read_exact {bytes : Bytes} {n : Node} (h : read bytes = .ok n) :
    bytes = n.encode ∧ n.payload.WF ∧ n.version = 0 :=
  decode_exact (read_ok_iff.mp h)

end Effect4.Store.Node
