import Effect4.Evidence.Char.Conformance.GSet
import Effect4.Evidence.Char.Conformance.Vector
import Effect4.Store.Genesis

/-!
# Char.Canonical — the hand instances of the room's generic carriers

Owner: the `Canonical` and `Content` instances that `Effect4Gen` cannot write, and the one
helper that builds an untyped pointer from a typed address.

Everything monomorphic in the Char room is generated into `Evidence/Char/Derived.lean` by
`tools/Effect4Gen/Main.lean`. The generator does not yet take a **bare parameter** (lane G's
open item, `NOTES-L1.md` of 2026-09-05 01:19), so the four carriers with one below them —
`GSet α`, `ClientReading C`, `Fact L C`, `Vector L C` — and, through them, `VectorSet L C` are
written here by hand, in the generator's own shape: a `shapeDoc`, a `toVal`, an `ofVal`, the
three laws and the instance per carrier, on the `Prod`/`List` templates of
`Store/Canonical.lean:486-601` and the emitted templates of `Store/PinDerived.lean:74-168`.
Nothing here is a shortcut: every instance carries `ofVal_toVal`, `ofVal_exact` and `fits`, so
the class's derived exactness (`Canonical.decode_exact`) holds for them as for a generated one.

They sit in namespace `Effect4.Store`, as the generated files do, because `Effect4.Store`
exports `shape`, `toVal`, `ofVal`, `ofVal_toVal`, `ofVal_exact` and `fits`
(`Store/Canonical.lean:45`): only a namespace nested inside `Effect4.Store` lets a per-carrier
`toVal` shadow the exported field name, which is exactly how `Store/PinDerived.lean` reads.
Carrier names are written from the root for the same reason.

`Provenance` is monomorphic and would have been generated, but `Vector L C` and `VectorSet L C`
carry it and both are needed **before** `Derived.lean` exists (`Conformance/Consume.lean`
addresses a `Fact`, `Conformance/Surface.lean` a `VectorSet`), so its instance is hand here
beside them rather than generated behind them. That is the one carrier this lane hand-wrote
that the landing's rule would have generated; its shape is the same six-case sum the generator
emits, so moving it later costs a regeneration and no proof.

Kinds (plan §3, row 14): a fact, a vector and a vector set file under `vector`. The `GSet`
instance is generic, so **every** grow-only set files under `vector`, the receipt set of
`Conformance/Consume.lean` included; the kind byte is not injective on types (Q3), so
`Ref Receipts` and `Ref (VectorSet L C)` stay different Lean types over the one byte. The
alternative — a `Content Receipts` at `annotation` — cannot be written before
`Canonical Receipt` exists, and that instance is inside the generated file, so it would need a
second hand module below `Derived.lean`; the choice is recorded in `workshop/Cas/NOTES-X.md`
for the coordinator.
-/

set_option autoImplicit false
-- A generic carrier's laws mention its parameters' instances only through the definitions they
-- unfold to, so the section variables read as unused; they are not.
set_option linter.unusedSectionVars false

namespace Effect4.Store

/-! ## `GSet α`: a struct over its list state -/

namespace CharGSetC

variable {α : Type} [Canonical α]

def shapeDoc : ShapeDoc :=
  ⟨.struct "GSet" [("elems", (shape (_root_.List α)).root)], (shape (_root_.List α)).defs⟩

def toVal : _root_.Effect4.Char.GSet α → Val
  | .mk a0 => .ctor 0 [Canonical.toVal a0]

def ofVal : Val → Option (_root_.Effect4.Char.GSet α)
  | .ctor 0 [v0] =>
    match Canonical.ofVal (α := _root_.List α) v0 with
    | some a0 => some ⟨a0⟩
    | _ => none
  | _ => none

theorem ofVal_toVal (a : _root_.Effect4.Char.GSet α) : ofVal (toVal a) = some a := by
  obtain ⟨a0⟩ := a
  simp [toVal, ofVal, Canonical.ofVal_toVal]

theorem ofVal_exact {v : Val} {a : _root_.Effect4.Char.GSet α} (h : ofVal v = some a) :
    v = toVal a := by
  unfold ofVal at h
  split at h
  · next v0 =>
    split at h
    · next b0 h0 =>
      injection h with h
      subst h
      simp only [toVal]
      rw [Canonical.ofVal_exact h0]
    · exact nomatch h
  · exact nomatch h

theorem lift_elems (x : _root_.List α) :
    acceptsIn (shapeDoc (α := α)).defs (shape (_root_.List α)).root (Canonical.toVal x) = true :=
  acceptsIn_mono_of_subset (fun _ hp => hp) _ _ (Canonical.fits x)

theorem fits (a : _root_.Effect4.Char.GSet α) :
    (shapeDoc (α := α)).accepts (toVal a) = true := by
  obtain ⟨a0⟩ := a
  apply accepts_struct
  exact acceptsFields_cons _ _ _ _ _ _ (lift_elems a0) (acceptsFields_nil _)

instance instCanonical : Canonical (_root_.Effect4.Char.GSet α) :=
  ⟨shapeDoc (α := α), toVal, ofVal, ofVal_toVal, ofVal_exact, fits⟩

/-- Every grow-only set of the conformance layer files under kind `vector`. -/
instance instContent : Content (_root_.Effect4.Char.GSet α) := ⟨.vector⟩

end CharGSetC

/-! ## `ClientReading C`: what one client saw -/

namespace CharClientReadingC

variable {C : Type} [Canonical C]

def shapeDoc : ShapeDoc :=
  ⟨.struct "ClientReading"
     [("client", (shape C).root), ("acc", (shape (_root_.List _root_.Effect4.Char.Item)).root),
      ("del", (shape (_root_.List _root_.Effect4.Char.Item)).root),
      ("residue", (shape (_root_.List _root_.Effect4.Char.Item)).root)],
   (shape C).defs ++ (shape (_root_.List _root_.Effect4.Char.Item)).defs⟩

def toVal : _root_.Effect4.Char.ClientReading C → Val
  | .mk a0 a1 a2 a3 =>
    .ctor 0 [Canonical.toVal a0, Canonical.toVal a1, Canonical.toVal a2, Canonical.toVal a3]

def ofVal : Val → Option (_root_.Effect4.Char.ClientReading C)
  | .ctor 0 [v0, v1, v2, v3] =>
    match Canonical.ofVal (α := C) v0,
        Canonical.ofVal (α := _root_.List _root_.Effect4.Char.Item) v1,
        Canonical.ofVal (α := _root_.List _root_.Effect4.Char.Item) v2,
        Canonical.ofVal (α := _root_.List _root_.Effect4.Char.Item) v3 with
    | some a0, some a1, some a2, some a3 => some ⟨a0, a1, a2, a3⟩
    | _, _, _, _ => none
  | _ => none

theorem ofVal_toVal (a : _root_.Effect4.Char.ClientReading C) : ofVal (toVal a) = some a := by
  obtain ⟨a0, a1, a2, a3⟩ := a
  simp [toVal, ofVal, Canonical.ofVal_toVal]

theorem ofVal_exact {v : Val} {a : _root_.Effect4.Char.ClientReading C} (h : ofVal v = some a) :
    v = toVal a := by
  unfold ofVal at h
  split at h
  · next v0 v1 v2 v3 =>
    split at h
    · next b0 b1 b2 b3 h0 h1 h2 h3 =>
      injection h with h
      subst h
      simp only [toVal]
      rw [Canonical.ofVal_exact h0, Canonical.ofVal_exact h1, Canonical.ofVal_exact h2,
        Canonical.ofVal_exact h3]
    · exact nomatch h
  · exact nomatch h

theorem lift_client (x : C) :
    acceptsIn (shapeDoc (C := C)).defs (shape C).root (Canonical.toVal x) = true :=
  acceptsIn_mono_of_subset (fun _ hp => mem_append_of_left hp) _ _ (Canonical.fits x)

theorem lift_items (x : _root_.List _root_.Effect4.Char.Item) :
    acceptsIn (shapeDoc (C := C)).defs (shape (_root_.List _root_.Effect4.Char.Item)).root
      (Canonical.toVal x) = true :=
  acceptsIn_mono_of_subset (fun _ hp => mem_append_of_right hp) _ _ (Canonical.fits x)

theorem fits (a : _root_.Effect4.Char.ClientReading C) :
    (shapeDoc (C := C)).accepts (toVal a) = true := by
  obtain ⟨a0, a1, a2, a3⟩ := a
  apply accepts_struct
  exact
    (acceptsFields_cons _ _ _ _ _ _ (lift_client a0)
      (acceptsFields_cons _ _ _ _ _ _ (lift_items a1)
        (acceptsFields_cons _ _ _ _ _ _ (lift_items a2)
          (acceptsFields_cons _ _ _ _ _ _ (lift_items a3) (acceptsFields_nil _)))))

instance instCanonical : Canonical (_root_.Effect4.Char.ClientReading C) :=
  ⟨shapeDoc (C := C), toVal, ofVal, ofVal_toVal, ofVal_exact, fits⟩

end CharClientReadingC

/-! ## `Provenance`: the six-case tag -/

namespace CharProvenanceC

def shapeDoc : ShapeDoc :=
  ⟨.sum "Provenance"
     [("authored", [("test", .string)]),
      ("mutantKill", [("mutant", .string), ("test", .string)]),
      ("mutantSurvives", [("mutant", .string), ("test", .string)]),
      ("enumerated", [("depth", .nat)]),
      ("refused", [("depth", .nat)]),
      ("doctest", [("span", .string), ("ratifiedBy", .string)])],
   []⟩

def toVal : _root_.Effect4.Char.Provenance → Val
  | .authored a0 => .ctor 0 [.str a0]
  | .mutantKill a0 a1 => .ctor 1 [.str a0, .str a1]
  | .mutantSurvives a0 a1 => .ctor 2 [.str a0, .str a1]
  | .enumerated a0 => .ctor 3 [.nat a0]
  | .refused a0 => .ctor 4 [.nat a0]
  | .doctest a0 a1 => .ctor 5 [.str a0, .str a1]

def ofVal : Val → Option (_root_.Effect4.Char.Provenance)
  | .ctor 0 [.str a0] => some (.authored a0)
  | .ctor 1 [.str a0, .str a1] => some (.mutantKill a0 a1)
  | .ctor 2 [.str a0, .str a1] => some (.mutantSurvives a0 a1)
  | .ctor 3 [.nat a0] => some (.enumerated a0)
  | .ctor 4 [.nat a0] => some (.refused a0)
  | .ctor 5 [.str a0, .str a1] => some (.doctest a0 a1)
  | _ => none

theorem ofVal_toVal (a : _root_.Effect4.Char.Provenance) : ofVal (toVal a) = some a := by
  cases a <;> rfl

theorem ofVal_exact {v : Val} {a : _root_.Effect4.Char.Provenance} (h : ofVal v = some a) :
    v = toVal a := by
  unfold ofVal at h
  split at h
  all_goals first
    | (injection h with h; subst h; rfl)
    | exact nomatch h

theorem fits (a : _root_.Effect4.Char.Provenance) : shapeDoc.accepts (toVal a) = true := by
  cases a <;> rfl

instance instCanonical : Canonical (_root_.Effect4.Char.Provenance) :=
  ⟨shapeDoc, toVal, ofVal, ofVal_toVal, ofVal_exact, fits⟩

end CharProvenanceC

/-! ## `Fact L C`: the addressed unit -/

namespace CharFactC

variable {L C : Type} [Canonical L] [Canonical C]

def shapeDoc : ShapeDoc :=
  ⟨.struct "Fact"
     [("word", (shape (_root_.List L)).root), ("accept", (shape _root_.Bool).root),
      ("readings", (shape (_root_.List (_root_.Effect4.Char.ClientReading C))).root)],
   (shape (_root_.List L)).defs ++ (shape _root_.Bool).defs ++
     (shape (_root_.List (_root_.Effect4.Char.ClientReading C))).defs⟩

def toVal : _root_.Effect4.Char.Fact L C → Val
  | .mk a0 a1 a2 => .ctor 0 [Canonical.toVal a0, Canonical.toVal a1, Canonical.toVal a2]

def ofVal : Val → Option (_root_.Effect4.Char.Fact L C)
  | .ctor 0 [v0, v1, v2] =>
    match Canonical.ofVal (α := _root_.List L) v0, Canonical.ofVal (α := _root_.Bool) v1,
        Canonical.ofVal (α := _root_.List (_root_.Effect4.Char.ClientReading C)) v2 with
    | some a0, some a1, some a2 => some ⟨a0, a1, a2⟩
    | _, _, _ => none
  | _ => none

theorem ofVal_toVal (a : _root_.Effect4.Char.Fact L C) : ofVal (toVal a) = some a := by
  obtain ⟨a0, a1, a2⟩ := a
  simp [toVal, ofVal, Canonical.ofVal_toVal]

theorem ofVal_exact {v : Val} {a : _root_.Effect4.Char.Fact L C} (h : ofVal v = some a) :
    v = toVal a := by
  unfold ofVal at h
  split at h
  · next v0 v1 v2 =>
    split at h
    · next b0 b1 b2 h0 h1 h2 =>
      injection h with h
      subst h
      simp only [toVal]
      rw [Canonical.ofVal_exact h0, Canonical.ofVal_exact h1, Canonical.ofVal_exact h2]
    · exact nomatch h
  · exact nomatch h

theorem lift_word (x : _root_.List L) :
    acceptsIn (shapeDoc (L := L) (C := C)).defs (shape (_root_.List L)).root
      (Canonical.toVal x) = true :=
  acceptsIn_mono_of_subset (fun _ hp => mem_append_of_left (mem_append_of_left hp))
    _ _ (Canonical.fits x)

theorem lift_accept (x : _root_.Bool) :
    acceptsIn (shapeDoc (L := L) (C := C)).defs (shape _root_.Bool).root
      (Canonical.toVal x) = true :=
  acceptsIn_mono_of_subset (fun _ hp => mem_append_of_left (mem_append_of_right hp))
    _ _ (Canonical.fits x)

theorem lift_readings (x : _root_.List (_root_.Effect4.Char.ClientReading C)) :
    acceptsIn (shapeDoc (L := L) (C := C)).defs
      (shape (_root_.List (_root_.Effect4.Char.ClientReading C))).root
      (Canonical.toVal x) = true :=
  acceptsIn_mono_of_subset (fun _ hp => mem_append_of_right hp) _ _ (Canonical.fits x)

theorem fits (a : _root_.Effect4.Char.Fact L C) :
    (shapeDoc (L := L) (C := C)).accepts (toVal a) = true := by
  obtain ⟨a0, a1, a2⟩ := a
  apply accepts_struct
  exact
    (acceptsFields_cons _ _ _ _ _ _ (lift_word a0)
      (acceptsFields_cons _ _ _ _ _ _ (lift_accept a1)
        (acceptsFields_cons _ _ _ _ _ _ (lift_readings a2) (acceptsFields_nil _))))

instance instCanonical : Canonical (_root_.Effect4.Char.Fact L C) :=
  ⟨shapeDoc (L := L) (C := C), toVal, ofVal, ofVal_toVal, ofVal_exact, fits⟩

/-- A fact is the addressed unit of the conformance layer: kind `vector`. -/
instance instContent : Content (_root_.Effect4.Char.Fact L C) := ⟨.vector⟩

end CharFactC

/-! ## `Vector L C`: the fact with its tags -/

namespace CharVectorC

variable {L C : Type} [Canonical L] [Canonical C]

def shapeDoc : ShapeDoc :=
  ⟨.struct "Vector"
     [("fact", (shape (_root_.Effect4.Char.Fact L C)).root),
      ("tags", (shape (_root_.List _root_.Effect4.Char.Provenance)).root)],
   (shape (_root_.Effect4.Char.Fact L C)).defs ++
     (shape (_root_.List _root_.Effect4.Char.Provenance)).defs⟩

def toVal : _root_.Effect4.Char.Vector L C → Val
  | .mk a0 a1 => .ctor 0 [Canonical.toVal a0, Canonical.toVal a1]

def ofVal : Val → Option (_root_.Effect4.Char.Vector L C)
  | .ctor 0 [v0, v1] =>
    match Canonical.ofVal (α := _root_.Effect4.Char.Fact L C) v0,
        Canonical.ofVal (α := _root_.List _root_.Effect4.Char.Provenance) v1 with
    | some a0, some a1 => some ⟨a0, a1⟩
    | _, _ => none
  | _ => none

theorem ofVal_toVal (a : _root_.Effect4.Char.Vector L C) : ofVal (toVal a) = some a := by
  obtain ⟨a0, a1⟩ := a
  simp [toVal, ofVal, Canonical.ofVal_toVal]

theorem ofVal_exact {v : Val} {a : _root_.Effect4.Char.Vector L C} (h : ofVal v = some a) :
    v = toVal a := by
  unfold ofVal at h
  split at h
  · next v0 v1 =>
    split at h
    · next b0 b1 h0 h1 =>
      injection h with h
      subst h
      simp only [toVal]
      rw [Canonical.ofVal_exact h0, Canonical.ofVal_exact h1]
    · exact nomatch h
  · exact nomatch h

theorem lift_fact (x : _root_.Effect4.Char.Fact L C) :
    acceptsIn (shapeDoc (L := L) (C := C)).defs (shape (_root_.Effect4.Char.Fact L C)).root
      (Canonical.toVal x) = true :=
  acceptsIn_mono_of_subset (fun _ hp => mem_append_of_left hp) _ _ (Canonical.fits x)

theorem lift_tags (x : _root_.List _root_.Effect4.Char.Provenance) :
    acceptsIn (shapeDoc (L := L) (C := C)).defs
      (shape (_root_.List _root_.Effect4.Char.Provenance)).root
      (Canonical.toVal x) = true :=
  acceptsIn_mono_of_subset (fun _ hp => mem_append_of_right hp) _ _ (Canonical.fits x)

theorem fits (a : _root_.Effect4.Char.Vector L C) :
    (shapeDoc (L := L) (C := C)).accepts (toVal a) = true := by
  obtain ⟨a0, a1⟩ := a
  apply accepts_struct
  exact
    (acceptsFields_cons _ _ _ _ _ _ (lift_fact a0)
      (acceptsFields_cons _ _ _ _ _ _ (lift_tags a1) (acceptsFields_nil _)))

instance instCanonical : Canonical (_root_.Effect4.Char.Vector L C) :=
  ⟨shapeDoc (L := L) (C := C), toVal, ofVal, ofVal_toVal, ofVal_exact, fits⟩

/-- A vector is a stored unit of the conformance layer: kind `vector`. -/
instance instContent : Content (_root_.Effect4.Char.Vector L C) := ⟨.vector⟩

end CharVectorC

end Effect4.Store

namespace Effect4.Char

open Effect4.Store

/-! ## The untyped pointer -/

/-- The untyped form of `address`: the node address of a value with the kind its own `Content`
instance files it under. The two places a monomorphic carrier points at a parameterised one —
`Receipt.vector` and `Characterized.vectors` — use it, because they cannot name the pointee's
type arguments (Q4's `AnyRef`). -/
def anyRef {α : Type} [Content α] (a : α) : AnyRef := ⟨Content.kind α, (address a).digest⟩

theorem anyRef_kind {α : Type} [Content α] (a : α) : (anyRef a).kind = Content.kind α := rfl

theorem anyRef_digest {α : Type} [Content α] (a : α) :
    (anyRef a).digest = (address a).digest := rfl

/-! ## The laws, run

The three class laws are `#guard`ed on one closed value of each generic carrier at
`L = C = Nat`, and the kinds are read back. A byte appended or dropped is refused, which is
`Canonical.decode_exact` made executable. -/

private def sampleReading : ClientReading Nat := ⟨7, [1, 2], [1], [2]⟩

private def sampleFact : Fact Nat Nat := ⟨[3, 4], true, [sampleReading]⟩

private def sampleVector : Vector Nat Nat := ⟨sampleFact, [.authored "t", .enumerated 2]⟩

private def sampleSet : GSet Nat := GSet.ofList [1, 2, 2, 3]

#guard Canonical.decode (α := ClientReading Nat) (Canonical.encode sampleReading) =
  some sampleReading
#guard Canonical.decode (α := Fact Nat Nat) (Canonical.encode sampleFact) = some sampleFact
#guard Canonical.decode (α := Vector Nat Nat) (Canonical.encode sampleVector) = some sampleVector
#guard Canonical.decode (α := GSet Nat) (Canonical.encode sampleSet) = some sampleSet
#guard Canonical.decode (α := Fact Nat Nat) (Canonical.encode sampleFact ++ [0]) = none
#guard Canonical.decode (α := Vector Nat Nat) (Canonical.encode sampleVector).dropLast = none
#guard [Provenance.authored "t", .mutantKill "m" "t", .mutantSurvives "m" "t", .enumerated 1,
    .refused 2, .doctest "s" "r"].all fun p =>
  Canonical.decode (α := Provenance) (Canonical.encode p) = some p
#guard (Canonical.shape (Vector Nat Nat)).accepts (Canonical.toVal sampleVector)
#guard (Canonical.shape (GSet Nat)).accepts (Canonical.toVal sampleSet)
#guard Content.kind (Fact Nat Nat) = .vector
#guard Content.kind (Vector Nat Nat) = .vector
#guard Content.kind (GSet Nat) = .vector
#guard (anyRef sampleFact).kind = .vector
-- `anyRef_digest` is the other half, by `rfl`; it is not `#guard`ed, because evaluating a node
-- address evaluates the genesis (a SHA-256 of ninety-two kilobytes, the landing's note on the
-- kernel cost), and a library module owes no such receipt.

/-! ## Receipts -/

#print axioms anyRef
#print axioms anyRef_kind
#print axioms anyRef_digest
#print axioms Effect4.Store.CharGSetC.toVal
#print axioms Effect4.Store.CharGSetC.ofVal
#print axioms Effect4.Store.CharGSetC.ofVal_toVal
#print axioms Effect4.Store.CharGSetC.ofVal_exact
#print axioms Effect4.Store.CharGSetC.lift_elems
#print axioms Effect4.Store.CharGSetC.fits
#print axioms Effect4.Store.CharGSetC.instCanonical
#print axioms Effect4.Store.CharGSetC.instContent
#print axioms Effect4.Store.CharClientReadingC.toVal
#print axioms Effect4.Store.CharClientReadingC.ofVal
#print axioms Effect4.Store.CharClientReadingC.ofVal_toVal
#print axioms Effect4.Store.CharClientReadingC.ofVal_exact
#print axioms Effect4.Store.CharClientReadingC.fits
#print axioms Effect4.Store.CharClientReadingC.instCanonical
#print axioms Effect4.Store.CharProvenanceC.toVal
#print axioms Effect4.Store.CharProvenanceC.ofVal
#print axioms Effect4.Store.CharProvenanceC.ofVal_toVal
#print axioms Effect4.Store.CharProvenanceC.ofVal_exact
#print axioms Effect4.Store.CharProvenanceC.fits
#print axioms Effect4.Store.CharProvenanceC.instCanonical
#print axioms Effect4.Store.CharFactC.toVal
#print axioms Effect4.Store.CharFactC.ofVal
#print axioms Effect4.Store.CharFactC.ofVal_toVal
#print axioms Effect4.Store.CharFactC.ofVal_exact
#print axioms Effect4.Store.CharFactC.fits
#print axioms Effect4.Store.CharFactC.instCanonical
#print axioms Effect4.Store.CharFactC.instContent
#print axioms Effect4.Store.CharVectorC.toVal
#print axioms Effect4.Store.CharVectorC.ofVal
#print axioms Effect4.Store.CharVectorC.ofVal_toVal
#print axioms Effect4.Store.CharVectorC.ofVal_exact
#print axioms Effect4.Store.CharVectorC.fits
#print axioms Effect4.Store.CharVectorC.instCanonical
#print axioms Effect4.Store.CharVectorC.instContent

end Effect4.Char
