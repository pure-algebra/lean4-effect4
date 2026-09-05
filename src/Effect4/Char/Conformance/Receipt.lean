import Effect4.Char.Conformance.VectorSet

/-!
# Conformance.Receipt: the implementation pin set and the receipt

Owner: the two carriers a replay is keyed by, and the grow-only set they live in. `consume`,
the oracle and the `Target` they are consumed under stay in `Conformance/Consume.lean`; this
module exists because the typed references of Q4 order the room's carriers in one line —
`Implementation ≺ Receipt ≺ Evidence ≺ Claim ≺ Manifest ≺ Target ≺ Characterized` — and
`Receipt` therefore has to be declared below `Char/Evidence.lean`, which names it in
`Evidence.fixture`, while `Target.model : Ref Manifest` puts `Target` above `Char/Manifest.lean`.
One module cannot be both. The data has no cycle; only the old file did.

A `Receipt` is a named `Bool` over first-order data, keyed by the **address of the vector** and
the **address of the implementation pin set**. Both keys are references now and not bare
digests (Q4): the vector's is an `AnyRef` at kind `vector`, because a monomorphic `Receipt`
cannot name the `Fact L C` it points at, and the pin set's is a typed `Ref Implementation`.
The shape of `06-gates/01-decidable-receipt.md` with the two keys; the TypeScript driver emits
this shape and reads the addresses as lowercase hex, which `Digest.hex` still prints.

A receipt that holds is the `replayed` rung's evidence and never more: it projects to the pair
`Evidence.fixture` takes in `Char/Evidence.lean`, which is now that same `AnyRef` and a
`Ref Receipt`. A failing receipt is a finding, not evidence. Two receipts for one vector and
one pin set with different verdicts are both kept and the verdict is then `false`: a replay
that is not deterministic is a finding, never a green.

The two canonical instances are here rather than in `Char/Derived.lean` for the same
ordering reason: `Char/Evidence.lean` needs `Content Receipt` (to shape `Ref Receipt`) and the
generated file is below it. They are the generator's own output for these two structures,
copied unedited from a run that emitted them, and they go back to the generated file as soon
as it can be emitted above `Char/Evidence.lean` — the bytes are the same either way, so no
address moves.
-/

set_option autoImplicit false

namespace Effect4.Char

open Effect4.Store

/-- **The implementation pin set**: the bytes and the run mode a receipt is about,
and nothing about the model. Its address is the `pin` key of every receipt. The
model digest is deliberately outside it: a vector is a fact that carries its own
expectation, so extending the alphabet moves the manifest and leaves every old
receipt keyed as it was. Driver bytes are also outside it, for the same reason. -/
structure Implementation where
  /-- The package, e.g. `"effect"`. -/
  package : String
  /-- The version, e.g. `"4.0.0-rc.112"`. -/
  version : String
  /-- Span digests of the pinned verbs, in verb order. A span digest is a foreign hash — it
  names no node and is checked by recomputation (Q4) — so it stays a `Digest`. -/
  pins : List Digest
  /-- The run mode the determinism argument of `04-harness/03` is made for: `"runSync"`. -/
  driver : String
  /-- The host pin (the node version, or `"absent"`). -/
  host : String
deriving DecidableEq, Repr

/-- **A receipt**: a named `Bool` over first-order data, keyed by the vector's
address and the implementation pin set's address. -/
structure Receipt where
  /-- Always `"replay"` here; the gate's obligation vocabulary. -/
  obligation : String
  /-- The vector's node address, at kind `vector`. Untyped, because a monomorphic `Receipt`
  cannot name the `Fact L C` the node carries. -/
  vector : AnyRef
  /-- The pin set's node address: never the model and never the driver bytes. -/
  pin : Ref Implementation
  /-- The verdict. -/
  holds : Bool
  /-- What was compared and, on `false`, what was found. Never a summary. -/
  detail : String
deriving DecidableEq, Repr

/-- The grow-only set of receipts. Its own node files under kind `vector` with every other
grow-only set (`Char/Canonical.lean`). -/
abbrev Receipts := GSet Receipt

end Effect4.Char

/-! ## The canonical instances, emitted by `Effect4Gen` and pasted here -/

namespace Effect4.Store

namespace CharImplementationC

def shapeDoc : ShapeDoc :=
  ⟨.struct "Implementation" [("package", (shape _root_.String).root),
     ("version", (shape _root_.String).root),
     ("pins", (shape (_root_.List (_root_.Effect4.Store.Digest))).root),
     ("driver", (shape _root_.String).root), ("host", (shape _root_.String).root)],
   (shape _root_.String).defs ++ (shape (_root_.List (_root_.Effect4.Store.Digest))).defs⟩

def toVal : _root_.Effect4.Char.Implementation → Val
  | .mk a0 a1 a2 a3 a4 => .ctor 0 [Canonical.toVal a0, Canonical.toVal a1, Canonical.toVal a2,
      Canonical.toVal a3, Canonical.toVal a4]

def ofVal : Val → Option (_root_.Effect4.Char.Implementation)
  | .ctor 0 [v0, v1, v2, v3, v4] =>
    match Canonical.ofVal (α := _root_.String) v0, Canonical.ofVal (α := _root_.String) v1,
        Canonical.ofVal (α := (_root_.List (_root_.Effect4.Store.Digest))) v2,
        Canonical.ofVal (α := _root_.String) v3, Canonical.ofVal (α := _root_.String) v4 with
    | some a0, some a1, some a2, some a3, some a4 => some ⟨a0, a1, a2, a3, a4⟩
    | _, _, _, _, _ => none
  | _ => none

theorem ofVal_toVal (a : _root_.Effect4.Char.Implementation) : ofVal (toVal a) = some a := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := a
  simp [toVal, ofVal, Canonical.ofVal_toVal]

theorem ofVal_exact {v : Val} {a : _root_.Effect4.Char.Implementation} (h : ofVal v = some a) :
    v = toVal a := by
  unfold ofVal at h
  split at h
  · next v0 v1 v2 v3 v4 =>
    split at h
    · next b0 b1 b2 b3 b4 h0 h1 h2 h3 h4 =>
      injection h with h
      subst h
      simp only [toVal]
      rw [Canonical.ofVal_exact h0, Canonical.ofVal_exact h1, Canonical.ofVal_exact h2,
        Canonical.ofVal_exact h3, Canonical.ofVal_exact h4]
    · exact nomatch h
  · exact nomatch h

theorem lift_String (x : _root_.String) :
    acceptsIn shapeDoc.defs (shape _root_.String).root (Canonical.toVal x) = true :=
  acceptsIn_mono_of_subset (fun _ hp => mem_append_of_left (hp))
    _ _ (Canonical.fits x)
theorem lift_ListDigest (x : (_root_.List (_root_.Effect4.Store.Digest))) :
    acceptsIn shapeDoc.defs (shape (_root_.List (_root_.Effect4.Store.Digest))).root
      (Canonical.toVal x) = true :=
  acceptsIn_mono_of_subset (fun _ hp => mem_append_of_right (hp))
    _ _ (Canonical.fits x)

theorem fits (a : _root_.Effect4.Char.Implementation) : shapeDoc.accepts (toVal a) = true := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := a
  apply accepts_struct
  exact
    (acceptsFields_cons _ _ _ _ _ _ (lift_String a0)
      (acceptsFields_cons _ _ _ _ _ _ (lift_String a1)
        (acceptsFields_cons _ _ _ _ _ _ (lift_ListDigest a2)
          (acceptsFields_cons _ _ _ _ _ _ (lift_String a3)
            (acceptsFields_cons _ _ _ _ _ _ (lift_String a4) (acceptsFields_nil _))))))

instance instCanonical : Canonical (_root_.Effect4.Char.Implementation) :=
  ⟨shapeDoc, toVal, ofVal, ofVal_toVal, ofVal_exact, fits⟩

/-- Every node carrying an `Implementation` files under kind `source`. -/
instance instContent : Content (_root_.Effect4.Char.Implementation) := ⟨.source⟩

end CharImplementationC

namespace CharReceiptC

def shapeDoc : ShapeDoc :=
  ⟨.struct "Receipt" [("obligation", (shape _root_.String).root),
     ("vector", (shape _root_.Effect4.Store.AnyRef).root),
     ("pin", (shape (_root_.Effect4.Store.Ref (_root_.Effect4.Char.Implementation))).root),
     ("holds", (shape _root_.Bool).root), ("detail", (shape _root_.String).root)],
   (shape _root_.String).defs ++ (shape _root_.Effect4.Store.AnyRef).defs ++
     (shape (_root_.Effect4.Store.Ref (_root_.Effect4.Char.Implementation))).defs ++
     (shape _root_.Bool).defs⟩

def toVal : _root_.Effect4.Char.Receipt → Val
  | .mk a0 a1 a2 a3 a4 => .ctor 0 [Canonical.toVal a0, Canonical.toVal a1, Canonical.toVal a2,
      Canonical.toVal a3, Canonical.toVal a4]

def ofVal : Val → Option (_root_.Effect4.Char.Receipt)
  | .ctor 0 [v0, v1, v2, v3, v4] =>
    match Canonical.ofVal (α := _root_.String) v0,
        Canonical.ofVal (α := _root_.Effect4.Store.AnyRef) v1,
        Canonical.ofVal (α := (_root_.Effect4.Store.Ref (_root_.Effect4.Char.Implementation))) v2,
        Canonical.ofVal (α := _root_.Bool) v3, Canonical.ofVal (α := _root_.String) v4 with
    | some a0, some a1, some a2, some a3, some a4 => some ⟨a0, a1, a2, a3, a4⟩
    | _, _, _, _, _ => none
  | _ => none

theorem ofVal_toVal (a : _root_.Effect4.Char.Receipt) : ofVal (toVal a) = some a := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := a
  simp [toVal, ofVal, Canonical.ofVal_toVal]

theorem ofVal_exact {v : Val} {a : _root_.Effect4.Char.Receipt} (h : ofVal v = some a) :
    v = toVal a := by
  unfold ofVal at h
  split at h
  · next v0 v1 v2 v3 v4 =>
    split at h
    · next b0 b1 b2 b3 b4 h0 h1 h2 h3 h4 =>
      injection h with h
      subst h
      simp only [toVal]
      rw [Canonical.ofVal_exact h0, Canonical.ofVal_exact h1, Canonical.ofVal_exact h2,
        Canonical.ofVal_exact h3, Canonical.ofVal_exact h4]
    · exact nomatch h
  · exact nomatch h

theorem lift_String (x : _root_.String) :
    acceptsIn shapeDoc.defs (shape _root_.String).root (Canonical.toVal x) = true :=
  acceptsIn_mono_of_subset
    (fun _ hp => mem_append_of_left (mem_append_of_left (mem_append_of_left (hp))))
    _ _ (Canonical.fits x)
theorem lift_AnyRef (x : _root_.Effect4.Store.AnyRef) :
    acceptsIn shapeDoc.defs (shape _root_.Effect4.Store.AnyRef).root (Canonical.toVal x) = true :=
  acceptsIn_mono_of_subset
    (fun _ hp => mem_append_of_left (mem_append_of_left (mem_append_of_right (hp))))
    _ _ (Canonical.fits x)
theorem lift_RefImplementation
    (x : (_root_.Effect4.Store.Ref (_root_.Effect4.Char.Implementation))) :
    acceptsIn shapeDoc.defs
      (shape (_root_.Effect4.Store.Ref (_root_.Effect4.Char.Implementation))).root
      (Canonical.toVal x) = true :=
  acceptsIn_mono_of_subset (fun _ hp => mem_append_of_left (mem_append_of_right (hp)))
    _ _ (Canonical.fits x)
theorem lift_Bool (x : _root_.Bool) :
    acceptsIn shapeDoc.defs (shape _root_.Bool).root (Canonical.toVal x) = true :=
  acceptsIn_mono_of_subset (fun _ hp => mem_append_of_right (hp))
    _ _ (Canonical.fits x)

theorem fits (a : _root_.Effect4.Char.Receipt) : shapeDoc.accepts (toVal a) = true := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := a
  apply accepts_struct
  exact
    (acceptsFields_cons _ _ _ _ _ _ (lift_String a0)
      (acceptsFields_cons _ _ _ _ _ _ (lift_AnyRef a1)
        (acceptsFields_cons _ _ _ _ _ _ (lift_RefImplementation a2)
          (acceptsFields_cons _ _ _ _ _ _ (lift_Bool a3)
            (acceptsFields_cons _ _ _ _ _ _ (lift_String a4) (acceptsFields_nil _))))))

instance instCanonical : Canonical (_root_.Effect4.Char.Receipt) :=
  ⟨shapeDoc, toVal, ofVal, ofVal_toVal, ofVal_exact, fits⟩

/-- Every node carrying a `Receipt` files under kind `annotation`. -/
instance instContent : Content (_root_.Effect4.Char.Receipt) := ⟨.annotation⟩

end CharReceiptC

end Effect4.Store

namespace Effect4.Char

open Effect4.Store

/-- The gate: the fold of `holds` under `&&`. -/
def Receipts.verdict (rs : Receipts) : Bool := rs.elems.all Receipt.holds

/-- The failing receipts, for the diagnostic. -/
def Receipts.failures (rs : Receipts) : List Receipt := rs.elems.filter fun r => !r.holds

/-- **The receipt is the `replayed` rung's evidence.** A holding receipt projects to the pair
`Evidence.fixture` takes in `Char/Evidence.lean`: the vector's reference, and a reference to
the receipt itself, which carries the pin key inside it. A failing receipt is evidence of
nothing; it is a finding. A receipt never reaches `proved`. -/
def Receipt.asFixtureEvidence (r : Receipt) : Option (AnyRef × Ref Receipt) :=
  if r.holds then some (r.vector, address r) else none

/-- A failing receipt is evidence of nothing: the half of the projection that needs no store. -/
theorem Receipt.asFixtureEvidence_of_not_holds {r : Receipt} (h : r.holds = false) :
    r.asFixtureEvidence = none := by
  unfold Receipt.asFixtureEvidence
  rw [h]
  rfl

/-- A holding receipt names its own vector. -/
theorem Receipt.asFixtureEvidence_vector {r : Receipt} (h : r.holds = true) :
    (r.asFixtureEvidence).map Prod.fst = some r.vector := by
  unfold Receipt.asFixtureEvidence
  rw [h]
  rfl

/-! ## The laws, run -/

private def sampleImpl : Implementation :=
  { package := "effect", version := "4.0.0-rc.112", pins := [zeroDigest], driver := "runSync",
    host := "absent" }

private def sampleReceipt : Receipt :=
  { obligation := "replay", vector := ⟨.vector, zeroDigest⟩, pin := ⟨zeroDigest⟩, holds := true,
    detail := "one word" }

#guard Canonical.decode (α := Implementation) (Canonical.encode sampleImpl) = some sampleImpl
#guard Canonical.decode (α := Receipt) (Canonical.encode sampleReceipt) = some sampleReceipt
#guard Canonical.decode (α := Receipt) (Canonical.encode sampleReceipt ++ [0]) = none
#guard Canonical.decode (α := Receipt) (Canonical.encode sampleReceipt).dropLast = none
#guard (Canonical.shape Receipt).accepts (Canonical.toVal sampleReceipt)
#guard Content.kind Implementation = .source
#guard Content.kind Receipt = .annotation
#guard Content.kind Receipts = .vector
#guard (Receipts.verdict (GSet.ofList [sampleReceipt])) = true
#guard (Receipts.verdict (GSet.ofList [{ sampleReceipt with holds := false }])) = false
#guard (Receipts.failures (GSet.ofList [sampleReceipt])).length = 0
#guard ({ sampleReceipt with holds := false }).asFixtureEvidence = none

/-! ## Receipts -/

#print axioms Receipts.verdict
#print axioms Receipts.failures
#print axioms Receipt.asFixtureEvidence
#print axioms Receipt.asFixtureEvidence_of_not_holds
#print axioms Receipt.asFixtureEvidence_vector
#print axioms Effect4.Store.CharImplementationC.toVal
#print axioms Effect4.Store.CharImplementationC.ofVal
#print axioms Effect4.Store.CharImplementationC.ofVal_toVal
#print axioms Effect4.Store.CharImplementationC.ofVal_exact
#print axioms Effect4.Store.CharImplementationC.fits
#print axioms Effect4.Store.CharImplementationC.instCanonical
#print axioms Effect4.Store.CharImplementationC.instContent
#print axioms Effect4.Store.CharReceiptC.toVal
#print axioms Effect4.Store.CharReceiptC.ofVal
#print axioms Effect4.Store.CharReceiptC.ofVal_toVal
#print axioms Effect4.Store.CharReceiptC.ofVal_exact
#print axioms Effect4.Store.CharReceiptC.fits
#print axioms Effect4.Store.CharReceiptC.instCanonical
#print axioms Effect4.Store.CharReceiptC.instContent

end Effect4.Char
