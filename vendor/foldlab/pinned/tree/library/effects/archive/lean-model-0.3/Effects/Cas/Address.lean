import Effects.Cas.Codec

/-!
# The address function

The address FUNCTION stays abstract: `H : Bytes → Addr` is a section
variable over an arbitrary codomain — never a concrete digest, and never
injective by construction anywhere a proof could lean on it. The model
never instantiates `H`; the concrete digest is an injected adapter on the
implementation side.

Every theorem sits at its declared level of the hash-hypothesis lattice
(the CAS-003 discipline):

- **Level 0 — no premise on `H`.** The address is a function of the
  canonical byte representation alone: equal admitted nodes deduplicate to
  one address, and equal addresses are characterized as node equality or an
  explicit `H`-collision pair (the surveyed ideal-or-collision-witness
  disjunct).
- **Level 1 — reflection only under the named premise.** Address equality
  reflects node equality only given `hInj : Function.Injective H`.
- **Level 2 — empty, and forced to be.** No theorem assumes collision
  resistance. The closing `example` exhibits a degenerate address function
  under which two distinct admitted nodes share an address, so
  unconditional reflection is unprovable at this abstraction.
-/

namespace Effects.Cas

section AddressFunction

variable {Addr : Type u} (H : Bytes → Addr)

/-- The address of an admitted node: the abstract hash of the canonical
pre-image — the node's one byte representation. -/
def addr (n : AdmittedNode) : Addr := H (encodeAdmitted n)

/-! ## Level 0 — no premise on `H` -/

/-- Deduplication, node level: the address is a function of the node, so
equal admitted nodes carry equal addresses. -/
theorem addr_congr {n m : AdmittedNode} (h : n = m) :
    addr H n = addr H m :=
  congrArg (addr H) h

/-- Equal-encoding deduplication: equal canonical bytes give equal
addresses. -/
theorem addr_eq_of_encode_eq {n m : AdmittedNode}
    (h : encodeAdmitted n = encodeAdmitted m) : addr H n = addr H m :=
  congrArg H h

/-- Collision characterization: equal addresses mean equal nodes, or an
explicit collision — two distinct canonical byte strings that `H` maps to
one address. The disjunction needs no premise on `H`; discharging its right
branch is exactly what would require one. -/
theorem addr_eq_or_collision {n m : AdmittedNode}
    (h : addr H n = addr H m) :
    n = m ∨
      (encodeAdmitted n ≠ encodeAdmitted m ∧
        H (encodeAdmitted n) = H (encodeAdmitted m)) := by
  by_cases henc : encodeAdmitted n = encodeAdmitted m
  · exact Or.inl (encodeAdmitted_inj henc)
  · exact Or.inr ⟨henc, h⟩

/-! ## Level 1 — reflection under the named injectivity premise -/

/-- Address equality reflects node equality — only here, only under
`hInj`. -/
theorem addr_inj (hInj : Function.Injective H) {n m : AdmittedNode}
    (h : addr H n = addr H m) : n = m :=
  encodeAdmitted_inj (hInj h)

end AddressFunction

/-! ## Level 2 — empty by design -/

/-- Why Level 2 stays empty: under a degenerate address function, two
distinct admitted nodes share an address, so address equality cannot
unconditionally reflect node equality. Reflection genuinely requires
Level 1's named premise; no theorem in the model assumes collision
resistance. -/
example :
    ∃ n m : AdmittedNode,
      n ≠ m ∧ addr (fun _ => ()) n = addr (fun _ => ()) m :=
  ⟨⟨⟨0, 0, [], []⟩, by decide⟩, ⟨⟨1, 0, [], []⟩, by decide⟩,
    by decide, rfl⟩

end Effects.Cas
