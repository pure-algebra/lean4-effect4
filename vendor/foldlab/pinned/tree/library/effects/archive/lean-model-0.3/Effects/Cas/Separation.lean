import Effects.Cas.Codec

/-!
# Domain separation of the leading bytes

The ratified pre-image shape leads with the scheme-version byte and the
kind-tag byte precisely so that separation is a structural fact about the
first two byte positions: nodes of distinct version never share a byte
representation, and nodes of distinct kind tag never share a byte
representation. Both facts are cons-injection arguments.

Two deliberate absences of premises:

- **No well-formedness premise.** Encoder injectivity (`encodeNode_injOn`)
  holds on the well-formed domain; separation of the leading bytes holds for
  ALL nodes, well-formed or not, because injection on the first two cons
  cells never inspects the body.
- **No same-version premise on tag separation.** The surveyed shape is
  "same version and distinct tag bytes give disjoint encodings"; here the
  tag byte occupies the second position for every version, so distinct tags
  separate encodings unconditionally, which subsumes the surveyed shape.

Everything here is hash-lattice Level 0: no premise about any hash appears.
The extraction forms (`version_eq_of_encodeNode_eq`, `tag_eq_of_encodeNode_eq`)
are the primitives; the separation theorems are their contrapositives, and
the admitted-surface corollaries restate them at the carrier the CODEC
schema instance quantifies over.
-/

namespace Effects.Cas

/-! ## Extraction: encoding equality pins the leading bytes -/

theorem version_eq_of_encodeNode_eq {n m : Node}
    (h : encodeNode n = encodeNode m) : n.version = m.version := by
  simp only [encodeNode, List.cons.injEq] at h
  exact h.1

theorem tag_eq_of_encodeNode_eq {n m : Node}
    (h : encodeNode n = encodeNode m) : n.tag = m.tag := by
  simp only [encodeNode, List.cons.injEq] at h
  exact h.2.1

/-! ## Separation: distinct leading bytes give disjoint encodings -/

theorem encodeNode_ne_of_version_ne {n m : Node}
    (h : n.version ≠ m.version) : encodeNode n ≠ encodeNode m :=
  fun he => h (version_eq_of_encodeNode_eq he)

theorem encodeNode_ne_of_tag_ne {n m : Node}
    (h : n.tag ≠ m.tag) : encodeNode n ≠ encodeNode m :=
  fun he => h (tag_eq_of_encodeNode_eq he)

/-! ## The admitted-node surface -/

theorem encodeAdmitted_ne_of_version_ne {n m : AdmittedNode}
    (h : n.val.version ≠ m.val.version) :
    encodeAdmitted n ≠ encodeAdmitted m :=
  encodeNode_ne_of_version_ne h

theorem encodeAdmitted_ne_of_tag_ne {n m : AdmittedNode}
    (h : n.val.tag ≠ m.val.tag) :
    encodeAdmitted n ≠ encodeAdmitted m :=
  encodeNode_ne_of_tag_ne h

end Effects.Cas
