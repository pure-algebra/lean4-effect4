/-
ShapeWitness.lean -- `ShapeDoc.document` is not injective: a sum case's wire tag is not rendered.

A research probe (seat rocq-cas, 2026-10-17), outside every build. Run from the repository root:
  lake env lean docs/research/2026-10-17-seat-rocq-cas/ShapeWitness.lean
`render` (src/Effect4/Schema/OfShape.lean) writes a nullary sum as the literal strings of its case
names, and a sum with fields as tagged structs of names and fields; neither writes the tag. So two
shapes that differ only in a tag have one document, one schema node, and one `specOf`.
-/
import Effect4.Schema.OfShape
open Effect4.Store

/-- Two nullary sums that differ only in a case's wire tag. -/
def tagged0 : ShapeDoc := ⟨.sum "S" [("a", 0, []), ("b", 1, [])], []⟩
def tagged2 : ShapeDoc := ⟨.sum "S" [("a", 0, []), ("b", 2, [])], []⟩
/-- Two sums with fields that differ only in a case's wire tag. -/
def fields0 : ShapeDoc := ⟨.sum "T" [("a", 0, [("x", .nat)]), ("b", 1, [])], []⟩
def fields5 : ShapeDoc := ⟨.sum "T" [("a", 5, [("x", .nat)]), ("b", 1, [])], []⟩

theorem tag_lost_nullary : tagged0.document = tagged2.document := rfl
theorem tag_lost_fields : fields0.document = fields5.document := rfl

theorem tagged_ne : tagged0 ≠ tagged2 := by
  intro h
  have h1 := (ShapeDoc.mk.inj h).1
  have h2 := (Shape.sum.inj h1).2
  have h3 := (List.cons.inj (List.cons.inj h2).2).1
  have h4 := (Prod.mk.inj (Prod.mk.inj h3).2).1
  exact absurd h4 (by decide)

/-- `ShapeDoc.document` is not injective. -/
theorem document_not_injective : ¬ Function.Injective ShapeDoc.document :=
  fun hinj => tagged_ne (hinj tag_lost_nullary)
