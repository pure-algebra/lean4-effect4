import Effect4.Api.Author

/-! Probe: the row-name projection has one consumer, `Built.positionOf`, and that consumer is
`List.findIdx?` on the rows. The projection is a `zipIdx` spelled for a `find?`. -/

set_option autoImplicit false
namespace Probe
open Effect4 Effect4.Program Effect4.Api

theorem find_zipIdx_eq_findIdx? (s : String) : ∀ (rows : List Row) (n : Nat),
    ((rows.zipIdx n).find? (fun e => e.1.spelling == s)).map Prod.snd =
      (rows.findIdx? (·.spelling == s)).map (· + n)
  | [], _ => rfl
  | r :: rest, n => by
    simp only [List.zipIdx_cons, List.find?_cons, List.findIdx?_cons]
    cases r.spelling == s with
    | true => simp
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [find_zipIdx_eq_findIdx? s rest (n + 1), Option.map_map]
      congr 1
      funext i
      show i + (n + 1) = i + 1 + n
      omega

/-- The one consumer, written without the projection. -/
theorem positionOf_eq (b : Built) (s : String) :
    b.positionOf s = b.app.rows.findIdx? (·.spelling == s) := by
  unfold Built.positionOf Built.rowNames SigApp.rowNames
  rw [List.find?_map, Option.map_map]
  show ((b.app.rows.zipIdx 0).find? (fun e => e.1.spelling == s)).map Prod.snd = _
  rw [find_zipIdx_eq_findIdx? s b.app.rows 0]
  generalize b.app.rows.findIdx? (·.spelling == s) = o
  cases o <;> rfl

end Probe
