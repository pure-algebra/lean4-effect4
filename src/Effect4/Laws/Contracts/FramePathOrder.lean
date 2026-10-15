import Effect4.Laws.Contracts.FramePath

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Consumer: Atomic and Timeout actual finalizer custody on ordered saved frames.
An increasing endpoint grade bounds the source endpoint of each actual saved frame.
These local path facts supply no source grade or finalizer custody producer.
-/
set_option autoImplicit false
namespace Effect4.Contracts.Path
universe u v
variable {Object : Type u} {Frame : Type v}
variable {Edge : Object → Object → Frame → Prop}

/-- Each actual saved member starts no earlier than the current answer endpoint. -/
theorem member_grade (grade : Object → Nat)
    (increases : ∀ input output frame, Edge input output frame → grade input ≤ grade output)
    {input output : Object} {frames : List Frame} (path : Path Edge input output frames) :
    ∀ frame ∈ frames, ∃ first last, Edge first last frame ∧ grade input ≤ grade first := by
  induction path with
  | nil kind => intro frame member; exact (List.not_mem_nil member).elim
  | @cons first middle last frame rest head tail ih =>
    intro actual member
    rcases List.mem_cons.mp member with same | member
    · subst actual
      exact ⟨first, middle, head, Nat.le_refl _⟩
    · obtain ⟨before, after, owned, bound⟩ := ih actual member
      exact ⟨before, after, owned, Nat.le_trans (increases _ _ _ head) bound⟩

/-- An actual low-domain finalizer bounds the current answer grade on the same saved path. -/
theorem grade_le_of_member (grade : Object → Nat)
    (increases : ∀ input output frame, Edge input output frame → grade input ≤ grade output)
    {input output : Object} {frames : List Frame} (path : Path Edge input output frames)
    (frame : Frame) (ceiling : Nat)
    (low : ∀ first last, Edge first last frame → grade first ≤ ceiling) (member : frame ∈ frames) :
    grade input ≤ ceiling := by
  obtain ⟨first, last, owned, bound⟩ := member_grade grade increases path frame member
  exact Nat.le_trans bound (low first last owned)

/-- A later answer grade excludes an earlier-domain authored finalizer. -/
theorem not_mem_of_grade (grade : Object → Nat)
    (increases : ∀ input output frame, Edge input output frame → grade input ≤ grade output)
    {input output : Object} {frames : List Frame} (path : Path Edge input output frames)
    (frame : Frame) (ceiling : Nat)
    (low : ∀ first last, Edge first last frame → grade first ≤ ceiling) (later : ceiling < grade input) :
    frame ∉ frames :=
  fun member => Nat.not_le_of_gt later (grade_le_of_member grade increases path frame ceiling low member)
end Effect4.Contracts.Path
