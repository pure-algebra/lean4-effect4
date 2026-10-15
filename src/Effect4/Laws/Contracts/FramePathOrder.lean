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
/-- A relation closed under identity and composition reads the endpoints of the existing path.
Consumer: Timeout's one saved path transports its owner count and pending-class validity together. -/
theorem endpoints (Relation : Object → Object → Prop)
    (identity : ∀ object, Relation object object)
    (compose : ∀ first middle last, Relation first middle → Relation middle last → Relation first last)
    (edge : ∀ first last frame, Edge first last frame → Relation first last)
    {input output : Object} {frames : List Frame} (path : Path Edge input output frames) :
    Relation input output := by
  induction path with
  | nil object => exact identity object
  | @cons first middle last frame rest head tail ih =>
    exact compose first middle last (edge first middle frame head) ih

/-- An actual path from an early endpoint to a later endpoint contains an actual crossing edge.
Consumer: Timeout's uniform source certificate identifies that edge as its authored finalizer.
This reads the existing path and establishes no source classification by itself. -/
theorem crossing_member (grade : Object → Nat) (ceiling : Nat)
    {input output : Object} {frames : List Frame} (path : Path Edge input output frames)
    (early : grade input ≤ ceiling) (later : ceiling < grade output) :
    ∃ first last frame, frame ∈ frames ∧ Edge first last frame ∧
      grade first ≤ ceiling ∧ ceiling < grade last := by
  revert early later
  induction path with
  | nil kind =>
    intro early later
    exact False.elim (Nat.not_le_of_gt later early)
  | @cons first middle last frame rest head tail ih =>
    intro early later
    by_cases crossed : ceiling < grade middle
    · exact ⟨first, middle, frame, List.mem_cons_self, head, early, crossed⟩
    · obtain ⟨before, after, actual, member, edge, low, high⟩ := ih (Nat.le_of_not_gt crossed) later
      exact ⟨before, after, actual, List.mem_cons_of_mem frame member, edge, low, high⟩

end Effect4.Contracts.Path
