/-- Part one: an interrupt reason carries neither excluded defect. -/
theorem noShapeDefect_of_interrupts (ty : EffTy) (cause : CauseV)
    (interrupts : ∀ reason ∈ cause.reasons, reason.tag = .interrupt) :
    NoShapeDefect ty (.failure cause) := by
  intro reason member
  have tag := interrupts reason member
  cases reason with
  | fail _ _ => trivial
  | die _ _ => cases tag
  | interrupt _ _ => trivial

/-- Removing Fail reasons does not introduce a shape defect. -/
theorem noShapeDefect_stripFail (ty : EffTy) (cause : CauseV)
    (shape : NoShapeDefect ty (.failure cause)) :
    NoShapeDefect ty (.failure cause.stripFail) := by
  intro reason member
  exact shape reason ((Cause.mem_stripFail reason cause).mp member).1

/-- Combine contains only reasons from its two inputs. -/
theorem noShapeDefect_combine (ty : EffTy) (left right : CauseV)
    (leftShape : NoShapeDefect ty (.failure left))
    (rightShape : NoShapeDefect ty (.failure right)) :
    NoShapeDefect ty (.failure (Cause.combine left right)) := by
  intro reason member
  rcases (Cause.mem_combine reason left right).mp member with fromLeft | fromRight
  · exact leftShape reason fromLeft
  · exact rightShape reason fromRight

/-- Sanitization strips Fail reasons and combines the remaining original reasons with
recorded interruption reasons; exclusion is required of both inputs. -/
theorem noShapeDefect_sanitize (ty : EffTy) (cause interrupted : CauseV)
    (shape : NoShapeDefect ty (.failure cause))
    (interruptShape : NoShapeDefect ty (.failure interrupted)) :
    NoShapeDefect ty (.failure (Cause.sanitize cause interrupted)) :=
  noShapeDefect_combine ty cause.stripFail interrupted
    (noShapeDefect_stripFail ty cause shape) interruptShape

