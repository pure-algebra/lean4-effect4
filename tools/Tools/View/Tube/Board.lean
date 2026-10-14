import Init.Data.List.Lemmas

/-!
# Tools.View.Tube.Board

An observer of an existing state transition. Changes and markings remain caller types.
The conditional projection law requires agreement at every transition.
It supplies no event-only projection of store changes.
Placement: the tool question `view-board-projection-fold`, row 334 (3), R14 groundwork.
-/

namespace Tools.View.Tube.Board

variable {S C B Δ : Type}

/-- One transition and its observed change acting on the current marking. -/
def advance (step : S → C → S) (change : S → C → S → Δ) (act : B → Δ → B)
    (current : S × B) (command : C) : S × B :=
  let next := step current.1 command
  (next, act current.2 (change current.1 command next))

/-- The board observer folded over existing commands. -/
def fold (step : S → C → S) (change : S → C → S → Δ) (act : B → Δ → B)
    (current : S × B) (commands : List C) : S × B :=
  commands.foldl (advance step change act) current

/-- Command concatenation composes observer folds. Helper of `view-board-projection-fold`. -/
theorem fold_append (step : S → C → S) (change : S → C → S → Δ) (act : B → Δ → B)
    (current : S × B) (before after : List C) :
    fold step change act current (before ++ after) =
      fold step change act (fold step change act current before) after :=
  List.foldl_append

/-- If each change agrees with the projection, every finite command fold does too.
Tool invariant `view-board-projection-fold`. The transition premise remains open. -/
theorem fold_projection (step : S → C → S) (change : S → C → S → Δ) (act : B → Δ → B)
    (project : S → B)
    (agrees : ∀ state command, act (project state) (change state command (step state command)) =
      project (step state command))
    (state : S) (commands : List C) :
    fold step change act (state, project state) commands =
      (commands.foldl step state, project (commands.foldl step state)) := by
  induction commands generalizing state with
  | nil => rfl
  | cons command commands ih =>
    change fold step change act
      (step state command,
        act (project state) (change state command (step state command))) commands = _
    rw [agrees state command]
    exact ih (step state command)

end Tools.View.Tube.Board
