import Effect4.Laws.Program.AnswerSlots.Actions

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: ordinary source entry excludes release destinations with unproved acquired answers.
Reach: selected acquisition paths in the existing source tree and actual child operations.
Limit: captured releases require their separate acquired-answer certificate.
Consumer: the stable typed source head and saved callback graph of the two crews.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots
open Effect4 Effect4.Machine Effect4.Program

/-- Ordinary entry excludes each selected acquisition's release child. -/
def Ordinary (acquisitions : List (List Nat)) (point : Point) : Prop :=
  ∀ path ∈ acquisitions, point.path ≠ path ++ [1]

/-- Every selected path identifies an actual acquisition head. -/
def AcquisitionSites (root : NativeEff) (acquisitions : List (List Nat)) : Prop :=
  ∀ path ∈ acquisitions, SourceScope.AcquisitionAt root path

/-- A non-release source edge cannot enter a selected release destination. -/
theorem child_ordinary (root : NativeEff) (acquisitions : List (List Nat)) (sites : AcquisitionSites root acquisitions)
    (point : Point) (index : Nat)
    (edge : index ≠ 1 ∨ ¬ SourceScope.AcquisitionAt root point.path) :
    Ordinary acquisitions (point.child index) := by
  intro path member selected
  have pieces := List.append_inj' selected (show [index].length = [1].length from rfl)
  have index_eq : index = 1 := List.cons.inj pieces.2 |>.1
  rcases edge with different | excluded
  · exact different index_eq
  · apply excluded
    rw [pieces.1]
    exact sites path member

/-- Appending a callback argument changes no source edge. -/
theorem childWith_ordinary (root : NativeEff) (acquisitions : List (List Nat))
    (sites : AcquisitionSites root acquisitions) (point : Point) (index : Nat) (value : Val)
    (edge : index ≠ 1 ∨ ¬ SourceScope.AcquisitionAt root point.path) :
    Ordinary acquisitions (point.childWith index value) :=
  child_ordinary root acquisitions sites point index edge

/-- An optional callback argument changes no source edge. -/
theorem childBind_ordinary (root : NativeEff) (acquisitions : List (List Nat))
    (sites : AcquisitionSites root acquisitions) (point : Point) (index : Nat) (value : Option Val)
    (edge : index ≠ 1 ∨ ¬ SourceScope.AcquisitionAt root point.path) :
    Ordinary acquisitions (point.childBind index value) := by
  cases value with
  | none => exact child_ordinary root acquisitions sites point index edge
  | some value => exact childWith_ordinary root acquisitions sites point index value edge

/-- A source constructor distinct from acquireRelease excludes an acquisition at its own path. -/
theorem not_acquisition (root : NativeEff) (point : Point) (effect : NativeEff)
    (found : Node.at_ (.eff root) point.path = some (.eff effect))
    (different : ∀ acquire release, effect ≠ .acquireRelease acquire release) :
    ¬ SourceScope.AcquisitionAt root point.path := by
  rintro ⟨acquire, release, acquisition⟩
  have same := found.symm.trans acquisition
  have effect_eq : effect = .acquireRelease acquire release := Node.eff.inj (Option.some.inj same)
  exact different acquire release effect_eq

/-- A real bind callback enters its ordinary continuation, rather than an acquisition's release. -/
theorem cont_ordinary (root : NativeEff) (acquisitions : List (List Nat))
    (sites : AcquisitionSites root acquisitions) (point : Point) (value : Val)
    (source : SourceScope.NameAt root (.cont point)) : Ordinary acquisitions (point.childWith 1 value) := by
  obtain ⟨_, first, rest, found⟩ := source
  apply childWith_ordinary root acquisitions sites point 1 value
  exact .inr (not_acquisition root point (.bind first rest) found (fun _ _ impossible => nomatch impossible))
end Effect4.Program.AnswerSlots
