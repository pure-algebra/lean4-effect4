import Effect4.Laws.Program.FinalizerGeneratorPC
import Effect4.Laws.Program.FinalizerLayerBody
import Effect4.Laws.Program.CodeClosure.Callbacks

/-!
Concept: scope-lifetime-finalization R11.
Question: source annotations for `once_placed_outside_census`.
Consumer: the full native callback debit and its history invariant.
The generated code fold retains clear parameter frames, valid generator counters and excluded layer construction regions.
Stored programs reuse the existing closure at the parameter-frame predicate.
These annotations establish no source-use bound or progress.
-/
set_option autoImplicit false
namespace Effect4.Program.FinalizerSource
open Effect4 Effect4.Machine Effect4.Program

abbrev PointAt (q : List Nat) (point : Point) : Prop := ParamsClear q point.params

/-- Layer construction regions carry the exclusion established at their actual layer leaf. -/
@[reducible] def RegionAt (q : List Nat) : Region → Prop
  | .program point | .build point _ _ | .buildAdding point _ _ => PointAt q point
  | .construct point _ => PointAt q point ∧ SourceScope.Opportunities.below q point.path = 0

/-- Full native names add generator and layer annotations to the existing stored-source slots. -/
@[reducible] def NameAt (q : List Nat) : EffName → Prop
  | .gen point pc _ => PointAt q point ∧ FinalizerGenerator.Counter pc
  | .provideLayerWith point | .provideLayerBody point
  | .buildWithScopeFromContext point _ | .withMemoMapThen point _ | .fromBuildThen point _
  | .memoize point _ _ | .buildIntoLayerScope point _ _ | .thenBuildInto point _ _
  | .freshThen point _ | .provideThen point _ _ _ | .mergeChildren point _
  | .mergeForkOne point _ _ _ _ | .mergeForkNext point _ _ _ _ | .mergeAllChildren point _
  | .mergeAllForkOne point _ _ _ _ | .mergeAllForkNext point _ _ _ _ => PointAt q point
  | .provideMask _ region | .updateThen _ region _ | .bodyThen region _ _ => RegionAt q region
  | callback => CodeClosure.Slots.NameAt (PointAt q) (fun _ => True) callback

/-- Full native thunks retain the same source annotations through layer suspensions. -/
@[reducible] def ThunkAt (q : List Nat) : EffThunk → Prop
  | .memoLookup point _ _ | .forkLayer point _ _ => PointAt q point
  | .provideMasked _ region _ | .restoreRegion region _ => RegionAt q region
  | suspended => CodeClosure.Slots.ThunkAt (PointAt q) (fun _ => True) suspended

abbrev CodeAt (q : List Nat) := CodeClosure.Code (NameAt q) (ThunkAt q)

/-- A direct region is an instance of the full region annotation. -/
theorem direct_region (q : List Nat) (region : Region)
    (held : CodeClosure.Slots.RegionAt (PointAt q) (fun _ => True) region) : RegionAt q region := by
  cases region with
  | program point => exact held
  | build | buildAdding | construct => exact held.elim

/-- The old direct callback annotation embeds without another code traversal. -/
theorem direct_name (q : List Nat) (callback : EffName)
    (held : CodeClosure.Slots.NameAt (PointAt q) (fun _ => True) callback) : NameAt q callback := by
  cases callback
  case gen | provideLayerWith | provideLayerBody | buildWithScopeFromContext | withMemoMapThen
    | fromBuildThen | memoize | buildIntoLayerScope | thenBuildInto | freshThen | provideThen
    | mergeChildren | mergeForkOne | mergeForkNext | mergeAllChildren | mergeAllForkOne
    | mergeAllForkNext => exact held.elim
  case provideMask | updateThen | bodyThen => exact direct_region q _ held
  all_goals exact held

/-- The old direct thunk annotation embeds into the full source slots. -/
theorem direct_thunk (q : List Nat) (suspended : EffThunk)
    (held : CodeClosure.Slots.ThunkAt (PointAt q) (fun _ => True) suspended) : ThunkAt q suspended := by
  cases suspended
  case memoLookup | forkLayer => exact held.elim
  case provideMasked | restoreRegion => exact direct_region q _ held
  all_goals exact held

/-- Stored-code producers use their existing closure proof at clear parameter frames. -/
theorem direct_code (q : List Nat) (code : NCode)
    (held : CodeClosure.Slots.CodeAt (PointAt q) (fun _ => True) code) : CodeAt q code :=
  CodeClosure.code_mono (direct_name q) (direct_thunk q) code held

/-- Ordinary source point changes preserve the existing parameter-frame list. -/
theorem point_same (q : List Nat) (first second : Point)
    (same : second.params = first.params) (held : PointAt q first) : PointAt q second := by
  change ParamsClear q second.params
  rw [same]
  exact held

/-- The existing direct closure instance supplies the compiler's unrestricted source leaves. -/
theorem pointTransport (q : List Nat) : CodeClosure.Slots.Transport (PointAt q) (fun _ => True) where
  environment := fun _ => trivial
  child := fun held _ => held
  childWith := fun held _ _ => held
  capture := fun held _ _ => held

/-- Compiler closure is shared; only its name and thunk conclusions widen. -/
theorem compile_at (root : NativeEff) (q : List Nat) (effect : NativeEff) (point : Point)
    (found : Node.at_ (.eff root) point.path = some (.eff effect)) (held : PointAt q point) :
    CodeAt q (compileEff effect point) :=
  direct_code q _ (CodeClosure.compile_closure
    (CodeClosure.Slots.compile_contract root (PointAt q) (fun _ => True) (pointTransport q))
    effect point found held)

/-- Resolution keeps the same parameter-frame annotation at its actual source node. -/
theorem resolve_at (root : NativeEff) (q : List Nat) (point : Point) (held : PointAt q point) :
    CodeAt q (resolve root point) := by
  unfold resolve
  split
  · exact compile_at root q _ point ‹_› held
  · trivial

/-- Actual foreign finalizers reuse the existing stored-program closure. -/
theorem finalizer_at (q : List Nat) (fin : FinName) (exit : ExitV)
    (held : CodeClosure.Slots.FinAt (PointAt q) (fun _ => True) fin) :
    CodeAt q (embed (finProgram fin exit)) :=
  direct_code q _ (CodeClosure.Slots.finProgram_at (PointAt q) (fun _ => True) fin exit held)

/-- Actual stored programs reuse the existing recursive closure. -/
theorem stored_at (q : List Nat) (program : ProgName)
    (held : CodeClosure.Slots.ProgAt (PointAt q) (fun _ => True) program) :
    CodeAt q (embed (progOf program)) :=
  direct_code q _ (CodeClosure.Slots.progOf_at (PointAt q) (fun _ => True) program held)

end Effect4.Program.FinalizerSource
