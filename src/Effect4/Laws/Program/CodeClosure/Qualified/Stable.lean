import Effect4.Laws.Program.CodeClosure.Qualified.Interp
import Effect4.Laws.Program.CodeClosure.Family

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: supplied source annotations instantiate the common saved-frame producer.
Consumers: the Prefix stable instance and both Timeout numeric endpoint producers.
Reach: the direct source fragment, actual callback views, and actual saved suffixes.
The instance supplies no initialization, numeric effects, or command history.
-/
set_option autoImplicit false
namespace Effect4.Program.CodeClosure.Qualified
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.AnswerSlots

/-- The direct source instance uses the same annotation in both callback roles. -/
abbrev prefixSpec (root : NativeEff) (table : RowTable) (point : Point → Prop)
    (env : List Val → Prop) (writes : SyncOp → Prop) :=
  Family.sourceSpec root table (NameAt point env writes) (NameAt point env writes) (ThunkAt point env writes)

/-- Exit representations retain every source annotation. -/
theorem prefix_ofExit (point : Point → Prop) (env : List Val → Prop) (writes : SyncOp → Prop)
    (exit : ExitV) : CodeAt point env writes (Prim.ofExit exit) :=
  Family.source_ofExit (NameAt point env writes) (NameAt point env writes) (ThunkAt point env writes) exit

/-- Native finalizer restoration adds no delayed source environment. -/
theorem prefix_finalizerCode (root : NativeEff) (point : Point → Prop) (env : List Val → Prop)
    (writes : SyncOp → Prop) (view) (table : RowTable) (exit : ExitV) (body : NCode)
    (owned : CodeAt point env writes body) :
    CodeAt point env writes (finalizerCode (interpAt root view table) exit body) := by
  cases exit with
  | success value => exact ⟨owned, trivial⟩
  | failure cause => exact ⟨⟨owned, trivial⟩, trivial⟩

/-- Existing direct-source callback facts fill the common interpreter contract. -/
theorem prefixHooks (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) (writes : SyncOp → Prop)
    (contract : Contract root point env writes) (stable : ViewStable point) (table : RowTable) :
    Family.Hooks root table (NameAt point env writes) (NameAt point env writes) (ThunkAt point env writes) where
  value := fun view => interp_contA_at root fragment point env writes contract stable view table
  bothValue := fun view => interp_contA_at root fragment point env writes contract stable view table
  cause := fun view => interp_contE_at root fragment point env writes contract stable view table
  suspend := fun view => interp_suspend_at root fragment point env writes contract stable view table
  iterator := fun view => interp_iter_at root point env writes view table
  loopEnter := fun view => interp_loopEnter_at root fragment point env writes contract stable view table
  loopResume := fun view => interp_loopResume_at root fragment point env writes contract stable view table
  cancel := fun view => interp_cancel_at root point env writes view table
  finalizer := fun view => interp_fin_at root fragment point env writes contract stable view table
  restore := fun view exit body owned => prefix_finalizerCode root point env writes view table exit body owned

/-- Actual value arms use the common generated-code producer. -/
theorem prefix_armA (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) (writes : SyncOp → Prop)
    (contract : Contract root point env writes) (stable : ViewStable point) (view) (table : RowTable)
    (frame : NCode) (value : Val) (provided : Option ExitV) (next : NCode) (pushed : List NCode)
    (owned : CodeAt point env writes frame)
    (actual : frame.armA (interpAt root view table).toPrimInterp value provided = some (next, pushed)) :
    CodeAt point env writes next ∧ ∀ code ∈ pushed, CodeAt point env writes code :=
  Family.source_armA root table _ _ _ (prefixHooks root fragment point env writes contract stable table)
    view frame value provided next pushed owned actual

/-- Actual cause arms use the same generated-code producer. -/
theorem prefix_armE (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) (writes : SyncOp → Prop)
    (contract : Contract root point env writes) (stable : ViewStable point) (view) (table : RowTable)
    (frame : NCode) (cause : CauseV) (provided : Option ExitV) (next : NCode) (pushed : List NCode)
    (owned : CodeAt point env writes frame)
    (actual : frame.armE (interpAt root view table).toPrimInterp cause provided = some (next, pushed)) :
    CodeAt point env writes next ∧ ∀ code ∈ pushed, CodeAt point env writes code :=
  Family.source_armE root table _ _ _ (prefixHooks root fragment point env writes contract stable table)
    view frame cause provided next pushed owned actual

abbrev prefixEdge (point : Point → Prop) (env : List Val → Prop) (writes : SyncOp → Prop) :=
  Family.sourceEdge (NameAt point env writes) (NameAt point env writes) (ThunkAt point env writes)

abbrev prefix_path (point : Point → Prop) (env : List Val → Prop) (writes : SyncOp → Prop) :=
  Family.source_path (NameAt point env writes) (NameAt point env writes) (ThunkAt point env writes)

abbrev prefix_path_owned (point : Point → Prop) (env : List Val → Prop) (writes : SyncOp → Prop) :=
  @Family.source_path_owned (NameAt point env writes) (NameAt point env writes) (ThunkAt point env writes)

/-- Every actual callback view supplies the common saved-family instance. -/
theorem prefix_family (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) (writes : SyncOp → Prop)
    (contract : Contract root point env writes) (stable : ViewStable point) (table : RowTable) (view) :
    AnswerFlow.SavedFamily ((prefixSpec root table point env writes).model view)
      (interpAt root view table).toPrimInterp (prefixEdge point env writes) :=
  Family.source_family root table _ _ _ (prefixHooks root fragment point env writes contract stable table) view

/-- Every current constructor uses the common head producer. -/
theorem prefix_head (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) (writes : SyncOp → Prop)
    (contract : Contract root point env writes) (stable : ViewStable point) (table : RowTable) (view)
    (code : NCode) (owned : CodeAt point env writes code) :
    AnswerFlow.HeadAt ((prefixSpec root table point env writes).model view)
      (interpAt root view table).toPrimInterp (prefixEdge point env writes) () () code :=
  Family.source_head root table _ _ _ (prefixHooks root fragment point env writes contract stable table) view code owned

/-- The direct source instance retains its existing public stable interface. -/
def prefixLaws (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) (writes : SyncOp → Prop)
    (contract : Contract root point env writes) (stable : ViewStable point) (table : RowTable) :
    StableLaws (prefixSpec root table point env writes) :=
  Family.sourceLaws root table _ _ _ (prefixHooks root fragment point env writes contract stable table)

end Effect4.Program.CodeClosure.Qualified
