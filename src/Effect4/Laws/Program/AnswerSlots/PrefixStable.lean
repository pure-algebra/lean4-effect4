import Effect4.Laws.Program.AnswerSlots.Interp
import Effect4.Laws.Program.AnswerSlots.Stable
import Effect4.Laws.Program.CodeClosure.Stable

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: Atomic.shop_stages and the numeric cleanup goals retain initialized root bindings.
Reach: the direct source fragment, all completed-fiber views and actual saved callback suffixes.
Limit: allocation, source ownership and command history remain separate premises.
Consumer: the common allocation-prefix adapter and its Atomic and Timeout instances.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots
open Effect4 Effect4.Machine Effect4.Program

/-- The broad stable class retains initialized bindings and admits every answer. -/
def prefixSpec (root : NativeEff) (table : RowTable) (bindings : List Val) : StableSpec where
  root := root
  table := table
  Kind := Unit
  rootKind := ()
  value _ _ := True
  code _ := CodeAt bindings
  success _ _ _ := trivial
  failure _ _ := trivial

/-- The compatibility Prefix model reads the same shared source graph. -/
theorem prefixModel_slots_eq (root : NativeEff) (table : RowTable) (bindings : List Val) (view) :
    (prefixSpec root table bindings).model view =
      (CodeClosure.Slots.prefixSpec root table (fun p => Prefix bindings p.env) (Prefix bindings)).model view := by
  unfold prefixSpec CodeClosure.Slots.prefixSpec StableSpec.model
  congr 1
  funext world kind program
  exact codeAt_fold bindings program

/-- Every exit representation contains no delayed source environment. -/
theorem prefix_ofExit (bindings : List Val) (exit : ExitV) : CodeAt bindings (Prim.ofExit exit) := by
  cases exit <;> trivial

/-- Actual value callbacks retain the current code and every pushed binding certificate. -/
theorem prefix_armA (root : NativeEff) (fragment : SourceScope.Fragment root)
    (bindings : List Val) (view) (table : RowTable)
    (frame : NCode) (value : Val) (provided : Option ExitV) (next : NCode) (pushed : List NCode)
    (owned : CodeAt bindings frame)
    (actual : frame.armA (interpAt root view table).toPrimInterp value provided = some (next, pushed)) :
    CodeAt bindings next ∧ ∀ code ∈ pushed, CodeAt bindings code := by
  rw [codeAt_fold] at owned
  have produced := CodeClosure.Slots.prefix_armA root fragment (fun p => Prefix bindings p.env) (Prefix bindings)
    (prefix_contract root bindings) (fun _ held _ => held) view table frame value provided next pushed owned actual
  constructor
  · rw [codeAt_fold]; exact produced.1
  · intro code member
    rw [codeAt_fold]
    exact produced.2 code member

/-- Actual cause callbacks retain the current code and every pushed binding certificate. -/
theorem prefix_armE (root : NativeEff) (fragment : SourceScope.Fragment root)
    (bindings : List Val) (view) (table : RowTable)
    (frame : NCode) (cause : CauseV) (provided : Option ExitV) (next : NCode) (pushed : List NCode)
    (owned : CodeAt bindings frame)
    (actual : frame.armE (interpAt root view table).toPrimInterp cause provided = some (next, pushed)) :
    CodeAt bindings next ∧ ∀ code ∈ pushed, CodeAt bindings code := by
  rw [codeAt_fold] at owned
  have produced := CodeClosure.Slots.prefix_armE root fragment (fun p => Prefix bindings p.env) (Prefix bindings)
    (prefix_contract root bindings) (fun _ held _ => held) view table frame cause provided next pushed owned actual
  constructor
  · rw [codeAt_fold]; exact produced.1
  · intro code member
    rw [codeAt_fold]
    exact produced.2 code member

/-- Native finalizer restoration adds no delayed source environment. -/
theorem prefix_finalizerCode (root : NativeEff) (bindings : List Val) (view) (table : RowTable)
    (exit : ExitV) (body : NCode) (owned : CodeAt bindings body) :
    CodeAt bindings (finalizerCode (interpAt root view table) exit body) := by
  rw [codeAt_fold] at owned ⊢
  exact CodeClosure.Slots.prefix_finalizerCode root (fun p => Prefix bindings p.env) (Prefix bindings)
    view table exit body owned

/-- The same binding certificate annotates saved code at every completed-fiber view. -/
def prefixEdge (bindings : List Val) (_ : Unit) (_ _ : Unit) : NCode → Prop := CodeAt bindings

/-- The compatibility saved edges read the same generated code annotation. -/
theorem prefixEdge_slots_eq (bindings : List Val) :
    prefixEdge bindings = CodeClosure.Slots.prefixEdge (fun p => Prefix bindings p.env) (Prefix bindings) := by
  funext world input output
  exact funext (codeAt_fold bindings)

/-- An actual saved suffix composes the same immutable binding certificate. -/
theorem prefix_path (bindings : List Val) (frames : List NCode)
    (owned : ∀ code ∈ frames, CodeAt bindings code) :
    Contracts.Path (prefixEdge bindings ()) () () frames := by
  induction frames with
  | nil => exact .nil ()
  | cons frame rest ih =>
    exact .cons (owned frame (.head _)) (ih (fun code member => owned code (.tail _ member)))

/-- Every actual callback view supplies the common saved-frame obligations. -/
theorem prefix_family (root : NativeEff) (fragment : SourceScope.Fragment root)
    (bindings : List Val) (table : RowTable) (view) :
    AnswerFlow.SavedFamily ((prefixSpec root table bindings).model view)
      (interpAt root view table).toPrimInterp (prefixEdge bindings) := by
  rw [prefixModel_slots_eq, prefixEdge_slots_eq]
  exact CodeClosure.Slots.prefix_family root fragment (fun p => Prefix bindings p.env) (Prefix bindings)
    (prefix_contract root bindings) (fun _ held _ => held) table view

/-- Every permitted current head consumes the same stable binding class. -/
theorem prefix_head (root : NativeEff) (fragment : SourceScope.Fragment root)
    (bindings : List Val) (table : RowTable) (view) (code : NCode) (owned : CodeAt bindings code) :
    AnswerFlow.HeadAt ((prefixSpec root table bindings).model view)
      (interpAt root view table).toPrimInterp (prefixEdge bindings) () () code := by
  rw [prefixModel_slots_eq, prefixEdge_slots_eq]
  rw [codeAt_fold] at owned
  exact CodeClosure.Slots.prefix_head root fragment (fun p => Prefix bindings p.env) (Prefix bindings)
    (prefix_contract root bindings) (fun _ held _ => held) table view code owned

/-- The common allocation adapter accepts the existing prefix graph at every actual view. -/
def prefixLaws (root : NativeEff) (fragment : SourceScope.Fragment root)
    (bindings : List Val) (table : RowTable) : StableLaws (prefixSpec root table bindings) where
  Edge := prefixEdge bindings
  family := prefix_family root fragment bindings table
  head view kind code owned := by
    cases kind
    exact prefix_head root fragment bindings table view code owned

end Effect4.Program.AnswerSlots
