import Effect4.Laws.Program.AnswerSlots.Compile
import Effect4.Laws.Program.CodeClosure.Callbacks

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: stable callback closure serves both crew cleanup log claims.
Reach: the actual direct-fragment value, cause, loop and suspend callbacks.
Limit: this graph retains leading bindings, without proving initialization or acquired literals.
Consumer: the stable answer-flow class and the crew writer debits.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Effect4.Program.AnswerSlots
open Effect4 Effect4.Machine Effect4.Program

/-- The existing leading-binding assertion instantiates the shared point callback contract. -/
theorem prefix_contract (root : NativeEff) (bindings : List Val) :
    CodeClosure.Slots.Contract root (fun p => Prefix bindings p.env) (Prefix bindings) where
  compilation := compile_contract root bindings
  child := fun held index => child held index
  childWith := fun held index value => childWith held index value
  capture := fun held value context => capture held value context

/-- A callback's child retains initialized leading bindings. -/
theorem resolve_child_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (bindings : List Val) (p : Point) (index : Nat) (held : Prefix bindings p.env) :
    CodeAt bindings (resolve root (p.child index)) := by
  rw [codeAt_fold]
  exact CodeClosure.Slots.resolve_child_at root fragment (fun p => Prefix bindings p.env) (Prefix bindings)
    (prefix_contract root bindings) p index held

/-- A callback appends its answer after initialized leading bindings. -/
theorem resolve_arg_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (bindings : List Val) (p : Point) (index : Nat) (value : Val) (held : Prefix bindings p.env) :
    CodeAt bindings (resolve root (p.childWith index value)) := by
  rw [codeAt_fold]
  exact CodeClosure.Slots.resolve_arg_at root fragment (fun p => Prefix bindings p.env) (Prefix bindings)
    (prefix_contract root bindings) p index value held

/-- A direct service region retains its leading environment under interpretation. -/
theorem region_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (bindings : List Val) (region : Region) (held : RegionAt bindings region) :
    CodeAt bindings (regionCode root region) := by
  rw [codeAt_fold]
  exact CodeClosure.Slots.region_at root fragment (fun p => Prefix bindings p.env) (Prefix bindings)
    (prefix_contract root bindings) region held

/-- Capturing an acquired answer preserves the leading environment. -/
theorem capture_at (bindings : List Val) (p : Point) (value : Val) (ctx : Ctx)
    (held : Prefix bindings p.env) : FinAt bindings (.foreign (p.capture value ctx)) :=
  capture held value ctx

/-- Calling any stable value callback preserves all delayed leading environments. -/
theorem contA_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (bindings : List Val) (name : EffName) (value : Val) (held : NameAt bindings name) :
    CodeAt bindings (contAOf root name value) := by
  rw [codeAt_fold]
  exact CodeClosure.Slots.contA_at root fragment (fun p => Prefix bindings p.env) (Prefix bindings)
    (prefix_contract root bindings) name value held

/-- Calling any stable cause callback preserves all delayed leading environments. -/
theorem contE_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (bindings : List Val) (name : EffName) (cause : CauseV) (held : NameAt bindings name) :
    CodeAt bindings (contEOf root name cause) := by
  rw [codeAt_fold]
  exact CodeClosure.Slots.contE_at root fragment (fun p => Prefix bindings p.env) (Prefix bindings)
    (prefix_contract root bindings) name cause held

/-- A loop's returned value carries no delayed lexical environment. -/
theorem loopFinish_at (bindings : List Val) (root : NativeEff) (p : Point) (cursor : Val) :
    CodeAt bindings (loopFinishAt root p cursor) := by
  rw [codeAt_fold]
  exact CodeClosure.Slots.loopFinish_at root (fun p => Prefix bindings p.env) (Prefix bindings) p cursor

/-- Both branches of a source decision preserve leading bindings. -/
theorem select_arg_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (bindings : List Val) (p : Point) (first : Bool) (bound : Option Val)
    (held : Prefix bindings p.env) :
    CodeAt bindings (resolve root (p.childBind (cond first 0 1) bound)) := by
  rw [codeAt_fold]
  exact CodeClosure.Slots.select_arg_at root fragment (fun p => Prefix bindings p.env) (Prefix bindings)
    (prefix_contract root bindings) p first bound held

/-- Every loop result retains the delayed environment of its body. -/
def LoopAt (bindings : List Val) : LoopNext Val NCode → Prop
  | .continue _ body | .finish body => CodeAt bindings body

/-- The loop reading uses the same generated runtime-code fold in each actual branch. -/
theorem loopAt_fold (bindings : List Val) (result : LoopNext Val NCode) :
    LoopAt bindings result ↔ CodeClosure.Slots.LoopAt (fun p => Prefix bindings p.env) (Prefix bindings) result := by
  cases result <;> exact Iff.of_eq (codeAt_fold bindings _)

/-- Entering an iterate body appends its cursor after initialized leading bindings. -/
theorem loopNext_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (bindings : List Val) (p : Point) (cursor : Val) (held : Prefix bindings p.env) :
    LoopAt bindings (loopNextAt root p cursor) := by
  rw [loopAt_fold]
  exact CodeClosure.Slots.loopNext_at root fragment (fun p => Prefix bindings p.env) (Prefix bindings)
    (prefix_contract root bindings) p cursor held

/-- A resumed iterate body starts from the same initialized leading bindings. -/
theorem loopResume_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (bindings : List Val) (p : Point) (cursor answer : Val) (held : Prefix bindings p.env) :
    LoopAt bindings (loopResumeAt root p cursor answer) := by
  rw [loopAt_fold]
  exact CodeClosure.Slots.loopResume_at root fragment (fun p => Prefix bindings p.env) (Prefix bindings)
    (prefix_contract root bindings) p cursor answer held

/-- Executing a stable suspended body preserves all delayed leading environments. -/
theorem suspend_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (bindings : List Val) (thunk : EffThunk) (held : ThunkAt bindings thunk) :
    CodeAt bindings (suspendBodyAt root thunk) := by
  rw [codeAt_fold]
  exact CodeClosure.Slots.suspend_at root fragment (fun p => Prefix bindings p.env) (Prefix bindings)
    (prefix_contract root bindings) thunk held

end Effect4.Program.AnswerSlots
