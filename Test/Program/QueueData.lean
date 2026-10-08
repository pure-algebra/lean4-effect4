import Effect4.Modules.Queue.Steps
import Effect4.Laws.Modules.Step.ErasedCompiler

/-! Queue stored data controls. These finite evaluations cover generic messages,
flat triples, key comparison, and annotation-independent reading.
They establish no delivery, cancellation, progress, or target behavior. -/

set_option autoImplicit false
namespace Test.Program.QueueData
open Effect4 Effect4.Program Effect4.Program.Authoring Effect4.Schema Effect4.Schema.Model
open Effect4.Modules Effect4.Store

abbrev P : Ty := .var 0

def inputSource (n : Nat) : TermSrc := fun _ _ => .ok (.var n)
def run (src : TermSrc) (vals : List Val) : Option Val :=
  (src { names := vals.map fun _ => "slot" } []).toOption.bind (evalTerm vals ·)
def cellC : CarrierAt Leaves.deferredKeys (Queue.cellTy P) := ((1 : Nat), ([], ([], ([], ()))))
def offerInputs : Inputs Leaves.deferredKeys (Queue.Data.offerΓ P) :=
  (⟨1⟩, (⟨2⟩, (Val.unit, (cellC, ()))))
def encodedOffer : Val :=
  (imageAt Leaves.deferredKeys (.prod (.prod (.option .bool) (.list Queue.takerTy)) (Queue.cellTy P))).toVal
    (Step.eval Leaves.deferredKeys offerInputs (Queue.Data.offer P))
def encodedCell : Val := (imageAt Leaves.deferredKeys (Queue.cellTy P)).toVal cellC

-- The shared compiler law is read at Queue's actual offer data.
example (srcs : List TermSrc) : eraseSource ((Queue.Data.offer .nat).term (Input.source srcs)) =
    Step.cata Step.erasedTermAlg (Queue.Data.offer .nat) (Input.source srcs) :=
  Step.term_erase (Queue.Data.offer .nat) (Input.source srcs)

-- A message's arbitrary value remains untouched, even under a different declaration.
#guard run (Queue.offerStep .nat (inputSource 0) (inputSource 1) (inputSource 2) (inputSource 3))
  [Machine.Val.promise ⟨1⟩, Machine.Val.promise ⟨2⟩, Val.unit, encodedCell] = some encodedOffer
#guard run (Queue.offerStep P (inputSource 0) (inputSource 1) (inputSource 2) (inputSource 3))
  [Machine.Val.promise ⟨1⟩, Machine.Val.promise ⟨2⟩, Val.unit, encodedCell] = some encodedOffer

-- Deferred comparisons use the promise keys, including distinct stored requests.
#guard (show Bool from Step.eval (Γ := [idTy, idTy]) Leaves.deferredKeys (⟨1⟩, (⟨2⟩, ()))
  (Step.sameDeferred (Γ := [idTy, idTy]) (.var (.here _ _))
    (.var (.there _ (.here _ _))))) == false

-- This concrete record declaration is ignored by evaluation; its names remain observable.
def declaredRecord : Term := .record [("v", false, .nat)] ["v"] (.cons (.lit .unit) .nil)
example : evalTerm [] declaredRecord.eraseAnnotations = evalTerm [] declaredRecord :=
  evalTerm_eraseAnnotations declaredRecord []
#guard evalTerm [] declaredRecord.eraseAnnotations = some (.ctor 0 [.list [.str "v"], .list [.unit]])
end Test.Program.QueueData
