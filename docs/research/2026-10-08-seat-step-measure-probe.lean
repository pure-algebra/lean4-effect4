import Effect4.Modules.Queue.Steps
import Effect4.Modules.Pool.Steps
import Effect4.Modules.Semaphore.Steps
open Effect4 Effect4.Program Effect4.Program.Authoring Effect4.Modules
set_option maxRecDepth 16384
namespace Measurement
def termAt (names : List String) (src : TermSrc) : Option Term := (src {names := names} []).toOption
/-- The nodes of a term. -/
def nodesAlgebra : TermAlgebra (fun _ => Nat) where
  term_var _ := 1
  term_lit _ := 1
  term_app _ args := 1 + args
  term_record _ _ values := 1 + values
  term_field _ target _ := 1 + target
  term_recordSet target _ value := 1 + target + value
  term_tupleAt target _ := 1 + target
  term_fold _ list init body := 1 + list + init + body
  terms_nil := 0
  terms_cons head tail := head + tail

/-- The folds of a term. -/
def foldsAlgebra : TermAlgebra (fun _ => Nat) where
  term_var _ := 0
  term_lit _ := 0
  term_app _ args := args
  term_record _ _ values := values
  term_field _ target _ := target
  term_recordSet target _ value := target + value
  term_tupleAt target _ := target
  term_fold _ list init body := 1 + list + init + body
  terms_nil := 0
  terms_cons head tail := head + tail

/-- A step's nodes and folds, at the scope of its arguments. -/
def measure (names : List String) (src : TermSrc) : Option (Nat × Nat) :=
  (termAt names src).map fun t => (cata_term nodesAlgebra t, cata_term foldsAlgebra t)


-- QueueSteps
#eval measure ["id", "hint", "s"] (Queue.takeStep .nat (var "id") (var "hint") (var "s"))
#eval measure ["id", "hint", "a", "s"]
  (Queue.offerStep .nat (var "id") (var "hint") (var "a") (var "s"))
#eval measure ["s"] (Queue.pollStep .nat (var "s"))
#eval measure ["s"] (Queue.sizeStep .nat (var "s"))
#eval measure ["id", "s"] (Queue.withdrawTake .nat (var "id") (var "s"))
#eval measure ["id", "s"] (Queue.withdrawOffer .nat (var "id") (var "s"))
#eval measure [] (Queue.gained (nat 1) nilT nilT)

-- PoolSteps
#eval measure ["id", "hint", "s"] (Pool.leaseStep (var "id") (var "hint") (var "s"))
#eval measure ["item", "lease", "s"] (Pool.returnStep (var "item") (var "lease") (var "s"))
#eval measure ["count", "s"] (Pool.selectStep (var "count") (var "s"))
#eval measure ["id", "s"] (Pool.withdrawStep (var "id") (var "s"))
#eval measure ["s"] (Pool.closeStep (var "s"))
#eval measure ["id", "hint", "s"] (Pool.drainStep (var "id") (var "hint") (var "s"))
#eval measure ["s"] (Pool.headStamp (var "s"))
#eval measure ["s"] (Pool.marked (var "s"))
#eval measure ["s"] (Pool.leasedOf (var "s"))
#eval measure ["item", "lease", "s"] (Pool.heldBy (var "item") (var "lease") (var "s"))
#eval measure ["item", "lease", "s"] (Pool.freed (var "item") (var "lease") (var "s"))
#eval measure ["id", "s"] (Pool.withdrawn (var "id") (var "s"))
#eval measure ["s"] (Pool.outstanding (var "s"))
#eval measure [] (Pool.initial .nat [nat 1])
#eval measure [] (Pool.initial .nat [nat 1, nat 2])

-- SemaphoreSteps
#eval measure ["need", "id", "hint", "s"]
  (Semaphore.takeStep (var "need") (var "id") (var "hint") (var "s"))
#eval measure ["need", "s"] (Semaphore.takeIfAvailableStep (var "need") (var "s"))
#eval measure ["count", "s"] (Semaphore.releaseStep (var "count") (var "s"))
#eval measure ["cursor", "s"] (Semaphore.visitStep (var "cursor") (var "s"))
#eval measure ["id", "s"] (Semaphore.withdrawStep (var "id") (var "s"))
#eval measure ["cursor", "s"] (Semaphore.fromFirst (var "cursor") (var "s"))
#eval measure ["ws", "id"] (Semaphore.removeWaiter (var "ws") (var "id"))
end Measurement
