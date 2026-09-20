import Effect4.Laws.Auto.TypedStateDecl
import Effect4.Store.Val
open Effect4.Program.Typed

namespace Test.TypedStateDecl.Positive
inductive Expect | root
structure Sample where
  value : Effect4.Store.Val
def sources : List Row := [("Test.TypedStateDecl.Positive.Sample.value", .custom "ValueOk")]
#typed_state Test.TypedStateDecl.Positive.Sample using sources
example {W : Type} (P : Preds W) (w : W) (e : Expect) (x : Sample)
    (h : P.ValueOk w e x.value) : SampleOk P w e x := ⟨h⟩
end Test.TypedStateDecl.Positive

namespace Test.TypedStateDecl.Collision
inductive Expect | root
structure Sample where
  one : Option Effect4.Store.Val
  many : List Effect4.Store.Val
def sources : List Row := [
  ("Test.TypedStateDecl.Collision.Sample.one", .custom "Same"),
  ("Test.TypedStateDecl.Collision.Sample.many", .custom "Same")]
/-- error: typed state: incompatible uses of predicate Same -/
#guard_msgs in
#typed_state Test.TypedStateDecl.Collision.Sample using sources
end Test.TypedStateDecl.Collision

namespace Test.TypedStateDecl.Missing
inductive Expect | root
structure Sample where
  value : Effect4.Store.Val
def sources : List Row := []
/-- error: typed state: missing source for Test.TypedStateDecl.Missing.Sample.value -/
#guard_msgs in
#typed_state Test.TypedStateDecl.Missing.Sample using sources
end Test.TypedStateDecl.Missing
