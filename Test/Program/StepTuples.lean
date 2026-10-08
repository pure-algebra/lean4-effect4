import Effect4.Laws.Modules.Step
import Effect4.Laws.Modules.Step.Scope
import Effect4.Laws.Modules.Step.Rename
import Effect4.Laws.Modules.Step.ErasedCompiler
import Effect4.Program.Native

/-! Readers and finite controls for arbitrary typed tuple item lists.
The shared Step laws own the reading, typing, scope, and renaming claims.
These cases exercise arities zero through four and the native two-item normalization cut.
No target execution or checked Modeled tuple admission is claimed. -/
set_option autoImplicit false
namespace Test.Program.StepTuples
open Effect4.Program Effect4.Program.Authoring Effect4.Schema Effect4.Schema.Model Effect4.Modules Effect4.Store

def zero : Step [] (.tuple []) := .tuple .nil
def one : Step [] (.tuple [.nat]) := .tuple (.cons (.nat 7) .nil)
def two : Step [] (.prod .nat .bool) := .tuple2 (.nat 7) (.bool true)
def three : Step [] (.tuple [.nat,.bool,.unit]) := .tuple3 (.nat 7) (.bool true) .unit
def four : Step [] (.tuple [.nat,.bool,.unit,.nat]) :=
  .tuple (.cons (.nat 7) (.cons (.bool true) (.cons .unit (.cons (.nat 9) .nil))))

-- The retained triple compatibility corollary reads at the original flat carrier.
example : three.eval (Γ := []) Leaves.opaque () =
    ((7 : Nat), ((true : Bool), ((() : Unit), ()))) :=
  Step.eval_tuple3 (Γ := []) (L := Leaves.opaque) (.nat 7) (.bool true) .unit ()

#guard zero.normal && one.normal && two.normal && three.normal && four.normal
#guard zero.canonical && one.canonical && two.canonical && three.canonical && four.canonical
#guard (zero.term (Input.source []) {} []).toOption == some (.app "tuple" .nil)
#guard (two.term (Input.source []) {} []).toOption ==
  some (.app "tuple" (.cons (.lit (.nat 7)) (.cons (.lit (.bool true)) .nil)))
#guard (three.term (Input.source []) {} []).toOption ==
  some (.app "tuple" (.cons (.lit (.nat 7)) (.cons (.lit (.bool true)) (.cons (.lit .unit) .nil))))
#guard (one.term (Input.source []) {} []).toOption == some (.app "tuple" (.cons (.lit (.nat 7)) .nil))
#guard match four.term (Input.source []) {} [] with
  | .ok t => evalTerm [] t == some (Val.tuple [.nat 7,.bool true,.unit,.nat 9]) &&
      termTy nativeSignature [] t == some (Ty.tuple [.nat,.bool,.unit,.nat])
  | .error _ => false

example : Reads (zero.term (Input.source [])) {} [] [] (Val.tuple []) :=
  Step.sound (Γ := []) Leaves.opaque () Input.reads_nil zero rfl
example : Reads (one.term (Input.source [])) {} [] [] (Val.tuple [.nat 7]) :=
  Step.sound (Γ := []) Leaves.opaque () Input.reads_nil one rfl
example : Reads (two.term (Input.source [])) {} [] [] (Val.tuple [.nat 7,.bool true]) :=
  Step.sound (Γ := []) Leaves.opaque () Input.reads_nil two rfl
example : Reads (three.term (Input.source [])) {} [] [] (Val.tuple [.nat 7,.bool true,.unit]) :=
  Step.sound (Γ := []) Leaves.opaque () Input.reads_nil three rfl
example : Reads (four.term (Input.source [])) {} [] [] (Val.tuple [.nat 7,.bool true,.unit,.nat 9]) :=
  Step.sound (Γ := []) Leaves.opaque () Input.reads_nil four rfl

example : TypesEach nativeSignature (zero.term (Input.source [])) {} [] [] (Ty.tuple []) :=
  Step.typed_of_normal nativeSignature rfl Input.types_nil zero rfl
example : TypesEach nativeSignature (one.term (Input.source [])) {} [] [] (Ty.tuple [.nat]) :=
  Step.typed_of_normal nativeSignature rfl Input.types_nil one rfl
example : TypesEach nativeSignature (two.term (Input.source [])) {} [] [] (.prod .nat .bool) :=
  Step.typed_of_normal nativeSignature rfl Input.types_nil two rfl
example : TypesEach nativeSignature (three.term (Input.source [])) {} [] [] (Ty.tuple [.nat,.bool,.unit]) :=
  Step.typed_of_normal nativeSignature rfl Input.types_nil three rfl
example : TypesEach nativeSignature (four.term (Input.source [])) {} [] [] (Ty.tuple [.nat,.bool,.unit,.nat]) :=
  Step.typed_of_normal nativeSignature rfl Input.types_nil four rfl
example : (four.term (Input.source [])).Scoped := Step.scoped four (fun x => nomatch x)

-- Two union items normalize to a wider product. The exact declared product cannot type by the check.
def unionItem : Ty := .union .nat .bool
def unionTwo : Step [unionItem] (.prod unionItem .unit) := .tuple2 (.var (.here _ _)) .unit
#guard !unionTwo.normal

-- More than two items retain the flat tuple index even for a generic payload.
def payloadFour (A : Ty) : Step [A] (.tuple [A,.nat,.bool,.unit]) :=
  .tuple (.cons (.var (.here _ _)) (.cons (.nat 7) (.cons (.bool true) (.cons .unit .nil))))
example (A : Ty) (normal : A.normalize = A) : (payloadFour A).Facts :=
  ⟨⟨normal,rfl,rfl,rfl⟩, trivial, trivial, trivial, trivial⟩
example (A : Ty) (value : CarrierAt Leaves.opaque A) :
    (payloadFour A).eval (Γ := [A]) Leaves.opaque (value, ()) =
      (value, ((7 : Nat), ((true : Bool), ((() : Unit), ())))) := rfl

-- A noncanonical captured record keeps its refusal at arbitrary tuple arity.
def badFields : List (String × Bool × Ty) := [("z",false,.nat),("a",false,.nat)]
def badRead : Step [.record badFields] (.tuple [.nat]) :=
  .tuple (.cons (.get (.var (.here _ _)) (.here "z" .nat _)) .nil)
#guard !badRead.canonical

-- A fold nested in a tuple retains its scope requirement and flat result.
def foldedOne : Step [] (.tuple [.nat]) := .tuple (.cons
  (.fold (.cons (.nat 3) .nil) (.nat 2)
    (.add (.var (.here _ _)) (.var (.there _ (.here _ _))))) .nil)
#guard foldedOne.binds && foldedOne.normal
example : Reads (foldedOne.term (Input.source [])) {} [] [] (Val.tuple [.nat 5]) :=
  Step.sound (Γ := []) Leaves.opaque () Input.reads_nil foldedOne rfl rfl
example : TypesEach nativeSignature (foldedOne.term (Input.source [])) {} [] [] (.tuple [.nat]) :=
  Step.typed_of_normal nativeSignature rfl Input.types_nil foldedOne rfl rfl

-- Generic payload values survive tuple renaming, including the terminal column unit.
example (A : Ty) (value : CarrierAt Leaves.opaque A) :
    ((payloadFour A).rename (fun x => .there .nat x)).eval (Γ := [.nat,A])
      Leaves.opaque ((4 : Nat), (value, ())) =
      (payloadFour A).eval (Γ := [A]) Leaves.opaque (value, ()) :=
  Step.eval_lift Leaves.opaque (u := .nat) (payloadFour A) (value, ()) (4 : Nat)

/-- error: Application type mismatch: The argument
  Step.bool true
has type
  Step [] Ty.bool
but is expected to have type
  Step [] Ty.nat
in the application
  StepItems.cons (Step.bool true) -/
#guard_msgs in
example : StepItems [] [.nat] := .cons (Step.bool (Γ := []) true) .nil

/-- error: Type mismatch
  (Step.nat 7).tuple2 (Step.bool true)
has type
  Step [] (Ty.nat.prod Ty.bool)
but is expected to have type
  Step [] (Ty.tuple [Ty.nat, Ty.bool]) -/
#guard_msgs in
example : Step [] (.tuple [.nat,.bool]) := .tuple2 (Step.nat (Γ := []) 7) (.bool true)

end Test.Program.StepTuples
