import Effect4.Codegen.Styles

/-! Finite receipts for relative form bindings, required slots, and the owner's
unambiguous-lambda ruling. No source recognizer or host equivalence is claimed here. -/
namespace Test.Codegen.FormsContract
open Effect4 Effect4.Program Effect4.Codegen.Forms Effect4.Codegen.Styles

def tap : Template := .bind (.argument 0 0 0)
  (.bind (.argument 1 0 1) (.succeed (.here 0)))

def args (n : Nat) : Arguments :=
  { effects := [.succeed (.lit (.nat 11)), .bind (.succeed (.lit (.nat 22))) (.succeed (.var n))] }

#guard [0, 2, 5].all fun n => tap.expand n (args n) == some
  (.bind (.succeed (.lit (.nat 11)))
    (.bind (.bind (.succeed (.lit (.nat 22))) (.succeed (.var (n + 1)))) (.succeed (.var n))))
#guard tap.expand 0 {} == none

-- Release's resource stays at n; only its local binder moves past the unused exit.
#guard [0, 2, 5].all fun n =>
  let release : Eff NativeOp := .bind (.succeed (.lit (.nat 2)))
    (.succeed (.app "pair" (.cons (.var n) (.cons (.var (n + 1)) .nil))))
  (Template.argument 0 1 1).expand n { effects := [release] } == some
    (.bind (.succeed (.lit (.nat 2)))
      (.succeed (.app "pair" (.cons (.var n) (.cons (.var (n + 2)) .nil)))))

#guard all.all fun f => [0, 1, 2, 5].all fun n => f.checkExample n && (Form.foreign f {} n).isSome
#guard [Effect4.Machine.FnName.incr, .double, .zeroWhenPositive, .noChange].all
  (fun f => (lambdaShape f).isSome)
#guard lambdaShape .takeAndBump == none
#guard match expression { lambdas := true } (.ident "takeAndBump") with
  | .leaf (.ident "takeAndBump") => true | _ => false
#guard match expression { lambdas := true } (.ident "incr") with
  | .atomLambda .addOne => true | _ => false
-- Every depth-n example includes its n enclosing bindings in the emitted source data.
#guard all.all fun f =>
  match Form.foreign f {} 1 with
  | some (.call _ [_, .lambda ["a0"] _]) => true
  | _ => false
#guard match all.find? (fun f => f.id == "yieldKey") with
  | some f => match Form.foreign f {} 0 with
    | some (.call (.leaf (.ident "Effect.gen")) [.generator _]) => true
    | _ => false
  | none => false
#print axioms lambdaAtom_exact
#print axioms Template.expand
#print axioms expression
end Test.Codegen.FormsContract
