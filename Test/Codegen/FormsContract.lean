import Effect4.Codegen.Styles
import Effect4.Laws.Codegen.Forms

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

-- The second effect captures an outer Nat and introduces its own Nat binder.
-- An omitted insertion would instead pass tap's Bool answer to `succ`.
def capturedSecond : NativeEff :=
  .bind (.succeed (.var 0)) (.succeed (.app "succ" (.cons (.var 1) .nil)))

#guard ((all.find? (fun f => f.id == "tapEffect")).bind
  (fun f => f.expansion.expand 1
    { effects := [.succeed (.lit (.bool true)), capturedSecond] })).bind
      (effTy nativeSignature [.nat]) = some (EffTy.pure .bool)
#guard effTy nativeSignature [.nat]
  (.bind (.succeed (.lit (.bool true)))
    (.bind capturedSecond (.succeed (.var 1)))) = none

-- The same captured finalizer is shifted beneath an exit, not a result value.
#guard ((all.find? (fun f => f.id == "ensuring")).bind
  (fun f => f.expansion.expand 1
    { effects := [.succeed (.lit (.bool true)), capturedSecond] })).bind
      (effTy nativeSignature [.nat]) = some (EffTy.pure .bool)
#guard effTy nativeSignature [.nat]
  (.onExit (.succeed (.lit (.bool true))) capturedSecond) = none

-- Inserting slots cannot turn a rejected captured computation into a typed one.
#guard effTy nativeSignature ([.nat] ++ [.bool, .unit] ++ [.string])
  (insert 1 2 (.succeed (.app "succ" (.cons (.var 1) .nil)) : NativeEff)) = none

#print axioms lambdaAtom_exact
#print axioms Template.expand
#print axioms expression
end Test.Codegen.FormsContract
