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

/-! ### A term row as a form's argument (state plan T3b; register row `E4-CHECK-CE-019`)

A form places an argument effect under the binders it introduces: `insert cut count` weakens the
argument, an operation's own binder term included (`ScopedOp.mapTerm`). `tap`'s second argument
sits under the first argument's answer. With `Ref.update(cell, a => succ(a))` as that argument
at level 1 (the cell at `var 0`), the expansion keeps the cell and moves the term's current value
past the new binder. -/

/-- `Ref.update(cell, a => succ(a))` at level `n + 1`: the cell at `var n`, its value at
`var (n + 1)`. -/
def bump (n : Nat) : Eff NativeOp :=
  .perform (.refUpdateWith (.app "succ" (.cons (.var (n + 1)) .nil))) (.var n)

-- under the form's one new binder the request keeps the cell and the term reads `var (n + 2)`
#guard [0, 2, 5].all fun n =>
  (Template.argument 1 0 1).expand (n + 1) { effects := [.succeed (.lit .unit), bump n] } == some
    (.perform (.refUpdateWith (.app "succ" (.cons (.var (n + 2)) .nil))) (.var n))
#guard insert 1 1 (bump 0) =
  (.perform (.refUpdateWith (.app "succ" (.cons (.var 2) .nil))) (.var 0) : Eff NativeOp)
-- the inserted argument types as the argument did, whatever the new binder holds: the instance
-- of `effTy_insert_append` at the native signature
#guard [Ty.string, .nat, .bool].all fun slot =>
  effTy nativeSignature ([.refOf .nat] ++ [slot]) (insert 1 1 (bump 0)) ==
    effTy nativeSignature [.refOf .nat] (bump 0)
example (slot : Ty) :
    effTy nativeSignature ([.refOf .nat] ++ [slot]) (insert 1 1 (bump 0)) =
      effTy nativeSignature [.refOf .nat] (bump 0) :=
  effTy_insert_append nativeSignature (nativeSignature_weakenNatural []) [.refOf .nat] [slot]
    (bump 0)

/-- Red control: the insertion of before slice B of the state plan's T3b, which weakened the
request and left the operation's term alone. -/
def insertRequestOnly (cut : Nat) : Eff NativeOp → Eff NativeOp
  | .perform op request => .perform op (Term.weaken cut request)
  | e => e

-- the unshifted term still reads `var 1`, the form's new binder, not the cell's value
#guard insertRequestOnly 1 (bump 0) = bump 0
#guard insertRequestOnly 1 (bump 0) != insert 1 1 (bump 0)
-- a string in the new binder: the argument typed, and the unshifted insertion does not
#guard (effTy nativeSignature [.refOf .nat] (bump 0)).isSome
#guard effTy nativeSignature [.refOf .nat, .string] (insertRequestOnly 1 (bump 0)) = none
-- a number in the new binder: it types and reads the wrong binder, answering the binder's
-- successor where the inserted term answers the cell's
#guard (effTy nativeSignature [.refOf .nat, .nat] (insertRequestOnly 1 (bump 0))).isSome
#guard evalTerm ([Effect4.Machine.Val.cell ⟨0⟩, .nat 100] ++ [.nat 5])
  (.app "succ" (.cons (.var 1) .nil)) = some (.nat 101)
#guard evalTerm ([Effect4.Machine.Val.cell ⟨0⟩, .nat 100] ++ [.nat 5])
  (.app "succ" (.cons (.var 2) .nil)) = some (.nat 6)

#guard all.all fun f => [0, 1, 2, 5].all fun n => f.checkExample n && (Form.foreign f {} n).isSome
-- The foreign lambda shapes (the state plan's T5): the printer writes a row's term as a function,
-- and the `lambdas` style spells a function that is a shape's term at its row as the shape. The
-- five names are no identifiers of any face: a name is restyled nowhere.
#guard (lambdaShapes.map lambdaAtom) == [Effect4.Machine.FnName.incr, .double, .noChange, .zeroWhenPositive]
#guard match expression { lambdas := true } (.ident "incr") with
  | .leaf (.ident "incr") => true | _ => false
#guard match expression { lambdas := true }
    (.call (.ident "Ref.update") [.ident "a0", .lambda [{ name := "a1" }]
      (.call (.ident "succ") [.ident "a1"])]) with
  | .call _ [_, .atomLambda .addOne] => true | _ => false
-- `takeAndBump`'s term has no lambda spelling: its function keeps its printed form
#guard match expression { lambdas := true }
    (.call (.ident "Ref.update") [.ident "a0", .lambda [{ name := "a1" }]
      (.call (.ident "add") [.ident "a1", .int 1])]) with
  | .call _ [_, .lambda _ _ none] => true | _ => false
-- without the style every function keeps its printed form
#guard match expression {}
    (.call (.ident "Ref.update") [.ident "a0", .lambda [{ name := "a1" }]
      (.call (.ident "succ") [.ident "a1"])]) with
  | .call _ [_, .lambda _ _ none] => true | _ => false
-- Every depth-n example includes its n enclosing bindings in the emitted source data.
#guard all.all fun f =>
  match Form.foreign f {} 1 with
  | some (.call _ [_, .lambda [⟨"a0", none⟩] _ none]) => true
  | _ => false
#guard match all.find? (fun f => f.id == "yieldKey") with
  | some f => match Form.foreign f {} 0 with
    | some (.call (.leaf (.ident "Effect.gen")) [.generator _]) => true
    | _ => false
  | none => false

-- Restyling retains every explicit local type. These compare structural
-- fields rather than rendered strings or projected binder names.
private def numberType : TypeScript.TypeRef := .name ["number"] []

#guard match expression {} (.lambda [⟨"x", some numberType⟩] (.ident "x") (some numberType)) with
  | .lambda [⟨"x", some parameterType⟩] (.leaf (.ident "x")) (some resultType) =>
      parameterType == numberType && resultType == numberType
  | _ => false
#guard match expression {} (.arrow (some numberType) (.int 1)) with
  | .lambda [] (.leaf (.int 1)) (some resultType) => resultType == numberType
  | _ => false
#guard match expression {} (.arrowBlock [⟨"x", some numberType⟩]
    [.ret (.ident "x")] (some numberType)) with
  | .arrowBlock [⟨"x", some parameterType⟩] [.ret (.leaf (.ident "x"))] (some resultType) =>
      parameterType == numberType && resultType == numberType
  | _ => false
#guard match statement {} (.constYield "x" (.ident "program") (some numberType)) with
  | .constYield "x" (.leaf (.ident "program")) (some declaredType) => declaredType == numberType
  | _ => false
#guard match statement {} (.letInit "x" (.int 1) (some numberType)) with
  | .letInit "x" (.leaf (.int 1)) (some declaredType) => declaredType == numberType
  | _ => false
#guard match expression {} (.generic (.ident "f") [numberType]) with
  | .generic (.leaf (.ident "f")) [argumentType] => argumentType == numberType
  | _ => false

-- An unused exit can be omitted only when it has no annotation. A return
-- annotation remains present in either spelling.
#guard match expression { releaseOne := true }
    (.call (.ident "Effect.acquireRelease") [.ident "acquire",
      .lambda [⟨"resource", some numberType⟩, ⟨"exit", some numberType⟩]
        (.ident "release") (some numberType)]) with
  | .call _ [_, .lambda [⟨"resource", some resourceType⟩, ⟨"exit", some exitType⟩]
      _ (some resultType)] =>
      resourceType == numberType && exitType == numberType && resultType == numberType
  | _ => false
#guard match expression { releaseOne := true }
    (.call (.ident "Effect.acquireRelease") [.ident "acquire",
      .lambda [⟨"resource", some numberType⟩, ⟨"exit", none⟩]
        (.ident "release") (some numberType)]) with
  | .call _ [_, .lambda [⟨"resource", some resourceType⟩] _ (some resultType)] =>
      resourceType == numberType && resultType == numberType
  | _ => false

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

end Test.Codegen.FormsContract
