module

public import Effect4.Machine.Term
public import Effect4.Store.Carrier.Image

/-!
# Program.FnName — five function names, a library of binder terms

A read-modify-write row of `NativeOp` carries a binder term (decisions row 43, the state plan's
T3b). The term runs at `env ++ [current]`, so it reads its current value at the node's level
(`ScopedOp`'s convention). The faces print the term itself, as a function of the current value
(the state plan's T5, `Codegen/PrintLeaf.lean` `printPerform`): no face spells a name. Before T5
the printer and the readers spelled a term by one of the five names below
(`Ref.update(ref, incr)`). This module keeps what still has a reader:

* `FnShape`, rc.112's four function types of the eight rows, with the parameter and result
  templates of each (`nativeSignature`'s `termOf`, `Program/Native.lean`);
* `FnName`, the five names, with `FnName.image`, the term of a name at a shape and a level. The
  foreign lambda forms spell four of them (`LambdaShape.term`, `Codegen/Forms.lean`), and the
  batteries and the corpus generator build their read-modify-write rows from them;
* the names' meaning on values (`FnName.total` and its three siblings, `FnName.valueAt`): what
  the store ran for a name before it ran terms. On every number an image evaluates to it
  (`FnName.image_agrees`, `Laws/Program/Progress.lean`).

No program stores a name, and no store code reads this module.
-/

@[expose] public section

set_option autoImplicit false

namespace Effect4.Program

/-- rc.112's four function types of the eight read-modify-write rows (`Ref.ts`): `A → A` at the
three update rows, `A → Option<A>` at the three `Some` rows, `A → readonly [B, A]` at `modify`
and `A → readonly [B, Option<A>]` at `modifySome`. -/
inductive FnShape
  | update
  | updateSome
  | modify
  | modifySome
deriving DecidableEq, Repr

/-- The parameter of a shape over the row's parameters: the cell's element `A`, `var 0`. -/
def FnShape.param (_ : FnShape) : Ty := .var 0

/-- The result of a shape over the row's parameters `A = var 0` and `B = var 1`. -/
def FnShape.result : FnShape → Ty
  | .update => .var 0
  | .updateSome => .option (.var 0)
  | .modify => .prod (.var 1) (.var 0)
  | .modifySome => .prod (.var 1) (.option (.var 0))

end Effect4.Program

namespace Effect4.Machine

open Effect4.Program (FnShape)

/-- Names of five pure functions over numbers. rc.112 takes a JavaScript function; DB-02 forbids
storing one, and the rows carry binder terms (decisions row 43). A name stands for one term per
shape and level (`FnName.image`); the faces print the term, never the name (the state plan's
T5). -/
inductive FnName
  /-- `a ↦ a + 1`. -/
  | incr
  /-- `a ↦ 2 * a`. -/
  | double
  /-- partial: `Some 0` on a positive cell, `None` otherwise. -/
  | zeroWhenPositive
  /-- partial: `None` always — the `modifySome` write-back witness. -/
  | noChange
  /-- `modify`: answer the old value, write the bumped one. -/
  | takeAndBump
deriving DecidableEq, Repr

/-! ## The names' meaning on values

What the store ran for a name before it ran terms (the state plan's T2). Nothing runs these:
they are the right side of the images' agreement on numbers (`FnName.image_agrees`). -/

/-- `a ↦ f(a)` for the total read-modify-write operations. -/
def FnName.total : FnName → Val → Val
  | FnName.incr, Val.nat n => Val.nat (n + 1)
  | FnName.double, Val.nat n => Val.nat (n * 2)
  | FnName.takeAndBump, Val.nat n => Val.nat (n + 1)
  | _, value => value

/-- `a ↦ pf(a)` for the `Some`/`None` read-modify-write operations. -/
def FnName.partialUpdate : FnName → Val → Option Val
  | FnName.noChange, _ => none
  | FnName.zeroWhenPositive, Val.nat (Nat.succ _) => some (Val.nat 0)
  | FnName.zeroWhenPositive, _ => none
  | f, value => some (f.total value)

/-- `a ↦ [b, a']` (`Ref.ts:898`). -/
def FnName.modify : FnName → Val → Val × Val
  | FnName.takeAndBump, Val.nat n => (Val.nat n, Val.nat (n + 1))
  | f, value => (value, f.total value)

/-- `a ↦ [b, Option a']` (`Ref.ts:1161`). -/
def FnName.modifySome : FnName → Val → Val × Option Val
  | FnName.noChange, value => (value, none)
  | f, value => ((f.modify value).1, some (f.modify value).2)

/-- The value a name answers on a current value at a shape, in the frame the row's store step
reads: the value itself at `update`, the option image at `updateSome`, the pair at `modify`, and
the pair with an option image at `modifySome`. -/
def FnName.valueAt (f : FnName) : FnShape → Val → Val
  | .update, a => f.total a
  | .updateSome, a => Store.Image.toOption Store.Image.ident (f.partialUpdate a)
  | .modify, a => Program.Val.tuple [(f.modify a).1, (f.modify a).2]
  | .modifySome, a =>
    Program.Val.tuple [(f.modifySome a).1, Store.Image.toOption Store.Image.ident (f.modifySome a).2]

/-! ## The images: a name as a binder term, per shape and level

A name means one function at each of rc.112's four shapes, so it has one term per shape. The
term reads the current value at the node's level `n`, the variable `var n` (`ScopedOp`'s
convention), so one name is a different term at every level. Two names never share a term at a
shape: where the plain terms would repeat, `takeAndBump` reads `add(a, 1)` beside `incr`'s
`succ(a)`, and `zeroWhenPositive` reads `add(a, 0)` beside `noChange`'s `a`. -/

/-- The term of a name at `A → A`, over the term `a` of the current value. -/
def FnName.totalAt (a : Program.Term) : FnName → Program.Term
  | .incr => .app "succ" (.cons a .nil)
  | .double => .app "mul" (.cons a (.cons (.lit (.nat 2)) .nil))
  | .zeroWhenPositive => .app "add" (.cons a (.cons (.lit (.nat 0)) .nil))
  | .noChange => a
  | .takeAndBump => .app "add" (.cons a (.cons (.lit (.nat 1)) .nil))

/-- The term of a name at a shape, over the term `a` of the current value. -/
def FnName.imageAt (a : Program.Term) : FnShape → FnName → Program.Term
  | .update, f => f.totalAt a
  | .updateSome, .noChange => .app "none" .nil
  | .updateSome, .zeroWhenPositive =>
    .app "ite" (.cons (.app "lt" (.cons (.lit (.nat 0)) (.cons a .nil)))
      (.cons (.app "some" (.cons (.lit (.nat 0)) .nil)) (.cons (.app "none" .nil) .nil)))
  | .updateSome, .incr => .app "some" (.cons (FnName.incr.totalAt a) .nil)
  | .updateSome, .double => .app "some" (.cons (FnName.double.totalAt a) .nil)
  | .updateSome, .takeAndBump => .app "some" (.cons (FnName.takeAndBump.totalAt a) .nil)
  | .modify, f => .app "pair" (.cons a (.cons (f.totalAt a) .nil))
  | .modifySome, .noChange => .app "pair" (.cons a (.cons (.app "none" .nil) .nil))
  | .modifySome, .zeroWhenPositive =>
    .app "pair" (.cons a (.cons (.app "some" (.cons a .nil)) .nil))
  | .modifySome, .incr =>
    .app "pair" (.cons a (.cons (.app "some" (.cons (FnName.incr.totalAt a) .nil)) .nil))
  | .modifySome, .double =>
    .app "pair" (.cons a (.cons (.app "some" (.cons (FnName.double.totalAt a) .nil)) .nil))
  | .modifySome, .takeAndBump =>
    .app "pair" (.cons a (.cons (.app "some" (.cons (FnName.takeAndBump.totalAt a) .nil)) .nil))

/-- **The image of a name**: its term at a shape, the current value at `var n`, the level of the
node that performs the row. -/
def FnName.image (s : FnShape) (n : Nat) (f : FnName) : Program.Term := f.imageAt (.var n) s

end Effect4.Machine

namespace Effect4.Program

open Effect4.Machine (FnName)

/-- The five names, in declaration order. -/
def fnNames : List FnName := [.incr, .double, .zeroWhenPositive, .noChange, .takeAndBump]

/-- A name's spelling, as a label: the foreign corpus names its probes by it
(`tools/Drivers/Styles.lean`). No face prints it. -/
def fnSpelling : FnName → String
  | .incr => "incr"
  | .double => "double"
  | .zeroWhenPositive => "zeroWhenPositive"
  | .noChange => "noChange"
  | .takeAndBump => "takeAndBump"

end Effect4.Program

namespace Effect4.Machine

open Effect4.Program (FnShape fnNames)

/-- An image reads its current value and nothing else: over any environment in which the term
`a` evaluates to `v`, the image over `a` evaluates as the level-0 image over `[v]`. A step of
`FnName.image_eval`. -/
theorem FnName.evalTerm_imageAt {ρ : List Val} {a : Program.Term} {v : Val}
    (h : Program.evalTerm ρ a = some v) (s : FnShape) (f : FnName) :
    Program.evalTerm ρ (f.imageAt a s) = Program.evalTerm [v] (f.imageAt (.var 0) s) := by
  cases s <;> cases f <;>
    simp only [FnName.imageAt, FnName.totalAt, Program.evalTerm, Program.evalTerms, h,
      List.getElem?_cons_zero]

/-- **An image at a node's level reads the current value**: at `env ++ [a]`, the image at level
`env.length` evaluates as the level-0 image at `[a]`, whatever the outer environment holds. A
step of `FnName.image_agrees` (`Laws/Program/Progress.lean`). -/
theorem FnName.image_eval (s : FnShape) (f : FnName) (env : List Val) (a : Val) :
    Program.evalTerm (env ++ [a]) (FnName.image s env.length f) =
      Program.evalTerm [a] (FnName.image s 0 f) :=
  FnName.evalTerm_imageAt (List.getElem?_concat_length) s f

end Effect4.Machine
