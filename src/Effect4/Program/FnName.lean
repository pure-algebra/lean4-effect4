module

public import Effect4.Machine.Term
public import Effect4.Store.Carrier.Image

/-!
# Program.FnName — the five function names, the faces' vocabulary for a binder term

A read-modify-write row of `NativeOp` carries a binder term (decisions row 43, the state plan's
T3b). The term runs at `env ++ [current]`, so it reads its current value at the node's level
(`ScopedOp`'s convention). Until the state plan's T5 prints a term as a lambda, the printer and
the readers spell a term by one of five names (`Ref.update(ref, incr)`). This module owns that
vocabulary:

* `FnShape`, rc.112's four function types of the eight rows, with the parameter and result
  templates of each;
* `FnName`, the five names, with their printed spelling (`fnSpelling`);
* `FnName.image`, the term of a name at a shape and a level, and `FnName.decode?`, the name of a
  term. The pair is an exact embedding of five names into terms at each shape and level:
  `FnName.decode?_image` is the retraction and `FnName.image_of_decode?` the exactness;
* the names' meaning on values (`FnName.total` and its three siblings, `FnName.valueAt`): what
  the store ran for a name before it ran terms, and what the TypeScript prelude's five functions
  compute (`harness/truth/prelude.ts`). On every number an image evaluates to it
  (`FnName.image_agrees`, `Laws/Program/Progress.lean`).

No program stores a name: a term that is no name's image is refused by the faces by its row's
spelling (`PrintRefusal.binderTerm`), never printed as a name. No store code reads this module.
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

/-- Names of the pure functions the faces spell a read-modify-write row's binder term by, until
the state plan's T5. rc.112 takes a JavaScript function; DB-02 forbids storing one, and the rows
carry binder terms (decisions row 43). A name is the faces' spelling of five terms per shape
(`FnName.image`). -/
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

What the store ran for a name before it ran terms (the state plan's T2). The TypeScript prelude's
five functions transcribe `total` and `partialUpdate` (`harness/truth/prelude.ts`). Nothing runs
these: they are the right side of the images' agreement on numbers (`FnName.image_agrees`). -/

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

/-- The five names, in declaration order: the order the tools' profiles print. -/
def fnNames : List FnName := [.incr, .double, .zeroWhenPositive, .noChange, .takeAndBump]

/-- The printed name of a pure function, `Ref.update(ref, incr)`. -/
def fnSpelling : FnName → String
  | .incr => "incr"
  | .double => "double"
  | .zeroWhenPositive => "zeroWhenPositive"
  | .noChange => "noChange"
  | .takeAndBump => "takeAndBump"

end Effect4.Program

namespace Effect4.Machine

open Effect4.Program (FnShape fnNames)

/-- **The name of a term** at a shape and a level: the name whose image the term is, `none` for a
term that is no name's image there. -/
def FnName.decode? (s : FnShape) (n : Nat) (t : Program.Term) : Option FnName :=
  fnNames.find? fun f => FnName.image s n f == t

/-- The name the head of an `A → A` term spells, read without the term's level. A step of
`FnName.headName?`. -/
def FnName.totalName? : Program.Term → Option FnName
  | .app "succ" _ => some .incr
  | .app "mul" _ => some .double
  | .app "add" (.cons _ (.cons (.lit (.nat 0)) .nil)) => some .zeroWhenPositive
  | .app "add" _ => some .takeAndBump
  | .var _ => some .noChange
  | _ => none

/-- The name a term's head spells at a shape, read without the term's level: the injectivity
witness of `FnName.image`, a step of `FnName.decode?_image`. -/
def FnName.headName? : FnShape → Program.Term → Option FnName
  | .update, t => FnName.totalName? t
  | .updateSome, .app "none" _ => some .noChange
  | .updateSome, .app "ite" _ => some .zeroWhenPositive
  | .updateSome, .app "some" (.cons t .nil) => FnName.totalName? t
  | .modify, .app "pair" (.cons _ (.cons t .nil)) => FnName.totalName? t
  | .modifySome, .app "pair" (.cons _ (.cons (.app "none" _) .nil)) => some .noChange
  | .modifySome, .app "pair" (.cons _ (.cons (.app "some" (.cons (.var _) .nil)) .nil)) =>
    some .zeroWhenPositive
  | .modifySome, .app "pair" (.cons _ (.cons (.app "some" (.cons t .nil)) .nil)) =>
    FnName.totalName? t
  | _, _ => none

/-- The head of an image spells its name, at every level. A step of `FnName.decode?_image`. -/
theorem FnName.headName?_image (s : FnShape) (n : Nat) (f : FnName) :
    FnName.headName? s (FnName.image s n f) = some f := by
  cases s <;> cases f <;> rfl

/-- Two names never share an image at a shape and a level. A step of `FnName.decode?_image`. -/
theorem FnName.image_injective {s : FnShape} {n : Nat} {f g : FnName}
    (h : FnName.image s n f = FnName.image s n g) : f = g := by
  have hf := FnName.headName?_image s n f
  rw [h, FnName.headName?_image] at hf
  exact (Option.some.inj hf).symm

/-- **Retraction**: a name reads back from its image, at every shape and level. With
`FnName.image_of_decode?` it makes the names an exact embedding into terms; a step of the faces'
round trip (`NativeOp.atLevel_symm`, `Program/Native.lean`). -/
theorem FnName.decode?_image (s : FnShape) (n : Nat) (f : FnName) :
    FnName.decode? s n (FnName.image s n f) = some f := by
  have hbeq : (fun g => FnName.image s n g == FnName.image s n f) = fun g => g == f := by
    funext g
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
    exact ⟨FnName.image_injective, fun h => h ▸ rfl⟩
  unfold FnName.decode?
  rw [hbeq]
  cases f <;> rfl

/-- **Exactness**: what reads as a name is that name's image. A term that is no image reads as
no name. -/
theorem FnName.image_of_decode? {s : FnShape} {n : Nat} {t : Program.Term} {f : FnName}
    (h : FnName.decode? s n t = some f) : FnName.image s n f = t :=
  eq_of_beq (List.find?_some (p := fun g => FnName.image s n g == t) h)

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

/-! ## T2's connector: a name lowered to a binder term at level 0 (retires at the cutover)

Until the rows carry their own terms (the state plan's T3b, slice E's cutover), `syncOpOf` hands
the store a name's lowering, one term per shape, each reading the cell's value at level 0 of the
environment `[]`. On every number each term evaluates to the image of the name's answer
(`FnName.updateTerm_agrees` and its three siblings, by `rfl`), and so does the faces' image at
every level (`FnName.image_agrees`, `Laws/Program/Progress.lean`). The four lowerings and their
agreements leave with the cutover. -/

/-- The term of a name at `A → A`: `succ(a)` for `incr` and `takeAndBump`, `mul(a, 2)` for
`double`, `a` for the other two. -/
def FnName.updateTerm : FnName → Program.Term
  | FnName.incr | FnName.takeAndBump => .app "succ" (.cons (.var 0) .nil)
  | FnName.double => .app "mul" (.cons (.var 0) (.cons (.lit (.nat 2)) .nil))
  | FnName.zeroWhenPositive | FnName.noChange => .var 0

/-- The term of a name at `A → Option<A>`: `none()` for `noChange`,
`ite(lt(0, a), some(0), none())` for `zeroWhenPositive`, `some` of the `A → A` term for the
others. -/
def FnName.updateSomeTerm : FnName → Program.Term
  | FnName.noChange => .app "none" .nil
  | FnName.zeroWhenPositive =>
    .app "ite" (.cons (.app "lt" (.cons (.lit (.nat 0)) (.cons (.var 0) .nil)))
      (.cons (.app "some" (.cons (.lit (.nat 0)) .nil)) (.cons (.app "none" .nil) .nil)))
  | f => .app "some" (.cons f.updateTerm .nil)

/-- The term of a name at `A → [B, A]`: the pair of the value read and the `A → A` term. -/
def FnName.modifyTerm (f : FnName) : Program.Term :=
  .app "pair" (.cons (.var 0) (.cons f.updateTerm .nil))

/-- The term of a name at `A → [B, Option<A>]`: the value read, paired with `none()` for
`noChange` and with `some` of the `A → A` term for the others. -/
def FnName.modifySomeTerm : FnName → Program.Term
  | FnName.noChange => .app "pair" (.cons (.var 0) (.cons (.app "none" .nil) .nil))
  | f => .app "pair" (.cons (.var 0) (.cons (.app "some" (.cons f.updateTerm .nil)) .nil))

/-- T2's lowering of a name at a shape. -/
def FnName.lowering (f : FnName) : FnShape → Program.Term
  | .update => f.updateTerm
  | .updateSome => f.updateSomeTerm
  | .modify => f.modifyTerm
  | .modifySome => f.modifySomeTerm

/-- On every number the `A → A` term evaluates to the name's answer. -/
theorem FnName.updateTerm_agrees (f : FnName) (n : Nat) :
    Program.evalTerm [.nat n] f.updateTerm = some (f.total (.nat n)) := by
  cases f <;> rfl

/-- On every number the `A → Option<A>` term evaluates to the option image of the name's
answer. -/
theorem FnName.updateSomeTerm_agrees (f : FnName) (n : Nat) :
    Program.evalTerm [.nat n] f.updateSomeTerm =
      some (Store.Image.toOption Store.Image.ident (f.partialUpdate (.nat n))) := by
  cases f
  case zeroWhenPositive => cases n <;> rfl
  all_goals rfl

/-- On every number the `A → [B, A]` term evaluates to the pair of the name's answer. -/
theorem FnName.modifyTerm_agrees (f : FnName) (n : Nat) :
    Program.evalTerm [.nat n] f.modifyTerm =
      some (Program.Val.tuple [(f.modify (.nat n)).1, (f.modify (.nat n)).2]) := by
  cases f <;> rfl

/-- On every number the `A → [B, Option<A>]` term evaluates to the pair of the name's answer,
its second component through the option image. -/
theorem FnName.modifySomeTerm_agrees (f : FnName) (n : Nat) :
    Program.evalTerm [.nat n] f.modifySomeTerm =
      some (Program.Val.tuple [(f.modifySome (.nat n)).1,
        Store.Image.toOption Store.Image.ident (f.modifySome (.nat n)).2]) := by
  cases f <;> rfl

/-- On every number T2's lowering evaluates to the name's value at the shape: the four
agreements above, as one statement. -/
theorem FnName.lowering_agrees (f : FnName) (s : FnShape) (n : Nat) :
    Program.evalTerm [.nat n] (f.lowering s) = some (f.valueAt s (.nat n)) := by
  cases s
  · exact f.updateTerm_agrees n
  · exact f.updateSomeTerm_agrees n
  · exact f.modifyTerm_agrees n
  · exact f.modifySomeTerm_agrees n

end Effect4.Machine
