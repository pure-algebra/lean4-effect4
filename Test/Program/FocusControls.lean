import Effect4.Laws.Program.Sketch
import Test.Program.ReplaceControls

/-!
# The focus function (decisions row 292): the controls of the first half of slice TRACE

`Program/Typing/Focus.lean` computes the focus at an address of a program: the sub-program, its
environment and its type (`focusAt`, over the step `Node.childEnv` and its fold `Node.envAt`).
`Laws/Program/Typing/Focus.lean` and `Laws/Program/Sketch.lean` prove that the replacement law
holds at its answer. These are the fixtures, on the example of `Test/Program/SketchControls.lean`:

    x = succeed 5;  cell = Ref.make(x);  _ = Ref.set(cell, 7);  Ref.get(cell)

* **Green (tested): the focus at each address.** The example has seven addresses of a program.
  The function answers the environment and the type at each one.
* **Green (tested): the omission that a tool computes.** At each of the seven addresses, the
  omission with the hole row that declares the answered type keeps the example's type. No type
  is written by hand.
* **Green (tested): a tool at a hole.** After an omission, the focus at the address is the
  hole, in the same environment, at the same type.
* **Proved: the two edits at a focus that reads its environment.** `Ref.get(cell)` reads a
  variable. Every program that the checker admits at a number in that focus's environment fills
  the address (`fill_a_reading_focus`), and the omission that declares a number keeps the type
  (`omit_a_reading_focus`). Slice REPLACE could prove neither: its focus was existential.
* **Red (tested): a filling of another type** at that focus. The law's premise fails, and the
  whole changes its type.
* **The first consumer (tested): a term of two members at an eliminator.** A term has no
  address. Its type is `termTy` at the environment of its node. Under `length` the term is a
  list of numbers or a list of strings, and the function answers both members.
* **The same shape, refused (tested).** With two fiber types under a join the checker refuses
  the program as `notFiber`. The focus at the refused node has no type. The environment there
  still answers, and so do the term's two members: what a printer of type arguments reads.
* **Tested: the three shapes of environment.** A statement and a loop's body read the loop flag.
  A layer's body is typed closed, under an environment that is not empty.
* **Red (tested): no address of a program**, and an address of a statement: the focus is none,
  and the environment answers at the statement.
* **Red (tested): an earlier sibling with no type.** The children after it have no environment.
  The sibling before a refused one keeps its focus: the function asks nothing of the program
  around the focus (`focusAt_typed`).
-/

set_option autoImplicit false

namespace Test.Program.FocusControls

open Effect4 Effect4.Program
open Effect4.Machine.Env (Requirement)
open Conform.Effect4.Typing
open Test.Program.SketchControls
open Test.Program.ReplaceControls

/-- The typing signature of the empty application. -/
def sig : Signature NativeOp := ({} : SigApp).signature

/-- The environment and the type of the focus at an address of a sketch. -/
def focusOf (s : Sketch) (path : List Nat) : Option (TyEnv × EffTy) :=
  (s.focusAt {} path).map fun f => (f.env, f.ty)

/-- The type of a cell of numbers, with no error and no requirement. -/
def cellTy : EffTy := ⟨.refOf .nat, .never, Requirement.empty⟩

/-! ## The focus at each address of the example -/

-- green (tested): the seven addresses of a program, each with its environment and its type
#guard focusOf original [] = some ([], numberTy)
#guard focusOf original [0] = some ([], numberTy)
#guard focusOf original [1] = some ([.nat], numberTy)
#guard focusOf original [1, 0] = some ([.nat], cellTy)
#guard focusOf original [1, 1] = some ([.nat, .refOf .nat], numberTy)
#guard focusOf original [1, 1, 0] = some ([.nat, .refOf .nat], cellTy)
#guard focusOf original [1, 1, 1] = some ([.nat, .refOf .nat, .refOf .nat], numberTy)
-- tested: the answered program is the sub-program at the address
#guard ((original : Sketch).focusAt {} [0]).map (·.program) = some (.succeed (.lit (.nat 5)))
#guard ((original : Sketch).focusAt {} [1, 1, 1]).map (·.program) =
  some (.perform .refGet (.var 1))
-- tested: at the root the answer is the checker's
#guard focusOf original [] = (Sketch.check (original : Sketch)).toOption.map fun t => ([], t)
-- red (tested): no address of a program
#guard (focusOf original [9]).isNone
#guard (focusOf original [0, 0]).isNone

/-! ## The omission that a tool computes -/

/-- The check of a sketch with the sub-program at `path` omitted, under the hole row that
declares the type which the focus function answers there. -/
def omitComputed (s : Sketch) (path : List Nat) : Option (Except TypeRefusal EffTy) :=
  (s.focusAt {} path).bind fun f =>
    (s.omitAt {} path (Row.hole "h0" f.ty.answer f.ty.error f.ty.requires.elems)).map (·.check)

-- green (tested): at each of the seven addresses the computed omission keeps the type
#guard [[], [0], [1], [1, 0], [1, 1], [1, 1, 0], [1, 1, 1]].all fun path =>
  omitComputed original path = some (.ok numberTy)
-- green (tested): a tool at a hole. After the omission the focus at the address is the hole,
-- in the same environment, at the same type
#guard (((original : Sketch).omitAt {} [1, 1, 1] (Row.hole "h0" .nat)).bind fun s =>
    (s.focusAt {} [1, 1, 1]).map fun f => (f.program, f.env, f.ty)) =
  some (Sketch.hole {} 0, [.nat, .refOf .nat, .refOf .nat], numberTy)

/-! ## The two edits at a focus that reads its environment, by the law -/

/-- The focus at `[1, 1, 1]` of the example: `Ref.get(cell)`, which reads the variable `cell`. -/
def readingFocus : Focus NativeOp :=
  ⟨.perform .refGet (.var 1), [.nat, .refOf .nat, .refOf .nat], numberTy⟩

/-- The focus function answers that focus (proved, by evaluation in the kernel). -/
theorem reading_focus_answered : (original : Sketch).focusAt {} [1, 1, 1] = some readingFocus := by
  decide +kernel

/-- **Every filling at a focus that reads its environment (proved, by the law).** Every program
that the checker admits at a number, in the environment that the focus function answers, fills
the address, and the example keeps its type. The filling alone is checked. -/
theorem fill_a_reading_focus (q' : NativeEff) (pq : List Nat)
    (hq' : Checker.check sig [.nat, .refOf .nat, .refOf .nat] pq q' = .ok numberTy) :
    ∃ s', (original : Sketch).fillAt [1, 1, 1] q' = some s' ∧ s'.check = .ok numberTy := by
  obtain ⟨s', hs', hT⟩ := Sketch.check_fill_focusAt (original : Sketch) {} original_checked
    reading_focus_answered [] (q' := q') (pq := pq) hq'
  exact ⟨s', by simpa only [List.append_nil] using hs', hT⟩

/-- **The omission at a focus that reads its environment (proved, by the law).** The hole row
declares the answered type, a number, and the omission keeps the example's type. -/
theorem omit_a_reading_focus :
    ∃ s', (original : Sketch).omitAt {} [1, 1, 1] (Row.hole "h0" .nat) = some s' ∧
      s'.check = .ok numberTy :=
  Sketch.check_omit_focusAt (original : Sketch) {} original_checked reading_focus_answered "h0"
    rfl rfl (by decide +kernel) (by decide +kernel)
    ((Formation.check_eq_none_iff _).mp (by decide +kernel))

-- green (tested): a filling that reads the first variable has the premise, and the type stays
#guard Checker.check sig [.nat, .refOf .nat, .refOf .nat] [] (.succeed (.var 0)) = .ok numberTy
#guard ((original : Sketch).fillAt [1, 1, 1] (.succeed (.var 0))).map (·.check) =
  some (.ok numberTy)
-- red (tested): a filling that reads the cell is of another type; the premise fails, and the
-- whole changes its type
#guard Checker.check sig [.nat, .refOf .nat, .refOf .nat] [] (.succeed (.var 1)) = .ok cellTy
#guard ((original : Sketch).fillAt [1, 1, 1] (.succeed (.var 1))).map (·.check) = some (.ok cellTy)

/-! ## The first consumer: the type of a term at an eliminator -/

/-- The type of a term that stands in the node at an address: the environment there, and
`termTy`. A term has no address of its own. -/
def termTyAt (p : NativeEff) (path : List Nat) (t : Term) : Option Ty :=
  ((Node.eff p).envAt sig (.env []) path).bind fun ctx => termTy sig ctx.tyEnv t

/-- A list of one element. -/
def listOf (x : Term) : Term := .app "cons" (.cons x (.cons (.app "nil" .nil) .nil))

/-- `if true then [1] else ["a"]`: a list of numbers or a list of strings. -/
def twoLists : NativeEff :=
  .select (.lit (.bool true)) .bool
    (.succeed (listOf (.lit (.nat 1)))) (.succeed (listOf (.lit (.str "a"))))

/-- `xs = twoLists; succeed (length xs)`: an eliminator over a term of two members. -/
def lengthOf : NativeEff := .bind twoLists (.succeed (.app "length" (.cons (.var 0) .nil)))

-- tested: the checker admits the program
#guard Checker.check sig [] [] lengthOf = .ok numberTy
-- green (tested): at the eliminator's node the term has its two members
#guard (termTyAt lengthOf [1] (.var 0)).map Ty.members = some [.list .nat, .list .string]
-- tested: the focus there has the environment of that one variable
#guard ((focusAt sig [] lengthOf [1]).map fun f => (f.env.map Ty.members, f.ty)) =
  some ([[.list .nat, .list .string]], numberTy)

/-- The options of a fork. -/
def forkOptions : Supervision.ForkOptions := ⟨true, false, .inherit⟩

/-- `if true then fork (succeed 1) else fork (succeed "a")`: one of two fiber types. -/
def twoFibers : NativeEff :=
  .select (.lit (.bool true)) .bool
    (.withFiber (.fork (.succeed (.lit (.nat 1))) forkOptions))
    (.withFiber (.fork (.succeed (.lit (.str "a"))) forkOptions))

/-- `f = twoFibers; join f`: the same shape, with a join over a term of two members. -/
def joinOf : NativeEff := .bind twoFibers (.awaitFiber (.var 0) .joinEffect)

-- red (tested): the checker refuses the program at the join, as no fiber
#guard refusedAt (Checker.check sig [] [] joinOf) = some ([1], "notFiber")
-- red (tested): the focus at the refused node has no type
#guard (focusAt sig [] joinOf [1]).isNone
-- green (tested): the environment at the refused node answers, and the term has its two
-- members there: what a printer of the join's type arguments reads
#guard (Node.eff joinOf).envAt sig (.env []) [1] =
  some (.env [.union (.fiberOf .nat .never) (.fiberOf .string .never)])
#guard (termTyAt joinOf [1] (.var 0)).map Ty.members =
  some [.fiberOf .nat .never, .fiberOf .string .never]
-- tested: the sibling before the refused node keeps its focus
#guard ((focusAt sig [] joinOf [0]).map fun f => (f.env, f.ty.answer.members)) =
  some ([], [.fiberOf .nat .never, .fiberOf .string .never])

/-! ## The three shapes of environment -/

/-- `gen { x = yield* succeed 1; while (true) { yield* succeed x; break }; return x }`. -/
def genBody : NativeEff :=
  .gen (.cons (.bindYield (.succeed (.lit (.nat 1))))
    (.cons (.whileTrue (.cons (.yieldDiscard (.succeed (.var 0))) (.cons .breakLoop .nil)))
      (.cons (.ret (.var 0)) .nil)))

/-- The environment at an address of `genBody`. -/
def genEnv (path : List Nat) : Option NodeEnv := (Node.eff genBody).envAt sig (.env []) path

-- tested: the checker admits the program
#guard (Checker.check sig [] [] genBody).toOption.isSome
-- tested: a statement list and a statement read the loop flag; the body starts outside a loop
#guard genEnv [0] = some (.body [] false)
#guard genEnv [0, 0] = some (.body [] false)
-- tested: the statements after a `bindYield` read its answer
#guard genEnv [0, 1] = some (.body [.nat] false)
-- tested: the body of a loop is typed in a loop, and a program in it reads no flag
#guard genEnv [0, 1, 0, 0] = some (.body [.nat] true)
#guard genEnv [0, 1, 0, 0, 0, 0] = some (.env [.nat])
-- tested: the statements after the loop are outside it again
#guard genEnv [0, 1, 1] = some (.body [.nat] false)
-- red (tested): an address of a statement has an environment and no focus
#guard (focusAt sig [] genBody [0, 1, 0]).isNone
-- tested: the term of the `return` statement is typed at its statement's environment
#guard ((genEnv [0, 1, 1, 0]).bind fun ctx => termTy sig ctx.tyEnv (.var 0)) = some .nat

/-- `x = succeed 1; provide(Layer.effect(greet, BODY), service greet)`, over the application of
`Test/Program/SketchControls.lean`: a layer under an environment that is not empty. -/
def layered (body : NativeEff) : NativeEff :=
  .bind (.succeed (.lit (.nat 1)))
    (.provideLayer (.effect greetKey body) false (.service greetKey))

/-- The environment at an address of `layered (succeed "hi")`. -/
def layerEnv (path : List Nat) : Option NodeEnv :=
  (Node.eff (layered (.succeed (.lit (.str "hi"))))).envAt app.signature (.env []) path

-- tested: the checker admits the program, and the layer provides what its body requires
#guard Checker.check app.signature [] [] (layered (.succeed (.lit (.str "hi")))) =
  .ok ⟨.string, .never, Requirement.empty⟩
-- tested: the provided program reads the variable; the layer reads nothing; its body is typed
-- at the empty environment
#guard layerEnv [1, 1] = some (.env [.nat])
#guard layerEnv [1, 0] = some .closed
#guard layerEnv [1, 0, 0] = some (.env [])
-- red (tested): a layer's body that reads the outer variable is refused, at the body
#guard refusedAt (Checker.check app.signature [] [] (layered (.succeed (.var 0)))) =
  some ([1, 0, 0], "term")

/-! ## Red: an earlier sibling with no type -/

/-- `x = succeed v7; succeed x`: the first child reads a variable that is not in scope. -/
def badFirst : NativeEff := .bind (.succeed (.var 7)) (.succeed (.var 0))

-- red (tested): the child after it has no environment, and so no focus
#guard ((Node.eff badFirst).envAt sig (.env []) [1]).isNone
#guard (focusAt sig [] badFirst [1]).isNone
-- tested: the refused child itself has its environment, and no type
#guard (Node.eff badFirst).envAt sig (.env []) [0] = some (.env [])
#guard (focusAt sig [] badFirst [0]).isNone

/-- `x = succeed 1; succeed v9`: the second child is refused. -/
def badSecond : NativeEff := .bind (.succeed (.lit (.nat 1))) (.succeed (.var 9))

-- tested: the checker refuses the program, and the child before the refused one keeps its
-- focus: the function asks nothing of the program around the focus
#guard refusedAt (Checker.check sig [] [] badSecond) = some ([1], "term")
#guard ((focusAt sig [] badSecond [0]).map fun f => (f.env, f.ty)) = some ([], numberTy)

end Test.Program.FocusControls
