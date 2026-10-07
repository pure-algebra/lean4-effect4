import Effect4.Program.Typing.Table
import Effect4.Program.Sketch
import Effect4.Laws.Program.Typing.Table
import Effect4.Laws.Program.Typing.Sound
import Test.Program.FocusControls

/-!
# The address table, the list of refusals and the slot table (slice TABLE): the controls

`Program/Typing/Table.lean` computes the address table of a program, its distinct refusals and
the environment of a term slot. `Laws/Program/Typing/Table.lean` proves the laws. These are
the finite evaluations, on the example of `Test/Program/SketchControls.lean` and on four small
programs:

    x = succeed 5;  cell = Ref.make(x);  _ = Ref.set(cell, 7);  Ref.get(cell)

* **Green (tested): the table of the example.** Seven addresses, in the fold's order. Each
  entry agrees with the focus function, and the list of refusals is empty.
* **Red (tested): two refusals.** A body with two refused statements has two refusals, and
  `explain` answers the first. Every entry has an environment, since a statement gives the
  next one its own. The seven addresses with no answer are no addresses of a program.
* **Red (tested): a refused sibling.** In a chain of `bind`, the program after a refused one
  is not reached: it has no environment, and the list has one refusal.
* **Tested: the frame of an edit.** A filling of the focus's type changes no entry outside the
  focus. A filling of another type changes an entry outside it. No theorem states the frame
  (the proposed claim `edit-frame`).
* **Tested: the table of a sketch** is the table of its program at its signature.
* **Tested: the slot table.** At each of the five slots, the environment of the slot and the
  type of the slot's term there. A node with no such slot answers none, and so does a slot
  whose rule reads a refused body.
* **Green (proved): the slot law at an operation's own term**, at `Ref.update`.

No line restates a theorem, and no line prints axioms.
-/

set_option autoImplicit false

namespace Test.Program.TableControls

open Effect4 Effect4.Program
open Effect4.Machine.Env (Requirement)
open Conform.Effect4.Typing
open Test.Program.SketchControls Test.Program.FocusControls

/-- An entry, as values that `#guard` compares. -/
def Entry.shape (e : Table.Entry) :
    List Nat × Option NodeEnv × Option (Option EffTy) × Option TypeRefusal :=
  (e.path, e.env, e.result.map Except.toOption, e.result.bind Checker.refusal)

/-- The path and the reason's name of each refusal. -/
def named (rs : List TypeRefusal) : List (List Nat × String) :=
  rs.map fun w => (w.path, w.reason.head)

/-- A refused program: `Ref.get` of a number. -/
def bad : NativeEff := .perform .refGet (.lit (.nat 5))

/-- A generator body with two refused statements. -/
def twoBad : NativeEff :=
  .gen (.cons (.yieldDiscard bad) (.cons (.yieldDiscard bad) (.cons (.ret (.lit (.nat 1))) .nil)))

/-- A chain of `bind` whose first program is refused. -/
def chained : NativeEff := .bind bad (.bind bad (.succeed (.var 0)))

/-- The example with the sub-program at `path` replaced by `q`. -/
def edited (path : List Nat) (q : NativeEff) : Option NativeEff :=
  ((Node.eff original).replaceAt path (.eff q)).bind Node.eff?

/-- The entries outside the focus at `path`. -/
def outside (path : List Nat) (rows : List Table.Entry) :=
  (rows.filter fun e => !path.isPrefixOf e.path).map Entry.shape

/-! ## The table of the example -/

-- green (tested): the seven addresses, in the fold's order
#guard Node.addresses (.eff original) = [[], [0], [1], [1, 0], [1, 1], [1, 1, 0], [1, 1, 1]]
-- green (tested): each entry agrees with the focus function
#guard (table sig [] original).all fun e =>
  (e.env.map NodeEnv.tyEnv, e.result.bind Except.toOption) =
    (((original : Sketch).focusAt {} e.path).map (·.env),
      ((original : Sketch).focusAt {} e.path).map (·.ty))
#guard refusals sig [] original = []

/-! ## Two refusals, and a refused sibling -/

-- red (tested): `explain` answers the first refusal, and the list holds both
#guard named (explain sig [] twoBad).toList = [([0, 0, 0], "requestNotSubtype")]
#guard named (refusals sig [] twoBad) =
  [([0, 0, 0], "requestNotSubtype"), ([0, 1, 0, 0], "requestNotSubtype")]
#guard (refusals sig [] twoBad).head? = explain sig [] twoBad
-- tested: every entry has an environment, and seven addresses are no addresses of a program
#guard (table sig [] twoBad).all fun e => e.env.isSome
#guard ((table sig [] twoBad).filter fun e => e.result.isNone).map (·.path) =
  [[0], [0, 0], [0, 1], [0, 1, 0], [0, 1, 1], [0, 1, 1, 0], [0, 1, 1, 1]]

-- red (tested): the programs after a refused sibling are not reached
#guard named (refusals sig [] chained) = [([0], "requestNotSubtype")]
#guard ((table sig [] chained).filter fun e => e.env.isNone).map (·.path) = [[1], [1, 0], [1, 1]]

/-! ## The frame of an edit -/

-- tested: a filling of the focus's type changes no entry outside the focus
#guard (edited [0] (.bind (.succeed (.lit (.nat 1))) (.succeed (.lit (.nat 6))))).all fun e' =>
  outside [0] (table sig [] e') = outside [0] (table sig [] original)
#guard (edited [0] (.bind (.succeed (.lit (.nat 1))) (.succeed (.lit (.nat 6))))).all fun e' =>
  (Node.addresses (.eff e')).length = 9
-- red (tested): a filling of another type changes an entry outside the focus
#guard (edited [0] (.succeed (.lit (.str "x")))).all fun e' =>
  outside [0] (table sig [] e') != outside [0] (table sig [] original)
#guard (edited [0] (.succeed (.lit (.str "x")))).all fun e' =>
  named (refusals sig [] e') = [([1, 1, 0], "requestNotSubtype")]
#guard (edited [0] (.succeed (.lit (.str "x")))).all fun e' =>
  ((table sig [] e').filter fun e => e.env.isNone).map (·.path) = [[1, 1, 1]]

/-! ## The table of a sketch -/

#guard (original : Sketch).table == table sig [] original
#guard (original : Sketch).refusals == []
#guard (twoBad : Sketch).refusals == refusals sig [] twoBad

/-! ## The slot table -/

/-- The environment of a slot of a program, and the type of the slot's term there. -/
def slotOf (env : TyEnv) (p : NativeEff) (slot : ExtSlot) : Option (TyEnv × Option Ty) :=
  ((Node.eff p).extSlotEnv sig env slot).map fun env' =>
    (env', ((Node.eff p).extSlotTerm sig slot).bind (termTy sig env'))

/-- `catchIf` whose test reads the caught error. -/
def caught : NativeEff :=
  .catchIf (.lit (.bool true)) (.fail (.lit (.str "err"))) (.succeed (.lit (.nat 1)))

/-- `iterate` whose step reads the body's answer and whose result reads the cursor. -/
def loop : NativeEff :=
  .iterate none (.lit (.nat 0)) (.lit (.bool true)) (.var 1) (.var 0) (.succeed (.var 0))

/-- `Ref.update(cell, current => current)`: the operation's own term reads its current value. -/
def update : NativeEff := .perform (.refUpdateWith (.var 1)) (.var 0)

-- tested: the test of `catchIf` reads the body's error
#guard slotOf [] caught .catchIfTest = some ([.string], some .bool)
-- tested: the test and the result of `iterate` read the cursor; its step reads the body's
-- answer too
#guard slotOf [] loop .iterateTest = some ([.nat], some .bool)
#guard slotOf [] loop .iterateStep = some ([.nat, .nat], some .nat)
#guard slotOf [] loop .iterateResult = some ([.nat], some .nat)
-- tested: an operation's own term reads its current value, at the instance of the parameter
#guard slotOf [.refOf .nat] update .opTerm = some ([.refOf .nat, .nat], some .nat)
-- red (tested): a node with no such slot answers none
#guard slotOf [] caught .iterateStep = none
#guard slotOf [.refOf .nat] (.perform .refGet (.var 0)) .opTerm = none
-- red (tested): the slot's rule reads a refused body, and the slot has no environment
#guard slotOf [] (.catchIf (.lit (.bool true)) bad (.succeed (.lit (.nat 1)))) .catchIfTest = none

/-- **The slot law at an operation's own term (proved, by the law).** `Ref.update` is typed at a
cell of numbers, so its term has a type at the slot's environment. -/
theorem update_term_typed :
    ∃ env' ty, (Node.eff update).extSlotEnv sig [.refOf .nat] .opTerm = some env' ∧
      termTy sig env' (.var 1) = some ty :=
  hasTy_extSlotEnv
    (effTy_sound sig update [.refOf .nat] ⟨.unit, .never, Requirement.empty⟩ (by decide +kernel))
    rfl

end Test.Program.TableControls
