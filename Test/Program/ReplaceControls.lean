import Effect4.Laws.Program.Sketch
import Test.Program.SketchControls

/-!
# The replacement law (decisions row 288, point 4): the controls of slice REPLACE

`Laws/Program/Typing/Replace.lean` proves the law: a program of the focus's type stands in the
focus's place, and the whole keeps its type. `Program/Sketch.lean` has the two edits that it is
the law of, `Sketch.fillAt` and `Sketch.omitAt`. These are the fixtures of the study's section
9.7 (`docs/research/2026-10-06-seat-GAP-study.md`), on the example of
`Test/Program/SketchControls.lean`:

    x = succeed 5;  cell = Ref.make(x);  _ = Ref.set(cell, 7);  Ref.get(cell)

* **Green (tested): an omission at each address.** The example has seven addresses of a
  program. At each one, the omission with the hole row that declares the focus's type keeps the
  example's type.
* **Green (tested): fillings of the hole's declared type.** The original first child fills the
  hole, and so does a program that dies first: the type stays, and the hole's row stays.
* **Red (tested): a filling of another type** is refused in the context, at the write.
* **Red (tested): no address of a program.** The two edits answer `none`.
* **Red (tested): the row that declares the answer alone**, under an exit whose value reaches a
  cell. The omitted error flows into a value, and the checker refuses the write. With three
  columns the same omission keeps the type.
* **Red (tested): a focus whose answer is not in normal form.** The checker gives a node the
  raw type of its term, and it reads a hole row in normal form. So the omission changes the
  type of the whole. It is the reason for the two premises on normal form in
  `Sketch.check_omit`.
* **The law at the example (proved).** Two conclusions come from the law and not from an
  evaluation: the omission of the first child, and the filling of the hole. The law's
  environment and type of the focus are existential. Each proof names them through a fact that
  holds in every environment: a literal's type, and a hole's declared type.
-/

set_option autoImplicit false

namespace Test.Program.ReplaceControls

open Effect4 Effect4.Program
open Effect4.Machine.Env (Requirement)
open Conform.Effect4.Typing
open Test.Program.SketchControls

/-- The type of the example: a number, no error, no requirement. -/
def numberTy : EffTy := ⟨.nat, .never, Requirement.empty⟩

/-! ## An omission at each address of the example -/

/-- The check of the example with the sub-program at `path` omitted, under a hole row that
declares the answer `answer`, the error `never` and no requirement. -/
def omitted (path : List Nat) (answer : Ty) : Option (Except TypeRefusal EffTy) :=
  ((original : Sketch).omitAt {} path (Row.hole "h0" answer)).map (·.check)

-- green (tested): the seven addresses of a program, each with the type of its focus
#guard omitted [] .nat = some (.ok numberTy)
#guard omitted [0] .nat = some (.ok numberTy)
#guard omitted [1] .nat = some (.ok numberTy)
#guard omitted [1, 0] (.refOf .nat) = some (.ok numberTy)
#guard omitted [1, 1] .nat = some (.ok numberTy)
#guard omitted [1, 1, 0] (.refOf .nat) = some (.ok numberTy)
#guard omitted [1, 1, 1] .nat = some (.ok numberTy)
-- red (tested): a hole row that declares another type; the context refuses, at the write
#guard (omitted [1, 0] (.refOf .string)).map refusedAt = some (some ([1, 1, 0], "requestNotSubtype"))
-- red (tested): no address of a program; the edit answers `none`
#guard (omitted [9] .nat).isNone
#guard (omitted [0, 0] .nat).isNone

-- tested: the omission appends the hole's row, and the hole stands at the address
#guard ((original : Sketch).omitAt {} [0] (Row.hole "h0" .nat)).map (·.program) =
  some (sketchAt .nat).program
#guard ((original : Sketch).omitAt {} [0] (Row.hole "h0" .nat)).map (·.holes) =
  some (sketchAt .nat).holes

/-! ## Fillings of the hole -/

/-- A program of the type `⟨number, never, ∅⟩` that dies first: a defect, then a loop whose
cursor is declared a number. The loop does not run. -/
def diesFirst : NativeEff :=
  .bind (.failCause (.die (.lit (.str "not written"))))
    (.iterate (some .nat) (.var 0) (.lit (.bool false)) (.var 1) (.var 1) (.succeed (.lit .unit)))

/-- The check of the example's sketch with its hole filled by `q`. -/
def filled (q : NativeEff) : Option (Except TypeRefusal EffTy) :=
  ((sketchAt .nat).fillAt [0] q).map (·.check)

-- tested: the two fillings have the hole's declared type
#guard effTy ({} : SigApp).signature [] (.succeed (.lit (.nat 5))) = some numberTy
#guard effTy ({} : SigApp).signature [] diesFirst = some numberTy
-- green (tested): the original first child fills the hole, and the sketch is the original
#guard filled (.succeed (.lit (.nat 5))) = some (.ok numberTy)
#guard ((sketchAt .nat).fillAt [0] (.succeed (.lit (.nat 5)))).map (·.program) = some original
-- tested: the filled hole's row stays in the hole table
#guard ((sketchAt .nat).fillAt [0] (.succeed (.lit (.nat 5)))).map (·.holes) =
  some (sketchAt .nat).holes
-- green (tested): the program that dies first fills the hole, and the type stays
#guard filled diesFirst = some (.ok numberTy)
-- red (tested): a filling of another type is refused in the context, at the write
#guard (filled (.succeed (.lit (.str "x")))).map refusedAt =
  some (some ([1, 1, 0], "requestNotSubtype"))
-- red (tested): no address of a program
#guard ((sketchAt .nat).fillAt [9] diesFirst).isNone

/-! ## The row that declares the answer alone -/

/-- `fail "boom"`: no answer, and the error `string`. -/
def boom : NativeEff := .fail (.lit (.str "boom"))

/-- `a = exit(BODY); cell = Ref.make(a); b = exit(fail "boom"); Ref.set(cell, b)`: the exit of
the body is a value, and it reaches a cell. -/
def exits (body : NativeEff) : NativeEff :=
  .bind (.exit body)
    (.bind (.perform .refMake (.var 0))
      (.bind (.exit boom)
        (.perform .refSet (pairT (.var 1) (.var 2)))))

/-- The check of `exits boom` with its body omitted under `row`. The body is at `[0, 0]`. -/
def exitsOmitted (row : Row) : Option (Except TypeRefusal EffTy) :=
  (Sketch.omitAt (exits boom : Sketch) {} [0, 0] row).map (·.check)

-- tested: the body's type is `⟨never, string, ∅⟩`, and the checker admits the program
#guard effTy ({} : SigApp).signature [] boom = some ⟨.never, .string, Requirement.empty⟩
#guard (Sketch.check (exits boom : Sketch)).toOption.isSome
-- green (tested): three columns; the omission keeps the type of the whole
#guard exitsOmitted (Row.hole "h0" .never .string) = some (Sketch.check (exits boom : Sketch))
-- red (tested): the answer alone; the exit's type changes, and the write is refused
#guard (exitsOmitted (Row.hole "h0" .never)).map refusedAt =
  some (some ([1, 1, 1], "requestNotSubtype"))

/-- `BODY; succeed 1`: the body's error reaches no value. -/
def thenOne (body : NativeEff) : NativeEff := .bind body (.succeed (.lit (.nat 1)))

-- tested: outside a handler, an exit and a fork, the answer-only row keeps the answer and
-- loses the omitted error; it is the row of the views of an error (decisions row 288, point 3)
#guard Sketch.check (thenOne boom : Sketch) = .ok ⟨.nat, .string, Requirement.empty⟩
#guard (Sketch.omitAt (thenOne boom : Sketch) {} [0] (Row.hole "h0" .never)).map (·.check) =
  some (.ok ⟨.nat, .never, Requirement.empty⟩)

/-! ## Red: a focus whose answer is not in normal form -/

/-- `if true then 1 else "a"`: a number or a string. -/
def numberOrString : NativeEff :=
  .select (.lit (.bool true)) .bool (.succeed (.lit (.nat 1))) (.succeed (.lit (.str "a")))

/-- The focus: `succeed (pair x 7)`, with `x` a number or a string. -/
def pairFocus : NativeEff := .succeed (pairT (.var 0) (.lit (.nat 7)))

/-- The focus's answer as the checker gives it: the raw type of the term. -/
def rawPair : Ty := .prod (.union .nat .string) .nat

/-- `x = numberOrString; p = FOCUS; succeed p`: the context keeps the focus's answer. -/
def keepsPair (focus : NativeEff) : NativeEff :=
  .bind numberOrString (.bind focus (.succeed (.var 1)))

/-- `x = numberOrString; p = FOCUS; succeed (fst p)`: the context reads a component. -/
def readsFirst (focus : NativeEff) : NativeEff :=
  .bind numberOrString (.bind focus (.succeed (.app "fst" (.cons (.var 1) .nil))))

-- tested: the focus's answer is the raw pair, and the raw pair is not its own normal form
#guard effTy ({} : SigApp).signature [.union .nat .string] pairFocus =
  some ⟨rawPair, .never, Requirement.empty⟩
#guard rawPair.normalize != rawPair
#guard Sketch.check (keepsPair pairFocus : Sketch) = .ok ⟨rawPair, .never, Requirement.empty⟩
-- red (tested): the hole declares the focus's own answer, and the checker reads the row in
-- normal form; the sketch's answer is the normal form, and not the original's answer
#guard (Sketch.omitAt (keepsPair pairFocus : Sketch) {} [1, 0] (Row.hole "h0" rawPair)).map (·.check) =
  some (.ok ⟨rawPair.normalize, .never, Requirement.empty⟩)
-- tested: a context that reads a component gives one type for both
#guard (Sketch.omitAt (readsFirst pairFocus : Sketch) {} [1, 0] (Row.hole "h0" rawPair)).map (·.check) =
  some (Sketch.check (readsFirst pairFocus : Sketch))

/-! ## The law at the example

The law's environment and type of the focus are existential (`Sketch.check_fill`,
`Sketch.check_omit`). A function that computes them is slice TRACE's. Two conclusions are still
in reach, because the focus's type holds in every environment: a literal, and a hole. -/

/-- The checker admits the example as a sketch, at a number. -/
theorem original_checked : Sketch.check (original : Sketch) = .ok numberTy := by
  decide +kernel

/-- **The omission of the first child, by the law (proved).** The focus is `succeed 5`, which
has the type `⟨number, never, ∅⟩` in every environment. So the law's type is that one, and the
omission with the hole row that declares it exists and keeps the example's type. -/
theorem omit_first_child :
    ∃ s', (original : Sketch).omitAt {} [0] (Row.hole "h0" .nat) = some s' ∧
      s'.check = .ok numberTy := by
  obtain ⟨env, t, hq, homit⟩ := Sketch.check_omit (original : Sketch) {} original_checked
    (path := [0]) (q := .succeed (.lit (.nat 5))) rfl
  have hlit : Checker.check (({} : SigApp).withHoles []).signature env []
      (.succeed (.lit (.nat 5))) = .ok numberTy := rfl
  have ht : numberTy = t := Except.ok.inj (hlit.symm.trans (hq []))
  subst ht
  exact homit "h0" rfl rfl (by decide +kernel) (by decide +kernel)
    ((Formation.check_eq_none_iff _).mp (by decide +kernel))

/-- The checker admits the example's sketch, at a number. -/
theorem sketch_checked : (sketchAt .nat).check = .ok numberTy := by
  decide +kernel

/-- **The filling of the hole, by the law (proved).** The focus is hole 0, which has its
declared type in every environment (`Sketch.hole_hasTy`). So the law's type is the declared one.
The filling `succeed 5` has that type in every environment, and the law checks nothing else: the
filled sketch exists and keeps the type. -/
theorem fill_the_hole :
    ∃ s', (sketchAt .nat).fillAt [0] (.succeed (.lit (.nat 5))) = some s' ∧
      s'.check = .ok numberTy := by
  obtain ⟨env, t, hq, hfill⟩ := Sketch.check_fill (sketchAt .nat) {} sketch_checked
    (path := [0]) (q := Sketch.hole {} 0) rfl
  have hhole : Checker.check (({} : SigApp).withHoles (sketchAt .nat).holes).signature env []
      (Sketch.hole {} 0) = .ok numberTy :=
    check_complete _ _ env _ (Sketch.hole_hasTy {} [Row.hole "h0" .nat] 0 env rfl rfl rfl
      ((Formation.check_eq_none_iff _).mp (by decide +kernel))) []
  have ht : numberTy = t := Except.ok.inj (hhole.symm.trans (hq []))
  subst ht
  obtain ⟨s', hs', hT⟩ := hfill [] (q' := .succeed (.lit (.nat 5))) (pq := []) rfl
  exact ⟨s', by simpa only [List.append_nil] using hs', hT⟩

end Test.Program.ReplaceControls
