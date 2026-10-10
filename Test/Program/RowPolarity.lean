import Effect4.Laws.Program.Polarity
import Effect4.Program.Native
import Effect4.Program.AtomInventory

/-!
# Test.Program.RowPolarity — the answer polarity of every built-in row and atom scheme

Slice VAR-3 of `docs/research/2026-10-10-openai-math-type-systems/brief.md`. A finite evaluation
over the built-in tables: each row's template (`NativeOp.spelled`, `NativeOp.row`) and each
polymorphic atom scheme (`NativeAtom.all`, `NativeAtom.spec`), read with `Ty.polarity` at
`Ty.sub`'s reading (`HeadReading.sub`, `src/Effect4/Program/Polarity.lean`).

A smaller request gives smaller bindings (`Bounds.matchArgsB_monotone`). The answer is then
smaller exactly where it reads every parameter at co or bi (the probe's
`least_solution_least_answer`). So the census is `checker-monotone`'s hypothesis at the rows
(`row-answer-polarity`): it holds at every built-in row and atom scheme except two, `Ref.make`
and `Ref.set`, which read their parameter invariantly in the answer.

The controls: the checker's verdicts on `cell = Ref.make(x); Ref.set(cell, y)` by the types of
`x` and `y` (the environment half of `checker-monotone` fails at `refMake` at an ordinary type),
and the atoms-only program that tsgo 7 accepts against rc.112 and the checker refuses
(`docs/research/2026-10-10-openai-math-type-systems/probes/ts/refcell.ts`; register line
`E4-POL-CE-001`). Placement: concept `subtyping-algebra`, the proposed claim `checker-monotone`
(`tools/ProofGraph/Registry.lean`). The battery establishes nothing at a supplied row table or a
definition block.
-/

set_option autoImplicit false

namespace Test.Program.RowPolarity

open Effect4.Program

/-- A template: its name, its request columns and its answer. -/
structure Tmpl where
  name : String
  request : List Ty
  answer : Ty

def rowTmpls : List Tmpl :=
  NativeOp.spelled.map fun op => ⟨op.row.name, [op.row.request], op.row.answer⟩

def atomTmpls : List Tmpl :=
  NativeAtom.all.filterMap fun a =>
    match (NativeAtom.spec a).scheme with
    | .poly ps ans => some ⟨(NativeAtom.row a).name, ps, ans⟩
    | _ => none

/-- The template parameters the built-in tables use. -/
def params : List Nat := [0, 1, 2]

/-- A template whose answer reads some parameter other than co or bi. -/
def answerAboveCo (t : Tmpl) : Bool :=
  params.any fun i => !Var4.le (t.answer.polarity .sub i) .co

-- The census: exactly two rows read a parameter above co in their answer, and no atom scheme.
#guard (rowTmpls.filter answerAboveCo).map (·.name) == ["refMake", "refSet"]
#guard (atomTmpls.filter answerAboveCo).isEmpty
-- The tables are not empty, so the census is no vacuous pass.
#guard rowTmpls.length > 20 && atomTmpls.length > 5
-- `refMake` reads its parameter co in the request and inv in the answer.
#guard (rowTmpls.find? (·.name == "refMake")).map (fun t =>
  ((t.request.map (·.polarity .sub 0)), t.answer.polarity .sub 0)) ==
  some ([Var4.co], Var4.inv)

/-! ## The checker's verdicts on the cell (controls) -/

/-- `x` (level 0) makes the cell and `y` (level 1) is written to it; the cell is level 2. -/
def pWrite : Eff NativeOp :=
  .bind (.perform .refMake (.var 0))
    (.perform .refSet (.app "pair" (.cons (.var 2) (.cons (.var 1) .nil))))

def verdict (env : List Ty) : Option (List Nat) :=
  match Checker.check nativeSignature env [] pWrite with
  | .ok _ => none
  | .error e => some e.path

-- `nat` is below `number`, so the second environment is pointwise below the first, and the
-- checker refuses it: the environment half of `checker-monotone` fails at `Ref.make`.
#guard verdict [.number, .number] == none
#guard verdict [.nat, .number] == some [1]
#guard verdict [.int, .number] == some [1]
#guard verdict [.nat, .int] == some [1]
#guard verdict [.int, .nat] == none
#guard verdict [.nat, .nat] == none

/-- `cell = Ref.make(succ(4)); Ref.set(cell, minus(0, 1))`: atoms only. tsgo 7 admits its print
against rc.112, where both atoms are declared at `number`. -/
def pAtoms : Eff NativeOp :=
  .bind (.perform .refMake (.app "succ" (.cons (.lit (.nat 4)) .nil)))
    (.perform .refSet (.app "pair" (.cons (.var 0)
      (.cons (.app "minus" (.cons (.lit (.nat 0)) (.cons (.lit (.nat 1)) .nil))) .nil))))

#guard (match Checker.check nativeSignature [] [] pAtoms with
  | .ok _ => none
  | .error e => some e.path) == some [1]

end Test.Program.RowPolarity
