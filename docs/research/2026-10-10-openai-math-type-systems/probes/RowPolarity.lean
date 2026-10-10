import Effect4.Program.Native
import Effect4.Program.AtomInventory
import Effect4.Program.Bounds

/-!
# Probe: the polarity of every template parameter of the tree's rows and atoms

A finite probe against the real declarations. It reads each built-in row (`NativeOp.spelled`,
`NativeOp.row`) and each polymorphic atom scheme (`NativeAtom.all`, `NativeAtom.spec`), and
computes the polarity of each template parameter in the request and in the answer, at the
variance `Ty.sub` reads each head (`src/Effect4/Program/Ty.lean`, `sub`'s arms; `app` at
`Ty.argVariance`).

The census answers one question: at which templates does a smaller request give a smaller
answer? `Bounds.matchArgsB_monotone` makes the bindings smaller; the answer is then smaller
exactly where it reads every parameter covariantly or not at all (the probe `Variance4.lean`,
`least_solution_least_answer`). An answer that reads a parameter invariantly is where
`checker-monotone` cannot hold without a fixed type argument.
-/

open Effect4.Program

namespace Probe2

structure Var4 where
  pos : Bool
  neg : Bool
deriving DecidableEq, Repr

namespace Var4
def bi : Var4 := ⟨false, false⟩
def co : Var4 := ⟨true, false⟩
def contra : Var4 := ⟨false, true⟩
def inv : Var4 := ⟨true, true⟩
instance : Add Var4 := ⟨fun a b => ⟨a.pos || b.pos, a.neg || b.neg⟩⟩
instance : Mul Var4 :=
  ⟨fun a b => ⟨(a.pos && b.pos) || (a.neg && b.neg), (a.pos && b.neg) || (a.neg && b.pos)⟩⟩
def le (a b : Var4) : Bool := (!a.pos || b.pos) && (!a.neg || b.neg)
def show' (v : Var4) : String :=
  match v.pos, v.neg with
  | false, false => "bi"
  | true, false => "co"
  | false, true => "contra"
  | true, true => "inv"
end Var4

open Var4

def ofV3 : Ty.Variance → Var4
  | .co => co
  | .contra => contra
  | .inv => inv

/-! The connector checks: the tree's `Bounds.comp` is the semiring's product, and
`Ty.Variance.select` is the Boolean reading of a variance. -/

def v3s : List Ty.Variance := [.co, .contra, .inv]

#guard v3s.all fun a => v3s.all fun b => ofV3 (Bounds.comp a b) == ofV3 a * ofV3 b

def selectOf (v : Var4) (xy yx : Bool) : Bool := (!v.pos || xy) && (!v.neg || yx)

#guard v3s.all fun v => [true, false].all fun xy => [true, false].all fun yx =>
  Ty.Variance.select v xy yx == selectOf (ofV3 v) xy yx

mutual
/-- The polarity of parameter `i`, at the variance at which `Ty.sub` reads each head. -/
def pol (i : Nat) : Ty → Var4
  | .var j => if i = j then co else bi
  | .option a => pol i a
  | .list a => pol i a
  | .causeOf a => pol i a
  | .prod a b => pol i a + pol i b
  | .except a b => pol i a + pol i b
  | .exitOf a b => pol i a + pol i b
  | .fiberOf a b => pol i a + pol i b
  | .union a b => pol i a + pol i b
  | .refOf a => inv * pol i a
  | .deferredOf a b => inv * (pol i a + pol i b)
  | .map k v => inv * pol i k + pol i v
  | .record fs => polFields i fs
  | .tuple ts => polItems i ts
  | .app n ts => polArgs i n 0 ts
  | _ => bi
def polFields (i : Nat) : List (String × Bool × Ty) → Var4
  | [] => bi
  | (_, _, t) :: rest => pol i t + polFields i rest
def polItems (i : Nat) : List Ty → Var4
  | [] => bi
  | t :: rest => pol i t + polItems i rest
def polArgs (i : Nat) (n : String) (k : Nat) : List Ty → Var4
  | [] => bi
  | t :: rest => ofV3 (Ty.argVariance n k) * pol i t + polArgs i n (k + 1) rest
end

/-- One template: its name, its request columns and its answer. -/
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

def params : List Nat := [0, 1, 2]

/-- A parameter occurs in a template when some column reads it. -/
def occurs (t : Tmpl) (i : Nat) : Bool :=
  (t.request.map (pol i)).any (fun v => v.pos || v.neg) || ((pol i t.answer).pos || (pol i t.answer).neg)

/-- Each parameter that occurs, with its polarity in the request columns and in the answer. -/
def census (t : Tmpl) : List (Nat × String × String) :=
  (params.filter (occurs t)).map fun i =>
    (i, (t.request.foldl (fun acc r => acc + pol i r) bi).show', (pol i t.answer).show')

/-- A template whose answer reads some parameter other than covariantly or not at all. -/
def answerNonCovariant (t : Tmpl) : Bool := params.any fun i => !le (pol i t.answer) co

-- The census: each row's parameters, with their polarity in the request and in the answer.
#eval rowTmpls.map fun t => (t.name, census t)
#eval atomTmpls.map fun t => (t.name, census t)
#eval (rowTmpls ++ atomTmpls).filter answerNonCovariant |>.map (·.name)

/-! ## Witnesses against the real checker

`Ref.make` answers `refOf (var 0)`: an invariant read of a parameter that its request reads
covariantly. A smaller request can then give an unrelated answer. -/

/-- The literal `7`. -/
def lit7 : Term := .lit (.nat 7)

/-! ### Witnesses with controlled types

`x` (level 0) makes the cell and `y` (level 1) is written to it; the cell is level 2. -/

def pWrite : Eff NativeOp :=
  .bind (.perform .refMake (.var 0))
    (.perform .refSet (.app "pair" (.cons (.var 2) (.cons (.var 1) .nil))))

def tyName : Ty → String
  | .nat => "nat" | .int => "int" | .number => "number"
  | .refOf a => s!"Ref<{tyName a}>"
  | t => Ty.renderRaw t

def verdict2 (r : Except TypeRefusal EffTy) : String :=
  match r with
  | .ok t => s!"admitted at {tyName t.answer}"
  | .error e => s!"refused at path {e.path}"

/-- Pairs of environment types for `x` and `y`, with the checker's verdict on `pWrite`. -/
def envs : List (Ty × Ty) :=
  [(.number, .number), (.nat, .number), (.int, .number), (.nat, .int), (.int, .nat), (.nat, .nat)]

#eval envs.map fun (a, b) =>
  (tyName a, tyName b, verdict2 (Checker.check nativeSignature [a, b] [] pWrite))

-- The types of the literal, of `succ`'s answer and of `minus`'s answer.
#eval (Checker.check nativeSignature [] [] (.succeed lit7)).toOption.map (tyName ·.answer)
#eval (Checker.check nativeSignature [] [] (.succeed (.app "succ" (.cons (.lit (.nat 4)) .nil)))).toOption.map (tyName ·.answer)
#eval (Checker.check nativeSignature [] [] (.succeed (.app "minus" (.cons (.lit (.nat 0)) (.cons (.lit (.nat 1)) .nil))))).toOption.map (tyName ·.answer)

/-- `cell = Ref.make(succ(4)); Ref.set(cell, minus(0, 1))`: atoms only, no environment. -/
def pAtoms : Eff NativeOp :=
  .bind (.perform .refMake (.app "succ" (.cons (.lit (.nat 4)) .nil)))
    (.perform .refSet (.app "pair" (.cons (.var 0)
      (.cons (.app "minus" (.cons (.lit (.nat 0)) (.cons (.lit (.nat 1)) .nil))) .nil))))

#eval verdict2 (Checker.check nativeSignature [] [] pAtoms)

end Probe2
