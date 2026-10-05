import OCaml5.Lcnf.Translate
import OCaml5.Lcnf.Dump
import OCaml5.Ml.Render
import Conform.Effect4.LcnfMl

/-! A probe of binder capture in the builtin expansions of `OCaml5.Lcnf.Translate`.
Each `…Cap` definition names one binder as the expansion names its own temporary. Each `…Ok`
definition is the same definition with an ordinary name. The probe prints the mono LCNF, the
translated OCaml, Lean's own answer and the answer of the tree's target evaluator. -/

namespace CaptureProbe

@[noinline] def mulCap (x _mula : Nat) : Nat := x * _mula
@[noinline] def mulOk (x y : Nat) : Nat := x * y

@[noinline] def shiftCap (_shift_scale b : Nat) : Nat := _shift_scale <<< b
@[noinline] def shiftOk (a b : Nat) : Nat := a <<< b

@[noinline] def applyTo (f : Nat → Nat) (x : Nat) : Nat := f x
@[noinline] def addCap (_b1 y : Nat) : Nat := applyTo (Nat.add _b1) y
@[noinline] def addOk (a y : Nat) : Nat := applyTo (Nat.add a) y

@[noinline] def containsCap (l : List Nat) (_elem : Nat) : Bool := l.contains _elem
@[noinline] def containsOk (l : List Nat) (a : Nat) : Bool := l.contains a

end CaptureProbe

open Lean Elab Command Compiler LCNF OCaml5 Conform.Lcnf

/-- The Lean answers, computed by Lean. -/
def leanAnswers : List (Name × List Nat × Nat) := [
  (`CaptureProbe.mulCap, [3, 5], CaptureProbe.mulCap 3 5),
  (`CaptureProbe.mulOk, [3, 5], CaptureProbe.mulOk 3 5),
  (`CaptureProbe.shiftCap, [3, 2], CaptureProbe.shiftCap 3 2),
  (`CaptureProbe.shiftOk, [3, 2], CaptureProbe.shiftOk 3 2),
  (`CaptureProbe.addCap, [3, 5], CaptureProbe.addCap 3 5),
  (`CaptureProbe.addOk, [3, 5], CaptureProbe.addOk 3 5)]

run_cmd liftTermElabM do
  let roots : Array Name := #[`CaptureProbe.mulCap, `CaptureProbe.mulOk, `CaptureProbe.shiftCap,
    `CaptureProbe.shiftOk, `CaptureProbe.addCap, `CaptureProbe.addOk,
    `CaptureProbe.containsCap, `CaptureProbe.containsOk]
  -- 1. the mono LCNF of each root, as the compiler stored it
  for r in roots ++ #[`CaptureProbe.applyTo] do
    match ← Lcnf.monoDecl? r with
    | some d => IO.println s!"-- LCNF {r}\n{← Lcnf.ppMono d}\n"
    | none => IO.println s!"-- LCNF {r}: none"
    if let some d ← Lcnf.monoDecl? (r ++ `_redArg) then
      IO.println s!"-- LCNF {r ++ `_redArg}\n{← Lcnf.ppMono d}\n"
  -- 2. the translation of the closure
  let translated ← Lcnf.translateClosure roots
  IO.println s!"-- closure: {translated.decls.size} declarations; todos={translated.todos}; missing={translated.missing}; frontier={translated.frontier}"
  let emitted ← IO.ofExcept (Lcnf.emit translated.decls)
  let module : Ml.Module := { name := "capture_probe", items := emitted }
  IO.println "-- OCAML BEGIN"
  IO.println (Ml.render module)
  IO.println "-- OCAML END"
  -- 3. the target evaluator of the tree on the translated closure
  -- `max_int` is the one free name of the expansions that the evaluator does not know
  let mut binds : Std.HashMap String (List String × Target.Expr) :=
    ({} : Std.HashMap String (List String × Target.Expr)).insert "max_int" ([], .int 4611686018427387903)
  for decl in translated.decls do
    match Conform.Effect4.LcnfMl.ofBind decl.bind with
    | .ok (name, ps, body) => binds := binds.insert name (ps, body)
    | .error why => IO.println s!"-- target reader refuses {decl.leanName}: {why}"
  let prog : Target.Program := { binds, pe := { word := { bits := 63 } } }
  for (n, args, lean) in leanAnswers do
    let out := Target.runT prog 4000 (Lcnf.globalName n) (args.toArray.map fun a => Target.TValue.int (Int.ofNat a))
    IO.println s!"RESULT\t{n}\t{args}\tlean={lean}\ttarget={out.render}"
