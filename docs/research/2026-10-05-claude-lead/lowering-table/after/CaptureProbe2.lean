import OCaml5.Lcnf.Translate
import OCaml5.Lcnf.Dump
import OCaml5.Ml.Render
import Conform.Effect4.LcnfMl

namespace CaptureProbe

@[noinline] def mulCap (x _mula : Nat) : Nat := x * _mula
@[noinline] def mulOk (x y : Nat) : Nat := x * y
@[noinline] def shiftCap (_shift_scale b : Nat) : Nat := _shift_scale <<< b
@[noinline] def shiftOk (a b : Nat) : Nat := a <<< b
@[noinline] def applyTo (f : Nat → Nat) (x : Nat) : Nat := f x
@[noinline] def addCap (_b1 y : Nat) : Nat := applyTo (Nat.add _b1) y
@[noinline] def addOk (a y : Nat) : Nat := applyTo (Nat.add a) y
-- a binder named as a free name of a form: `Nat.sub` is `max 0 (a - b)`
@[noinline] def subCap (max : Nat → Nat → Nat) (a b : Nat) : Nat := max (a - b) b
-- a binder named as a function the prelude defines
@[noinline] def helperCap (lcnf_nat_mul : Nat → Nat → Nat) (a b : Nat) : Nat := lcnf_nat_mul (a * b) b
-- a binder named as a generated declaration that the body calls
@[noinline] def globalCap (capture_probe_apply_to : (Nat → Nat) → Nat → Nat) (y : Nat) : Nat :=
  capture_probe_apply_to (Nat.add 2) (applyTo (Nat.add 1) y)

end CaptureProbe

open Lean Elab Command Compiler LCNF OCaml5 Conform.Lcnf

def leanAnswers : List (Name × List Nat × Nat) := [
  (`CaptureProbe.mulCap, [3, 5], CaptureProbe.mulCap 3 5),
  (`CaptureProbe.mulOk, [3, 5], CaptureProbe.mulOk 3 5),
  (`CaptureProbe.shiftCap, [3, 2], CaptureProbe.shiftCap 3 2),
  (`CaptureProbe.shiftOk, [3, 2], CaptureProbe.shiftOk 3 2),
  (`CaptureProbe.addCap, [3, 5], CaptureProbe.addCap 3 5),
  (`CaptureProbe.addOk, [3, 5], CaptureProbe.addOk 3 5)]

run_cmd liftTermElabM do
  let roots : Array Name := #[`CaptureProbe.mulCap, `CaptureProbe.mulOk, `CaptureProbe.shiftCap,
    `CaptureProbe.shiftOk, `CaptureProbe.addCap, `CaptureProbe.addOk, `CaptureProbe.subCap,
    `CaptureProbe.helperCap, `CaptureProbe.globalCap]
  for r in #[`CaptureProbe.subCap, `CaptureProbe.helperCap, `CaptureProbe.globalCap] do
    match ← Lcnf.monoDecl? r with
    | some d => IO.println s!"-- LCNF {r}\n{← Lcnf.ppMono d}\n"
    | none => IO.println s!"-- LCNF {r}: none"
  let translated ← Lcnf.translateClosure roots
  IO.println s!"-- closure: {translated.decls.size} declarations; todos={translated.todos}; missing={translated.missing}; frontier={translated.frontier}"
  IO.println s!"-- hygiene: {Lcnf.hygieneProblems translated.decls}"
  for d in translated.decls do
    IO.println s!"-- free names of {d.ocamlName}: {d.freeRefs}"
  let emitted ← IO.ofExcept (Lcnf.emit translated.decls)
  let module : Ml.Module := { name := "capture_probe", items := emitted }
  IO.println "-- OCAML BEGIN"
  IO.println (Ml.render module)
  IO.println "-- OCAML END"
  let mut binds : Std.HashMap String (List String × Target.Expr) :=
    ({} : Std.HashMap String (List String × Target.Expr)).insert "max_int" ([], .int 4611686018427387903)
  for s in Lcnf.support do
    match Conform.Effect4.LcnfMl.ofBind s.bind with
    | .ok (name, ps, body) => binds := binds.insert name (ps, body)
    | .error why => IO.println s!"-- target reader refuses support {s.name}: {why}"
  for decl in translated.decls do
    match Conform.Effect4.LcnfMl.ofBind decl.bind with
    | .ok (name, ps, body) => binds := binds.insert name (ps, body)
    | .error why => IO.println s!"-- target reader refuses {decl.leanName}: {why}"
  let prog : Target.Program := { binds, pe := { word := { bits := 63 } } }
  for (n, args, lean) in leanAnswers do
    let out := Target.runT prog 4000 (Lcnf.globalName n) (args.toArray.map fun a => Target.TValue.int (Int.ofNat a))
    IO.println s!"RESULT\t{n}\t{args}\tlean={lean}\ttarget={out.render}"
