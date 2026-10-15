import OCaml5.Ml.Check
import OCaml5.Ml.Render

open OCaml5.Ml

def one (name : String) (body : Expr) (before : List Decl := []) : Module :=
  { name := name, items := before ++ [.letD false [{ name := "probe", body := body }]] }

def positive : Module := one "positive" (.binop "+" (.int 2) (.int 3))
def wrongType : Module := one "wrong_type" (.binop "+" (.bool true) (.int 1))
def unbound : Module := one "unbound" (.var "missing_value")
def rawScope : Module := one "raw_scope" (.var "missing_value") [.rawD "(* no declarations *)"]
def unknownField : Module := one "unknown_field" (.record [("missing_label", .int 1)])
def holeFill : Module := one "hole_fill" (.hole "probe" (.assertE (.bool false)))

#guard (checkModule positive).isEmpty
#guard (checkModule wrongType).isEmpty
#guard (checkModule unbound).map (·.code) == ["unbound-value"]
#guard (checkModule rawScope).isEmpty
#guard (checkModule unknownField).isEmpty
#guard (checkModule holeFill).isEmpty

def main (args : List String) : IO Unit := do
  let [out] := args | throw (IO.userError "usage: CheckerProbe.lean OUTPUT_DIRECTORY")
  IO.FS.createDirAll out
  for (name, m) in [("positive", positive), ("wrong_type", wrongType),
      ("unbound", unbound), ("raw_scope", rawScope),
      ("unknown_field", unknownField), ("hole_fill", holeFill)] do
    IO.FS.writeFile (System.FilePath.mk out / s!"{name}.ml") (render m)
    IO.println s!"{name}: checker diagnostics = {(checkModule m).map Diag.toLine}"
