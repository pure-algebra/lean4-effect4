import Effect4.Codegen.Classes
import Effect4.Schema.Bridge
import Effect4.Schema.Modeled

/-! A finite probe: for one sample of each type former, which images of `Ty` exist today and
which read back. Run: `lake env lean docs/research/2026-10-15-type-roundtrip-audit/probes/RoundTrip.lean`.

Columns:
- `ts`: `Types.ofTy` prints a TypeScript type;
- `ts⁻¹`: the checked reader reads that spelling back to the same type (`ReadableTy`), at a
  definition header (`refs := true`) and at an expression's type arguments (`refs := false`);
- `schema⁻¹`: `Ty.ofSchema (Ty.schema t) = some t.normalize`;
- `lean`: `Model.refusal t = none`, a Lean carrier for `Modeled`. -/

open Effect4 Effect4.Program Effect4.Codegen

def samples : List (String × Ty) :=
  [ ("never", .never), ("unknown", .unknown), ("unit", .unit), ("nat", .nat), ("int", .int),
    ("number", .number), ("string", .string), ("bool", .bool), ("lit", .lit "a"),
    ("null", .null), ("undefined", .undefined), ("bytes", .bytes),
    ("handle", .handle "Foo"), ("app", .app "Foo" [.nat]), ("var", .var 0),
    ("option", .option .nat), ("list", .list .nat), ("prod", .prod .nat .string),
    ("tuple3", .tuple [.nat, .string, .bool]), ("map string", .map .string .nat),
    ("map nat", .map .nat .nat),
    ("record", .record [("a", false, .nat), ("b", false, .string)]),
    ("record optional", .record [("a", false, .nat), ("b", true, .string)]),
    ("union of literals", .union (.lit "a") (.lit "b")),
    ("union nat|string", .union .nat .string),
    ("nullable", .union .string .null),
    ("except", .except .string .nat), ("exitOf", .exitOf .nat .string),
    ("causeOf", .causeOf .string), ("fiberOf", .fiberOf .nat .string),
    ("refOf", .refOf .nat), ("deferredOf", .deferredOf .nat .string) ]

def mark (b : Bool) : String := if b then "yes" else "-"

def row (name : String) (t : Ty) : String :=
  let ts := (Types.ofTy t).isSome
  let back := Classes.ReadableTy { refs := true } t
  let backExpr := Classes.ReadableTy {} t
  let sch := decide (Ty.ofSchema (Ty.schema t) = some t.normalize)
  let lean := (Schema.Model.refusal t).getD "yes"
  s!"| {name} | {mark ts} | {mark back} / {mark backExpr} | {mark sch} | {lean} |"

#eval IO.println (String.intercalate "\n"
  ("| type | ts | ts⁻¹ header / expr | schema⁻¹ | lean |" ::
   "| --- | --- | --- | --- | --- |" :: samples.map fun (n, t) => row n t))
