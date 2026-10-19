import Conform.Manifest.Readers

/-! K0 finite controls for the generated OCaml constructor readers.
The controls exercise qualified names, standalone headers, and malformed input.
They establish neither generator correctness nor whole-program conformance. -/

namespace Test.Codegen.MirrorReaders
open Conform.Manifest

#guard (ocamlMatchArms
  "let f : Ty.t -> int =\n  function\n    | Ty.Never -> 0\n    | Ty.Nat -> 2\n"
  "let f : Ty.t -> int =").toOption == some #["Ty.Never", "Ty.Nat"]
#guard (ocamlMatchArms
  "let f =\n  match v with\n    | Ty.Never -> x\n    | Ty.Nat -> y\n"
  "let f =").toOption == some #["Ty.Never", "Ty.Nat"]
#guard (ocamlMatchArms "let f = function\n  | Never -> 0\n  | Nat -> 2\n"
  "let f = function").toOption == some #["Never", "Nat"]
#guard (ocamlMatchArms "let f = function\n  | _ -> 0\n" "let f = function").toOption.isNone
#guard (ocamlMatchArms "let f = function\n  | Ty..Nat -> 0\n" "let f = function").toOption.isNone
#guard (ocamlMatchArms "let f =\n  function\n  function\n  | Ty.Nat -> 0\n"
  "let f =").toOption.isNone
#guard (ocamlCtorNames "let ctor_names_ty : string list =\n  [\"never\"; \"nat\"]\n"
  "ty").toOption == some #["never", "nat"]
#guard (ocamlCtorNames "let ctor_names_ty : string list = [\"never\"; \"nat\"]\n"
  "ty").toOption == some #["never", "nat"]
#guard (ocamlCtorNames "let ctor_names_ty : string list =\n  [unquoted]\n"
  "ty").toOption.isNone

-- Read the current generated files, against their separately emitted constructor-name list.
#eval do
  let ctors ← IO.FS.readFile "ocaml/eff/eff_ctors.ml"
  let names ← match ocamlCtorNames ctors "ty" with
    | .ok names => pure names
    | .error e => throw (IO.userError e)
  for (path, key) in [
      ("ocaml/eff/eff_ctors.ml", "let ctor_index_ty : Ty.t -> int ="),
      ("ocaml/eff/eff_ctors.ml", "let ctor_name_ty : Ty.t -> string ="),
      ("ocaml/eff/eff_wire.ml", "let rec emit_ty (b : Eff_frame.writer) (v : Ty.t) : unit =")] do
    let text ← IO.FS.readFile path
    match ocamlMatchArms text key with
    | .error e => throw (IO.userError e)
    | .ok arms =>
      let actual := arms.map fun s => Rename.ocamlCtor.apply (dropS s 3)
      unless actual == names do throw (IO.userError s!"constructor mismatch: {path}")
      IO.println s!"PASS {path}: {arms.size} qualified constructors"

end Test.Codegen.MirrorReaders
