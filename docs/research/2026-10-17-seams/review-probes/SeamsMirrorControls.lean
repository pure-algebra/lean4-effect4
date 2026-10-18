import Conform.Manifest.Readers

/-!
# Finite controls for the K0 mirror-reader repair

Scope: the OCaml match-arm grammar at qualified `Ty` constructors.
Consumer: the K0 cut review, before changing mirror keys and prefixes.
Evidence: finite reader evaluations and reads of current generated OCaml files.
These controls establish neither generator correctness nor full mirror conformance.
-/

namespace SeamsMirrorControls

open Conform.Manifest

-- Changing the key to the current header still refuses the separate `function` line.
#guard (ocamlMatchArms
  "let ctor_index_ty : Ty.t -> int =\n  function\n    | Ty.Never -> 0\n    | Ty.Nat -> 2\n"
  "let ctor_index_ty : Ty.t -> int =").toOption.isNone

-- The existing grammar reads `match`, but truncates both qualified constructor names.
#guard (ocamlMatchArms
  "let rec json_ty (v : Ty.t) : Eff_json_text.t =\n  match v with\n    | Ty.Never -> x\n    | Ty.Nat -> y\n"
  "let rec json_ty (v : Ty.t) : Eff_json_text.t =").toOption == some #["Ty", "Ty"]

-- Moving `function` onto the header fixes only the first defect.
#guard (ocamlMatchArms
  "let ctor_index_ty : Ty.t -> int = function\n    | Ty.Never -> 0\n    | Ty.Nat -> 2\n"
  "let ctor_index_ty : Ty.t -> int = function").toOption == some #["Ty", "Ty"]

#guard leadingIdent "Ty.Nat" = "Ty"
#guard !(leadingIdent "Ty.Nat").startsWith "Ty."

-- A control for the grammar it currently supports.
#guard (ocamlMatchArms
  "let f = function\n  | Never -> 0\n  | Nat -> 2\n"
  "let f = function").toOption == some #["Never", "Nat"]

#eval do
  let text ← IO.FS.readFile "ocaml/eff/eff_ctors.ml"
  IO.println (reprStr (ocamlMatchArms text "let ctor_index_ty : Ty.t -> int ="))
  IO.println (reprStr (ocamlMatchArms text "let ctor_name_ty : Ty.t -> string ="))

#eval do
  let text ← IO.FS.readFile "ocaml/eff/eff_json.ml"
  IO.println (reprStr (ocamlMatchArms text
    "let rec json_ty (v : Ty.t) : Eff_json_text.t ="))

#eval do
  let text ← IO.FS.readFile "ocaml/eff/eff_wire.ml"
  IO.println (reprStr (ocamlMatchArms text
    "let rec emit_ty (b : Eff_frame.writer) (v : Ty.t) : unit ="))

end SeamsMirrorControls
