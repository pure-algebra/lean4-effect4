(* join_escape.ml -- the red control of warning 55: a [@local always] function that escapes.

   What it is: the shape no join point of the LCNF route may take. OCaml compiles a local
   function to a static jump only when every use is a full application in one tail scope
   (Simplif.simplify_local_functions, lambda/simplif.ml of OCaml 5.1.1). [join] is returned,
   so it is a closure, and [@local always] asks for what cannot be. The rule in the dune file
   beside this one compiles it with ocamlopt under -w @55, the flag every stanza that compiles
   LCNF-made code carries, and passes only when ocamlopt refuses it with the message of
   join_escape.expected. No library or executable holds this module.
   Depends on: nothing.

   Properties:
   J1  ocamlopt -w @55 refuses this file, by warning 55 at [join].     tested (dune test gen)
   J2  The rule fails when ocamlopt accepts the file (exit 0) or refuses it with another
       message.                                                        by construction (dune) *)

let escape x =
  let[@local always] join y = x + y in
  join, join
;;
