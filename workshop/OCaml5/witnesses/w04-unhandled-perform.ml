(* Witness 04: perform at the root. No parent stack, so Unhandled is raised on the
   performer itself (interp.c:1327-1332; amd64.S:897-905, label 112) and a try in the
   performer catches it. Transcribes `unhandled` of effects5_capabilities.ml:51-54.
   No continuation is taken on this route -- contrast witness 08. *)
open Effect
type _ Effect.t += Outer : int Effect.t
let row s = print_string s; print_newline ()
let () =
  let rejected =
    try
      row "perform\tOuter";
      ignore (perform Outer);
      row "unreachable";
      0
    with Unhandled Outer -> row "caught\tUnhandled"; 1
  in
  row (Printf.sprintf "value\t%d" rejected)
