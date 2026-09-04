(* Registers P5's generated corpus (spike P5 round four,
   `ocaml/probes/fuzz/corpus/corpus_fixture.ml`) as the avatar's `fuzz` family. Compiled
   only into `avatar-fuzz.byte`, so the avatar's own binary never depends on a file another
   spike regenerates. *)
let () = Deep_fibers.fuzz_programs := Corpus_fixture.programs
