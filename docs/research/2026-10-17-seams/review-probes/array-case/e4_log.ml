(* e4_log.ml — the append-only log as a persistent chunked vector.
   The property list L1-L5 and the measurement are in e4_log.mli.

   The carrier is `Lcnf_array` (ocaml/lcnf), the one owner of the chunked vector: this module's
   `Vec` was that structure until slice 3.2 of the OCaml estate refactor moved it there, where
   generated code spells Lean's `Array` with it too. Its frozen chunks are what L5 rests on
   (lcnf_array.mli V4). *)

module Vec = Lcnf_array

let chunk_size = Lcnf_array.chunk_size

type row = string
type t = row Vec.t

let empty = Vec.empty
let length = Vec.length
let append = Vec.push
let append_all t rows = List.fold_left Vec.push t rows
let get = Vec.get
let slice = Vec.slice
let fold = Vec.fold
let to_list = Vec.to_list
let of_list = Vec.of_list
