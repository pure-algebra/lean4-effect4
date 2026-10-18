(* e4_log.ml — the append-only log as a persistent chunked vector.
   The property list L1-L5 and the measurement are in e4_log.mli.

   The carrier is `Lcnf_array` (ocaml/lcnf), the one owner of the chunked vector: this module's
   The log held that structure until slice 3.2 moved it to that owner, where
   generated code spells Lean's `Array` with it too. Its frozen chunks are what L5 rests on
   (lcnf_array.mli V4). *)

let chunk_size = Lcnf_array.chunk_size

type row = string
type t = row Lcnf_array.t

let empty = Lcnf_array.empty
let length = Lcnf_array.length
let append = Lcnf_array.push
let append_all t rows = List.fold_left Lcnf_array.push t rows
let get = Lcnf_array.get
let slice = Lcnf_array.slice
let fold = Lcnf_array.fold
let to_list = Lcnf_array.to_list
let of_list = Lcnf_array.of_list
