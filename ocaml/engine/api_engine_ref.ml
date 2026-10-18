(* Api_engine_ref -- the REFERENCE instance of the generated engine: the same generated
   bodies over Lean's own list carriers.

     E4_instance.Make (E4_table_list) (E4_trace_list) (E4_memo_list) (E4_buckets_list) (E4_ppath_list) (E4_env_list) (E4_fibers_view_list)

   What it is: the engine of docs/research/2026-09-08-engine-a1-state.md §5.2, row 2 --
   "proves the SEAM is meaning-preserving: same generated bodies, list carriers".  Every
   carrier here reproduces the Lean definition operation for operation (`find?`, `map`, `++`,
   `set`, the duplicate the memo world appends, `tasks ++ [task]`), so a divergence between
   this instance and `Api_engine_inst` is a CARRIER law, never an extern row, and a
   divergence between this instance and `Api_gen.api_run` is an extern row, never a carrier.

   It is deliberately slow.  It is not benched except as the baseline.

   The adapter is `E4_instance.Make`, the functor `Api_engine_inst` applies too, so the two
   instances differ in their carriers and in nothing else.

   Depends on: E4_instance (and through it Api_engine, generated), E4_table_list,
   E4_trace_list, E4_memo_list, E4_buckets_list, E4_ppath_list, E4_env_list,
   E4_fibers_view_list -- whose completed is Lean's filterMap WALK, not a maintained view, so
   Ref vs Fast is exactly the question lane G3's view has to answer. *)

include
  E4_instance.Make (E4_table_list) (E4_trace_list) (E4_memo_list) (E4_buckets_list)
    (E4_ppath_list)
    (E4_env_list)
    (E4_fibers_view_list)

let name = "Ref"

let carriers =
  "E4_table_list / E4_trace_list / E4_memo_list / E4_buckets_list / E4_ppath_list / \
   E4_env_list / E4_fibers_view_list"
;;
