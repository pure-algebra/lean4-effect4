(* Api_engine_inst -- the FAST instance of the generated engine.

     E4_instance.Make (E4_table) (E4_trace) (E4_memo) (E4_buckets) (E4_ppath) (E4_env) (E4_fibers_view)

   What it is: the engine of docs/research/2026-09-08-engine-a1-state.md §5.2, row 3 --
   "`Api_engine.Make(Map carriers)`: proves the CARRIERS are meaning-preserving".  Every
   generated declaration is untouched; only the seven carriers behind the stores' tables,
   `RunMachine.fibers`, `RunMachine.trace`, `MemoMap.entries`, the per-fiber `Dispatcher`,
   `Point.path` and `Point.env` change (the last two are lane G2, docs/research/
   2026-09-08-engine-prof-chain.md: the snoc-shared spine that carries its node, and the
   snoc-shared environment with a cached length).  The fiber table is `E4_fibers_view`, which
   is `E4_table` plus the MAINTAINED completed view (lane G3): `completedExits` is a field
   read rather than a per-step scan of the table.

   The adapter -- the type abbreviations for the fully applied machine and the free-row
   projections of `E4_engine.INSTANCE`, with their behaviours I1-I4 -- is `E4_instance.Make`,
   which `Api_engine_ref` applies to the list twins.

   Depends on: E4_instance (and through it Api_engine, generated), E4_table, E4_trace,
   E4_memo, E4_buckets, E4_ppath, E4_env, E4_fibers_view. *)

include E4_instance.Make (E4_table) (E4_trace) (E4_memo) (E4_buckets) (E4_ppath) (E4_env) (E4_fibers_view)

let name = "Fast"
let carriers = "E4_table / E4_trace / E4_memo / E4_buckets / E4_ppath / E4_env / E4_fibers_view"
