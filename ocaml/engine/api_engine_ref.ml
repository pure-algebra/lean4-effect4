(* Api_engine_ref -- the REFERENCE instance of the generated engine: the same generated
   bodies over Lean's own list carriers.

     Api_engine.Make (E4_table_list) (E4_trace_list) (E4_memo_list) (E4_buckets_list) (E4_ppath_list) (E4_env_list) (E4_fibers_view_list)

   What it is: the engine of docs/research/2026-09-08-engine-a1-state.md §5.2, row 2 --
   "proves the SEAM is meaning-preserving: same generated bodies, list carriers".  Every
   carrier here reproduces the Lean definition operation for operation (`find?`, `map`, `++`,
   `set`, the duplicate the memo world appends, `tasks ++ [task]`), so a divergence between
   this instance and `Api_engine_inst` is a CARRIER law, never an extern row, and a
   divergence between this instance and `Api_gen.api_run` is an extern row, never a carrier.

   It is deliberately slow.  It is not benched except as the baseline.

   This file is `api_engine_inst.ml` line for line, with seven module names changed; the two
   are kept side by side rather than generated from one source because `ocaml/engine/dune`
   belongs to another lane and a copy rule cannot be added to it from here.  Any edit to one
   must be made to the other -- `test_engine.ml` runs BOTH through the same `E4_engine.Make`,
   so a projection that drifts shows up as a differential failure, not as silence.

   Depends on: Api_engine (generated), E4_table_list, E4_trace_list, E4_memo_list,
   E4_buckets_list, E4_ppath_list, E4_env_list, E4_fibers_view_list -- whose completed is
   Lean's filterMap WALK, not a maintained view, so Ref vs Fast is exactly the question lane
   G3's view has to answer. *)

include Api_engine.Make (E4_table_list) (E4_trace_list) (E4_memo_list) (E4_buckets_list) (E4_ppath_list) (E4_env_list) (E4_fibers_view_list)

let name = "Ref"
let carriers = "E4_table_list / E4_trace_list / E4_memo_list / E4_buckets_list / E4_ppath_list / E4_env_list / E4_fibers_view_list"

(* -- the fully applied machine ------------------------------------------------------- *)

type nu = eff_name
type s = eff_thunk
type prim_ = (nu, s, val_, err, defect, fiber_id, unit) prim
type ffiber = (nu, s, val_, err, defect, fiber_id, unit) frame_fiber
type fevent = (nu, s, val_, err, defect, fiber_id, unit) frame_event

type machine =
  (nu, s, val_, err, defect, fiber_id, unit, ctx, stores, prim_, ffiber, fevent) run_machine

type fiber = (nu, s, val_, err, defect, fiber_id, unit, ctx, prim_, ffiber) run_fiber
type event = (nu, s, val_, err, defect, fiber_id, unit, ctx, prim_, fevent) run_event
type decision = (nu, s, val_, err, defect, fiber_id, unit) run_decision
type interp = (nu, s, val_, err, defect, fiber_id, unit, ctx, stores, prim_) run_interp
type program = native_op eff

(* -- loading and stepping ------------------------------------------------------------- *)

let interp_of (p : program) : interp = program_interp_of p []

let load (p : program) ~(fuel : int) ~(choices : bool list) : machine =
  sh_api_load program_compile empty_ctx stores p fuel choices []

let step (p : program) (i : interp) ~(fuel : int) (m : machine) (d : decision)
  : machine * bool =
  step_decision_state_at_program_replay_checked_from_spec_1 p [] i fuel m d

let run_api (p : program) ~(fuel : int) ~(choices : bool list) : outcome * machine =
  let r = api_run p fuel choices [] [] in
  (r.outcome, r.machine)

(* -- the free rows -------------------------------------------------------------------- *)

let fibers (m : machine) : (fiber_id * fiber) list = E4_fibers_view_list.bindings m.fibers
let fiber_count (m : machine) : int = E4_fibers_view_list.cardinal m.fibers
let trace (m : machine) : event list = E4_trace_list.to_list m.trace
let trace_length (m : machine) : int = E4_trace_list.length m.trace
let stuck_of (m : machine) : stuck option = m.stuck
let armed_of (m : machine) : fiber_id list = m.armed
let next_id (m : machine) : int = m.next_id
let next_token (m : machine) : int = m.next_token
let race_count (m : machine) : int = List.length m.races
let middleware (m : machine) : bool = m.middleware_installed
let finished (m : machine) : bool = sh_machine_finished m

let completed_exits (m : machine)
  : (fiber_id * (val_, err, defect, fiber_id, unit) exit_) list =
  sh_machine_completed_exits m

let stores_of (m : machine) : stores = m.state
let refs (m : machine) : val_ list = E4_table_list.to_list (stores_of m).refs
let next_name (m : machine) : int = (stores_of m).next_name
let due_count (m : machine) : int = List.length (stores_of m).deferreds.due
let cell_count (m : machine) : int = E4_table_list.cardinal (stores_of m).deferreds.cells
let scope_count (m : machine) : int = E4_table_list.cardinal (stores_of m).scopes
let memo_map_count (m : machine) : int = List.length (stores_of m).memo

let memo_paths (m : machine) : (int * int list list) list =
  List.map
    (fun (mm : memo_map) -> (mm.id, List.map fst (E4_memo_list.bindings mm.entries)))
    (stores_of m).memo

(* -- the fiber's own fields ----------------------------------------------------------- *)

let f_id (f : fiber) : fiber_id = f.id
let f_exit (f : fiber) : (val_, err, defect, fiber_id, unit) exit_ option = f.exit_
let f_parked (f : fiber) : parked = f.parked
let f_running (f : fiber) : bool = f.running
let f_finalizing (f : fiber) : bool = Option.is_some f.finalizing

let f_pending_tokens (f : fiber) : int list =
  List.map (fun (p : (_, _, _, _, _, _) pending) -> p.token) f.pending

let f_observers (f : fiber) : observer list = f.observers
let f_children (f : fiber) : fiber_id list = f.children
let f_op_count (f : fiber) : int = f.current_op_count
let f_max_ops (f : fiber) : int = f.max_ops_before_yield
let f_prevent_yield (f : fiber) : bool = f.prevent_yield
let f_yield_override (f : fiber) : bool option = f.yield_override
let f_context (f : fiber) : ctx = f.context
let f_dispatcher_armed (f : fiber) : bool = E4_buckets_list.armed f.dispatcher

let f_dispatcher (f : fiber) : (int * int) list =
  List.map (fun (p, ts) -> (p, List.length ts)) (E4_buckets_list.to_list f.dispatcher)
