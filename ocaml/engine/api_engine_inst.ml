(* Api_engine_inst -- the FAST instance of the generated engine, plus the projections the
   drive loop reads it through.

     Api_engine.Make (E4_table) (E4_trace) (E4_memo) (E4_buckets) (E4_ppath) (E4_env) (E4_fibers_view)

   What it is: the engine of docs/research/2026-09-08-engine-a1-state.md §5.2, row 3 --
   "`Api_engine.Make(Map carriers)`: proves the CARRIERS are meaning-preserving".  Every
   generated declaration is untouched; only the seven carriers behind `RunMachine.fibers`,
   `RunMachine.trace`, `MemoMap.entries`, the per-fiber `Dispatcher`, `Point.path` and
   `Point.env` change (the last two are lane G2, docs/research/
   2026-09-08-engine-prof-chain.md: the snoc-shared spine that carries its node, and the
   snoc-shared environment with a cached length).  The fiber table is `E4_fibers_view`, which
   is `E4_table` plus the MAINTAINED completed view (lane G3): `completedExits` is a field
   read rather than a per-step scan of the table.

   Beside the functor application this file carries the ADAPTER: the type abbreviations for
   the fully applied machine and the free-row projections of `E4_engine.INSTANCE`.  They are
   here, not in `e4_engine.ml`, because they are the only lines that must name a carrier
   module (`E4_table.bindings`, `E4_trace.to_list`, `E4_buckets.to_list`); everything else --
   the drive loop, the answer alphabet, every renderer -- is written ONCE in
   `E4_engine.Make` and shared with `Api_engine_ref`.

   Depends on: Api_engine (generated), E4_table, E4_trace, E4_memo, E4_buckets.

   Behaviours:
   I1  Every projection is a pure function of the machine value: no fuel, no tape, no
       mutation (INV-TAPE-1, brief §2.4; E4_engine EN7).            by construction
   I2  `fibers`, `completed_exits` and `refs` are ASCENDING by key -- `E4_table.bindings`
       is (lane C law T5), `E4_fibers_view.bindings` IS it, and the maintained completed view
       is that same ascending filterMap (lane G3 law FV1) -- so the differential against the
       list twin compares like with like.
                                                                    by construction
   I3  `trace` is in emission order: `E4_trace.to_list` is one reverse of the accumulator
       (lane C law TR2).                                            by construction
   I4  `step` is the generated `stepDecisionState`, and its second component is the
       generated `settled` -- the discriminator the answer alphabet needs (owner default
       A1-Q7).                                                      by construction *)

include Api_engine.Make (E4_table) (E4_trace) (E4_memo) (E4_buckets) (E4_ppath) (E4_env) (E4_fibers_view)

let name = "Fast"
let carriers = "E4_table / E4_trace / E4_memo / E4_buckets / E4_ppath / E4_env / E4_fibers_view"

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

(* `Effect4.Machine.stepDecisionState` at `Api.replay`'s specialisation (api_engine.ml:11424);
   the bool is `Effect4.Machine.settled` (:11330), which api_replay reads at :11503. *)
let step (p : program) (i : interp) ~(fuel : int) (m : machine) (d : decision)
  : machine * bool =
  step_decision_state_at_program_replay_checked_from_spec_1 p [] i fuel m d

let run_api (p : program) ~(fuel : int) ~(choices : bool list) : outcome * machine =
  let r = api_run p fuel choices [] [] in
  (r.outcome, r.machine)

(* -- the free rows -------------------------------------------------------------------- *)

let fibers (m : machine) : (fiber_id * fiber) list = E4_fibers_view.bindings m.fibers
let fiber_count (m : machine) : int = E4_fibers_view.cardinal m.fibers
let trace (m : machine) : event list = E4_trace.to_list m.trace
let trace_length (m : machine) : int = E4_trace.length m.trace
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
let refs (m : machine) : val_ list = E4_table.to_list (stores_of m).refs
let next_name (m : machine) : int = (stores_of m).next_name
let due_count (m : machine) : int = List.length (stores_of m).deferreds.due
let cell_count (m : machine) : int = E4_table.cardinal (stores_of m).deferreds.cells
let scope_count (m : machine) : int = E4_table.cardinal (stores_of m).scopes
let memo_map_count (m : machine) : int = List.length (stores_of m).memo

let memo_paths (m : machine) : (int * int list list) list =
  List.map
    (fun (mm : memo_map) -> (mm.id, List.map fst (E4_memo.bindings mm.entries)))
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
let f_dispatcher_armed (f : fiber) : bool = E4_buckets.armed f.dispatcher

let f_dispatcher (f : fiber) : (int * int) list =
  List.map (fun (p, ts) -> (p, List.length ts)) (E4_buckets.to_list f.dispatcher)

(* The program conversion is NOT here: `E4_engine.Make` applies `E4_program.Make` to this
   module itself (the INSTANCE signature includes `E4_program.PROGRAM_TYPES`), so the
   conversion is written once and this file names it nowhere. *)
