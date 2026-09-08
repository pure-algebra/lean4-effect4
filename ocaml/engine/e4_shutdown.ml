(* e4_shutdown.ml — the ordered clean-up DAG.

   What it is: a registry of clean-up hooks with declared `after` edges, and one pass that
   runs them in a topological order whose tie-break is LIFO, seals itself against
   registrations made while it runs, accumulates rather than aborts, recurses to a fixpoint,
   and stops at a host deadline with everything it did not reach named in the report.
   Depends on: nothing in the library (Unix for the deadline, Thread for SD5's bounded wait).

   The laws SD1-SD6, the deadline convention, the exit-code contract and the two refusals
   are stated at the head of e4_shutdown.mli.

   THE ONE STRUCTURAL DECISION: how a hook is bounded. A hook is ordinary OCaml code; this
   module cannot interrupt it. With no deadline (`no_deadline`) a hook runs on the calling
   thread, which is the cheap and honest case. With a finite deadline each hook runs on a
   thread of its own and the caller waits for it up to the deadline; on overrun the caller
   walks away, reports the hook as `unfinished`, and stops the pass. The overrun hook keeps
   running -- there is no thread kill in OCaml and inventing one by exception injection
   would be worse -- so the contract is: after a deadline overrun the process is expected to
   exit, and exit code 129 tells the operator exactly that. Refusal row A3-SHUTDOWN-KILL.

   WHY THE PASS STOPS AT THE FIRST OVERRUN. The deadline is global, not per hook. Once it
   has passed, no later hook can be reached inside it either, so continuing would mean
   running hooks past a bound the caller set. Everything unreached is reported. *)

type id = { r_serial : int; index : int; hook_name : string; hook_loc : string }

let name h = h.hook_name
let loc h = h.hook_loc
let index h = h.index
let equal a b = a.r_serial = b.r_serial && a.index = b.index

type report = {
  ran : (id * float) list;
  failed : (id * exn) list;
  unfinished : id list;
  passes : int;
  exit_code : int;
}

(* Named constants, never `max_int` (trap #17). *)
let max_passes = 16
let no_deadline = infinity
let poll_seconds = 0.0005
let exit_clean = 127
let exit_cleanup_failed = 128
let exit_cleanup_unfinished = 129
let exit_forced = 255

type hook = { hid : id; fn : unit -> unit; after : id list }

module Registry = struct
  type t = {
    serial : int;
    mu : Mutex.t;
    mutable hooks : hook list; (* reverse registration order *)
    mutable next_index : int;
    mutable running : bool;
    mutable final : report option;
  }

  let serials = Atomic.make 0
  let create () =
    {
      serial = Atomic.fetch_and_add serials 1;
      mu = Mutex.create ();
      hooks = [];
      next_index = 0;
      running = false;
      final = None;
    }

  let registered t = Mutex.protect t.mu (fun () -> List.rev_map (fun h -> h.hid) t.hooks)

  let register t ?(after = []) ~loc ~name fn =
    Mutex.protect t.mu (fun () ->
        if t.final <> None then
          invalid_arg ("E4_shutdown.register: the pass is over (" ^ name ^ " at " ^ loc ^ ")");
        List.iter
          (fun (d : id) ->
            if d.r_serial <> t.serial then
              invalid_arg
                ("E4_shutdown.register: `after` id from another registry (" ^ name ^ " at " ^ loc
               ^ ")");
            if not (List.exists (fun h -> h.hid.index = d.index) t.hooks) then
              invalid_arg
                ("E4_shutdown.register: unknown `after` id (" ^ name ^ " at " ^ loc ^ ")"))
          after;
        let hid = { r_serial = t.serial; index = t.next_index; hook_name = name; hook_loc = loc } in
        t.next_index <- t.next_index + 1;
        t.hooks <- { hid; fn; after } :: t.hooks;
        hid)

  (* SD2: a topological order of the pass's hooks whose tie-break among eligible hooks is
     the largest registration index -- so with no `after` edge at all the order is exactly
     reverse registration. `attempted` holds the indices of earlier passes. *)
  let order pending ~attempted =
    let emitted = Hashtbl.create 16 in
    let remaining = ref pending in
    let out = ref [] in
    let largest sel =
      List.fold_left
        (fun acc h ->
          if sel h then
            match acc with
            | None -> Some h
            | Some (b : hook) -> if h.hid.index > b.hid.index then Some h else acc
          else acc)
        None !remaining
    in
    while !remaining <> [] do
      let ready h =
        List.for_all
          (fun (d : id) -> Hashtbl.mem attempted d.index || Hashtbl.mem emitted d.index)
          h.after
      in
      let pick =
        match largest ready with
        | Some h -> h
        | None -> (
            (* Unreachable while SD2's "every edge points backwards" holds; taking the
               largest index anyway keeps the loop total rather than spinning. *)
            match largest (fun _ -> true) with Some h -> h | None -> assert false)
      in
      Hashtbl.replace emitted pick.hid.index ();
      out := pick :: !out;
      remaining := List.filter (fun h -> h.hid.index <> pick.hid.index) !remaining
    done;
    List.rev !out

  (* One hook, bounded by the deadline. See the head of this file for why the finite case
     uses a thread and what happens to a hook that overruns. *)
  let run_hook h ~deadline =
    if deadline = no_deadline then (try h.fn (); `Ok with e -> `Failed e)
    else begin
      let outcome : [ `Ok | `Failed of exn | `Timeout ] ref = ref `Ok in
      let finished = Atomic.make false in
      let _ : Thread.t =
        Thread.create
          (fun () ->
            (try h.fn () with e -> outcome := `Failed e);
            Atomic.set finished true)
          ()
      in
      let rec wait () =
        if Atomic.get finished then !outcome
        else if Unix.gettimeofday () >= deadline then `Timeout
        else begin
          Thread.delay poll_seconds;
          wait ()
        end
      in
      wait ()
    end

  let exit_code_of ~forced ~failed ~unfinished =
    if forced then exit_forced
    else if unfinished <> [] then exit_cleanup_unfinished
    else if failed <> [] then exit_cleanup_failed
    else exit_clean

  let report t = Mutex.protect t.mu (fun () -> t.final)

  let run t ~deadline =
    (* SD6, both shapes: a second call after the pass returns the first report, and a second
       call DURING the pass (two signals, two threads) waits for it rather than starting a
       second pass. *)
    let claim =
      Mutex.protect t.mu (fun () ->
          match t.final with
          | Some r -> `Report r
          | None ->
              if t.running then `Wait
              else begin
                t.running <- true;
                `Run
              end)
    in
    match claim with
    | `Report r -> r
    | `Wait ->
        let rec w () =
          match report t with
          | Some r -> r
          | None ->
              Thread.delay poll_seconds;
              w ()
        in
        w ()
    | `Run ->
        let forced = Unix.gettimeofday () >= deadline in
        let attempted = Hashtbl.create 16 in
        let ran = ref [] and failed = ref [] and passes = ref 0 and expired = ref forced in
        let snapshot () =
          (* SD1: each pass snapshots the hooks not yet attempted; a registration made by a
             running hook lands in the NEXT snapshot, never in the one in flight. *)
          Mutex.protect t.mu (fun () -> List.rev t.hooks)
          |> List.filter (fun h -> not (Hashtbl.mem attempted h.hid.index))
        in
        let rec pass () =
          if (not !expired) && !passes < max_passes then begin
            match snapshot () with
            | [] -> ()
            | pending ->
                incr passes;
                List.iter
                  (fun h ->
                    if not !expired then
                      if Unix.gettimeofday () >= deadline then expired := true
                      else begin
                        Hashtbl.replace attempted h.hid.index ();
                        let t0 = Unix.gettimeofday () in
                        match run_hook h ~deadline with
                        | `Ok -> ran := (h.hid, Unix.gettimeofday () -. t0) :: !ran
                        | `Failed e -> failed := (h.hid, e) :: !failed
                        | `Timeout ->
                            (* SD5: not finished, so not attempted; it is reported below. *)
                            Hashtbl.remove attempted h.hid.index;
                            expired := true
                      end)
                  (order pending ~attempted);
                pass ()
          end
        in
        pass ();
        let unfinished =
          Mutex.protect t.mu (fun () -> List.rev t.hooks)
          |> List.filter (fun h -> not (Hashtbl.mem attempted h.hid.index))
          |> List.map (fun h -> h.hid)
        in
        let failed_l = List.rev !failed in
        let r =
          {
            ran = List.rev !ran;
            failed = failed_l;
            unfinished;
            passes = !passes;
            exit_code = exit_code_of ~forced ~failed:failed_l ~unfinished;
          }
        in
        Mutex.protect t.mu (fun () ->
            match t.final with
            | Some existing -> existing
            | None ->
                t.final <- Some r;
                r)
end

(* The process registry: lwt-exit's shape, one per process. *)
let process = Registry.create ()
let register ?after ~loc ~name fn = Registry.register process ?after ~loc ~name fn
let run ~deadline = Registry.run process ~deadline
let report () = Registry.report process
