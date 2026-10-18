(* stm_admit -- E4_sched's admission against a model of the host's saved state under qcheck-stm
   (plan E2).

   What it is: the scheduler's admission side, S2 of e4_sched.mli: `admit` reads the target's
   mailbox length, the mailbox bound and the pending count, before any pop. One worker domain
   runs, and its first `load` waits on a gate the test opens only at cleanup, so no decision is
   applied during a run: each mailbox length and the pending count are the commands' own. The
   model is that state: each machine's mailbox length, the pending count (one per Load not yet
   loaded, one per accepted decision) and the last sequence number.
     S1 sequential: E4_sched agrees with the model: spawn (the id, and its Load counted as
        pending, Q1), send (R1's stamp, R2's Unknown and Full), admit (S2 over E4_admit's bands),
        pending and last_seq.
     S2 red control: a scheduler whose bound is one larger than the model's disagrees.
     P1 parallel (STM_domain): two client domains spawn, send, admit and read pending and last_seq
        at once. Every outcome must be one the model allows for some interleaving.
     P2 red control: a client that sends only when its own `admit` answered Any, on two domains:
        admission read by a client and then acted on is a check-then-act race, and QCheck must
        find an outcome no interleaving explains.
   The bands are E4_admit's rule, restated as the model: room = bound - length - pending; no room
   admits nothing, the last four slots (E4_admit's priority reserve) admit priority traffic
   alone, and more room admits any.
   Depends on: Effect4_engine (E4_sched, E4_admit, E4_abandon), qcheck-stm, Stm_support.
   The model is hand OCaml: the scheduler is host code, whose meaning no Lean definition owns.
   The evidence is host-only: finite runs on this machine; no theorem reaches it. *)

open Effect4_engine

let bound = 6
let priority_reserve = 4

(* The gate the worker's first load waits on. *)
type gate =
  { mu : Mutex.t
  ; cv : Condition.t
  ; mutable opened : bool
  }

let gate () = { mu = Mutex.create (); cv = Condition.create (); opened = false }

let open_gate g =
  Mutex.protect g.mu (fun () ->
    g.opened <- true;
    Condition.broadcast g.cv)
;;

(* A machine is nothing and a decision is an int: the scheduler's admission side never reads
   either. The one behaviour is the gated load. *)
let engine g : (unit, int) E4_sched.engine =
  { init = ignore
  ; thread_init = ignore
  ; thread_finalize = ignore
  ; programs = (fun () -> [ "p" ])
  ; load =
      (fun ~program:_ ~fuel:_ ->
        Mutex.protect g.mu (fun () ->
          while not g.opened do
            Condition.wait g.cv g.mu
          done))
  ; step = (fun m ~fuel:_ _ -> m)
  ; release = ignore
  ; finished = (fun _ -> false)
  ; answer = (fun _ -> E4_sched.Suspended)
  ; armed = (fun _ -> [])
  ; fire_of = Fun.id
  ; trace_len = (fun _ -> 0)
  ; rows = (fun _ ~cursor:_ -> [])
  ; to_wire = string_of_int
  ; snapshot = (fun _ -> "")
  ; abandon =
      { interrupt = (fun m ~reason:_ -> m, 0)
      ; open_scopes = (fun _ -> [])
      ; finalizer_step = (fun _ ~scope:_ -> None)
      }
  }
;;

let config sut_bound =
  { E4_sched.domains = 1
  ; mailbox_bound = sut_bound
  ; ring_capacity = 16
  ; batch = 8
  ; spin_budget = 0
  ; finalizer_fuel = 0
  ; checkpoint_every = 0
  ; minor_heap_words = 0
  }
;;

(* [sut_bound] is the bound the scheduler starts with; the model's is [bound]. With
   [check_then_act], [Send] is a client's admit, then its send when the admit answered Any. *)
module Spec (G : sig
    val sut_bound : int
    val check_then_act : bool
  end) =
struct
  type cmd =
    | Spawn
    | Send of int
    | Admit of int
    | Pending
    | Last_seq

  let show_cmd = function
    | Spawn -> "Spawn"
    | Send i -> (if G.check_then_act then "Send_if_any " else "Send ") ^ string_of_int i
    | Admit i -> "Admit " ^ string_of_int i
    | Pending -> "Pending"
    | Last_seq -> "Last_seq"
  ;;

  (* Each spawned machine's mailbox length, in id order; the pending count; the last stamp. *)
  type state =
    { lens : int list
    ; pending : int
    ; seq : int
    }

  type sut =
    { sched : (unit, int) E4_sched.t
    ; gate : gate
    }

  let init_state = { lens = []; pending = 0; seq = 0 }
  let arb_of g = QCheck.make ~print:show_cmd g
  let machine = QCheck.Gen.int_bound 2

  let arb_cmd s =
    arb_of
      QCheck.Gen.(
        oneof_weighted
          [ (if List.is_empty s.lens then 4 else 1), return Spawn
          ; 4, map (fun i -> Send i) machine
          ; 3, map (fun i -> Admit i) machine
          ; 1, return Pending
          ; 1, return Last_seq
          ])
  ;;

  let arb_client _ =
    arb_of
      QCheck.Gen.(
        oneof_weighted
          [ 1, return Spawn
          ; 4, map (fun i -> Send i) machine
          ; 3, map (fun i -> Admit i) machine
          ; 1, return Pending
          ; 1, return Last_seq
          ])
  ;;

  let band room =
    if room <= 0 then "none" else if room <= priority_reserve then "priority" else "any"
  ;;

  let room s i = bound - List.nth s.lens i - s.pending
  let known s i = i < List.length s.lens

  (* The model's answer and next state, one function so the two never drift apart. *)
  let step c s =
    match c with
    | Spawn ->
      ( "ok " ^ string_of_int (List.length s.lens)
      , { s with lens = s.lens @ [ 0 ]; pending = s.pending + 1 } )
    | Send i ->
      if not (known s i)
      then "unknown", s
      else if G.check_then_act && not (String.equal (band (room s i)) "any")
      then "not admitted", s
      else if List.nth s.lens i >= bound
      then "full", s
      else
        ( "ok " ^ string_of_int (s.seq + 1)
        , { lens = List.mapi (fun j n -> if j = i then n + 1 else n) s.lens
          ; pending = s.pending + 1
          ; seq = s.seq + 1
          } )
    | Admit i -> (if known s i then band (room s i) else "none"), s
    | Pending -> string_of_int s.pending, s
    | Last_seq -> string_of_int s.seq, s
  ;;

  let next_state c s = snd (step c s)

  let init_sut () =
    let g = gate () in
    { sched = E4_sched.start (engine g) (config G.sut_bound); gate = g }
  ;;

  (* Open the gate, then the ordered shutdown: the worker loads and applies everything, and its
     domain is joined, so no domain outlives its run. *)
  let cleanup sut =
    open_gate sut.gate;
    ignore (E4_sched.shutdown sut.sched)
  ;;

  let precond _ _ = true

  let band_word = function
    | E4_admit.Any -> "any"
    | E4_admit.Priority_only -> "priority"
    | E4_admit.None_now -> "none"
  ;;

  let send_word = function
    | Ok seq -> "ok " ^ string_of_int seq
    | Error `Unknown -> "unknown"
    | Error `Full -> "full"
    | Error `Stopped -> "stopped"
  ;;

  let answer c sut =
    match c with
    | Spawn ->
      (match E4_sched.spawn sut.sched ~program:"p" ~fuel:1 with
       | Ok id -> "ok " ^ string_of_int id
       | Error (`Unknown_program p) -> "unknown program " ^ p
       | Error `Stopped -> "stopped")
    | Send i ->
      if G.check_then_act
      then (
        match E4_sched.admit sut.sched i with
        | E4_admit.Any -> send_word (E4_sched.send sut.sched i i)
        | E4_admit.Priority_only | E4_admit.None_now ->
          if Option.is_none (E4_sched.domain_of sut.sched i)
          then "unknown"
          else "not admitted")
      else send_word (E4_sched.send sut.sched i i)
    | Admit i -> band_word (E4_sched.admit sut.sched i)
    | Pending -> string_of_int (E4_sched.pending sut.sched)
    | Last_seq -> string_of_int (E4_sched.last_seq sut.sched)
  ;;

  let run c sut = STM.Res (STM.result STM.string STM.exn, STM.protect (answer c) sut)

  let postcond c s (r : STM.res) =
    match r with
    | STM.Res ((STM.Result (STM.String, STM.Exn), _), (r : (string, exn) result)) ->
      (match r with
       | Ok a -> String.equal a (fst (step c s))
       | Error _ -> false)
    | _ -> false
  ;;
end

module Real = Spec (struct
    let sut_bound = bound
    let check_then_act = false
  end)

module Wide = Spec (struct
    let sut_bound = bound + 1
    let check_then_act = false
  end)

module Client = Spec (struct
    let sut_bound = bound
    let check_then_act = true
  end)

module Seq_real = STM_sequential.Make (Real)
module Seq_wide = STM_sequential.Make (Wide)
module Par_real = STM_domain.Make (Real)
module Par_client = STM_domain.Make (Client)

let () =
  let open Stm_support in
  let clients = Par_real.arb_triple 8 8 Real.arb_cmd Real.arb_client Real.arb_client in
  let racing =
    Par_client.arb_triple 8 8 Client.arb_cmd Client.arb_client Client.arb_client
  in
  run
    [ Seq_real.agree_test ~count:300 ~name:"S1 E4_sched admission, sequential"
    ; Seq_wide.neg_agree_test
        ~count:300
        ~name:"S2 red: the bound one larger than the model's, sequential"
    ; par_test
        ~neg:false
        ~name:"P1 E4_sched admission, two client domains"
        ~count:150
        ~repeats:15
        ~ok:Par_real.all_interleavings_ok
        clients
        Par_real.agree_prop_par
    ; par_test
        ~neg:true
        ~name:"P2 red: a client's admit, then send, on two domains"
        ~count:150
        ~repeats:15
        ~ok:Par_client.all_interleavings_ok
        racing
        Par_client.agree_prop_par
    ]
;;
