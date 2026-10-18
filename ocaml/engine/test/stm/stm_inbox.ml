(* stm_inbox -- E4_inbox against an unbounded-FIFO model with a close flag under qcheck-stm (plan E2).

   What it is: one model, two sequential tests and three parallel tests. The model is an unbounded
   FIFO, a closed flag and the counters (pushed, popped): I1-I3 of e4_inbox.ml.
     S1 sequential: E4_inbox agrees with the model, the blocking `pop` included.
     S2 red control: an inbox whose push ignores the close disagrees (I3).
     P1 parallel (STM_domain): a sequential prefix, then one producer domain (push, close, length,
        is_closed, stats) beside one consumer domain (pop_opt, pop, length, stats): the run queue
        of one worker, as E4_sched uses it.
     P2 red control: E4_inbox's own algorithm with no lock, the same roles without the blocking
        `pop`. QCheck must find an outcome no interleaving explains.
     P3 parallel: two producer domains (push, close, length, stats): wakes and control messages
        arrive from many domains.
   A blocking `pop` is generated only where it cannot block: the consumer pops only elements the
   prefix left, so it never waits for the other domain. The wait itself (I2's blocking half) is
   outside this test; test_host's inbox-fifo exercises it.
   Depends on: Effect4_engine.E4_inbox, qcheck-stm (STM, STM_sequential, STM_domain), Stm_support.
   The model is hand OCaml: an inbox is host code, whose meaning no Lean definition owns. The
   evidence is host-only: finite runs on this machine; no theorem reaches it. *)

open Effect4_engine

module type INBOX = sig
  type 'a t

  val create : unit -> 'a t
  val push : 'a t -> 'a -> bool
  val pop : 'a t -> 'a option
  val pop_opt : 'a t -> 'a option
  val close : 'a t -> unit
  val length : 'a t -> int
  val is_closed : 'a t -> bool
  val stats : 'a t -> int * int
end

module Spec
    (I : INBOX)
    (G : sig
       val blocking_pop : bool
     end) =
struct
  type cmd =
    | Push of int
    | Pop_opt
    | Pop
    | Close
    | Length
    | Is_closed
    | Stats

  let show_cmd = function
    | Push x -> "Push " ^ string_of_int x
    | Pop_opt -> "Pop_opt"
    | Pop -> "Pop"
    | Close -> "Close"
    | Length -> "Length"
    | Is_closed -> "Is_closed"
    | Stats -> "Stats"
  ;;

  type state =
    { q : int list
    ; closed : bool
    ; pushed : int
    ; popped : int
    }

  type sut = int I.t

  let init_state = { q = []; closed = false; pushed = 0; popped = 0 }
  let arb_of g = QCheck.make ~print:show_cmd g
  let gen_push = QCheck.Gen.(map (fun x -> Push x) (int_bound 99))

  (* A blocking pop only where the state holds an element or the close: it never waits. *)
  let pop_weight s =
    if G.blocking_pop && ((not (List.is_empty s.q)) || s.closed) then 2 else 0
  ;;

  let arb_cmd s =
    arb_of
      QCheck.Gen.(
        oneof_weighted
          [ 3, gen_push
          ; 2, return Pop_opt
          ; pop_weight s, return Pop
          ; 1, return Close
          ; 1, return Length
          ; 1, return Is_closed
          ; 1, return Stats
          ])
  ;;

  let arb_producer _ =
    arb_of
      QCheck.Gen.(
        oneof_weighted
          [ 4, gen_push
          ; 1, return Close
          ; 1, return Length
          ; 1, return Is_closed
          ; 1, return Stats
          ])
  ;;

  (* The consumer's state threads its own pops only, so an element it sees here is one the prefix
     left, which no producer can take: its blocking pop has an element in every interleaving. *)
  let arb_consumer s =
    arb_of
      QCheck.Gen.(
        oneof_weighted
          [ 3, return Pop_opt
          ; pop_weight { s with closed = false }, return Pop
          ; 1, return Length
          ; 1, return Stats
          ])
  ;;

  let next_state c s =
    match c with
    | Push x -> if s.closed then s else { s with q = s.q @ [ x ]; pushed = s.pushed + 1 }
    | Pop_opt | Pop ->
      (match s.q with
       | [] -> s
       | _ :: rest -> { s with q = rest; popped = s.popped + 1 })
    | Close -> { s with closed = true }
    | Length | Is_closed | Stats -> s
  ;;

  let init_sut () = I.create ()
  let cleanup _ = ()

  let precond c s =
    match c with
    | Pop -> (not (List.is_empty s.q)) || s.closed
    | _ -> true
  ;;

  let res ty f x = STM.Res (STM.result ty STM.exn, STM.protect f x)

  let run c sut =
    match c with
    | Push x -> res STM.bool (fun () -> I.push sut x) ()
    | Pop_opt -> res (STM.option STM.int) I.pop_opt sut
    | Pop -> res (STM.option STM.int) I.pop sut
    | Close -> res STM.unit I.close sut
    | Length -> res STM.int I.length sut
    | Is_closed -> res STM.bool I.is_closed sut
    | Stats ->
      res
        (STM.list STM.int)
        (fun () ->
           let p, q = I.stats sut in
           [ p; q ])
        ()
  ;;

  let head s =
    match s.q with
    | [] -> None
    | x :: _ -> Some x
  ;;

  let postcond c s (r : STM.res) =
    match c, r with
    | Push _, STM.Res ((STM.Result (STM.Bool, STM.Exn), _), (r : (bool, exn) result)) ->
      (match r with
       | Ok b -> Bool.equal b (not s.closed)
       | Error _ -> false)
    | ( (Pop_opt | Pop)
      , STM.Res
          ((STM.Result (STM.Option STM.Int, STM.Exn), _), (r : (int option, exn) result))
      ) ->
      (match r with
       | Ok v -> Option.equal Int.equal v (head s)
       | Error _ -> false)
    | Close, STM.Res ((STM.Result (STM.Unit, STM.Exn), _), (r : (unit, exn) result)) ->
      Result.is_ok r
    | Length, STM.Res ((STM.Result (STM.Int, STM.Exn), _), (r : (int, exn) result)) ->
      (match r with
       | Ok n -> Int.equal n (List.length s.q)
       | Error _ -> false)
    | Is_closed, STM.Res ((STM.Result (STM.Bool, STM.Exn), _), (r : (bool, exn) result))
      ->
      (match r with
       | Ok b -> Bool.equal b s.closed
       | Error _ -> false)
    | ( Stats
      , STM.Res ((STM.Result (STM.List STM.Int, STM.Exn), _), (r : (int list, exn) result))
      ) ->
      (match r with
       | Ok xs -> List.equal Int.equal xs [ s.pushed; s.popped ]
       | Error _ -> false)
    | _ -> false
  ;;
end

(* The red controls' inboxes: E4_inbox's own algorithm without its lock, one of them pushing after
   the close. With no condition variable, `pop` cannot wait; it never needs to, because a pop is
   generated only where an element or the close is there, and P2 generates none. *)
module Unlocked (P : sig
    val refuse_after_close : bool
  end) : INBOX = struct
  type 'a t =
    { q : 'a Queue.t
    ; mutable closed : bool
    ; mutable pushed : int
    ; mutable popped : int
    }

  let create () = { q = Queue.create (); closed = false; pushed = 0; popped = 0 }

  let push t x =
    if P.refuse_after_close && t.closed
    then false
    else (
      Queue.push x t.q;
      t.pushed <- t.pushed + 1;
      true)
  ;;

  let pop_opt t =
    if Queue.is_empty t.q
    then None
    else (
      t.popped <- t.popped + 1;
      Some (Queue.pop t.q))
  ;;

  let pop t =
    match pop_opt t with
    | Some x -> Some x
    | None -> if t.closed then None else invalid_arg "Unlocked.pop would wait"
  ;;

  let close t = t.closed <- true
  let length t = Queue.length t.q
  let is_closed t = t.closed
  let stats t = t.pushed, t.popped
end

module Racy = Unlocked (struct
    let refuse_after_close = true
  end)

module Open_after_close = Unlocked (struct
    let refuse_after_close = false
  end)

module Real =
  Spec
    (E4_inbox)
    (struct
      let blocking_pop = true
    end)

module Racy_spec =
  Spec
    (Racy)
    (struct
      let blocking_pop = false
    end)

module Late_spec =
  Spec
    (Open_after_close)
    (struct
      let blocking_pop = true
    end)

module Seq_real = STM_sequential.Make (Real)
module Seq_late = STM_sequential.Make (Late_spec)
module Par_real = STM_domain.Make (Real)
module Par_racy = STM_domain.Make (Racy_spec)

let () =
  let open Stm_support in
  let producer_consumer =
    Par_real.arb_triple 12 10 Real.arb_cmd Real.arb_producer Real.arb_consumer
  in
  let two_producers =
    Par_real.arb_triple 12 10 Real.arb_cmd Real.arb_producer Real.arb_producer
  in
  let racy =
    Par_racy.arb_triple
      12
      10
      Racy_spec.arb_cmd
      Racy_spec.arb_producer
      Racy_spec.arb_consumer
  in
  run
    [ Seq_real.agree_test ~count:500 ~name:"S1 E4_inbox, sequential"
    ; Seq_late.neg_agree_test
        ~count:500
        ~name:"S2 red: a push after the close is queued, sequential"
    ; par_test
        ~neg:false
        ~name:"P1 E4_inbox, one producer and one consumer domain"
        ~count:200
        ~repeats:25
        ~ok:Par_real.all_interleavings_ok
        producer_consumer
        Par_real.agree_prop_par
    ; par_test
        ~neg:true
        ~name:"P2 red: no lock, one producer and one consumer domain"
        ~count:200
        ~repeats:25
        ~ok:Par_racy.all_interleavings_ok
        racy
        Par_racy.agree_prop_par
    ; par_test
        ~neg:false
        ~name:"P3 E4_inbox, two producer domains"
        ~count:200
        ~repeats:25
        ~ok:Par_real.all_interleavings_ok
        two_producers
        Par_real.agree_prop_par
    ]
;;
