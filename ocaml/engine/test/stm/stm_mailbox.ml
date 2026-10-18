(* stm_mailbox -- E4_mailbox against a bounded-FIFO model under qcheck-stm (plan E2; landed
   from docs/research/2026-10-18-ocaml-tooling-probe/probes/stm/stm_mailbox.ml).

   What it is: one model, three sequential tests and three parallel tests. The model is a bounded
   FIFO of stamps with the mailbox's counters: every accepted push takes the next stamp inside
   `push_with`, so the queue's order is visible, and the wake protocol is counted (M4).
     S1 sequential: E4_mailbox agrees with the model.
     S2 red control: a mailbox whose bound check is off by one disagrees (M2).
     S3 red control: a mailbox that takes the stamp before its bound check disagrees: a refused
        push takes a number (M5).
     P1 parallel (STM_domain): a sequential prefix, then one producer domain (push, length, stats)
        beside one consumer domain (pop, length, stats), as the mailbox's contract has them. Every
        outcome must be one the model allows for some interleaving.
     P2 red control: E4_mailbox's own algorithm with no lock, in the same producer and consumer
        roles. QCheck must find an outcome no interleaving explains.
     P3 parallel: two producer domains (push, length, stats): many producers, as M3 says.
   Depends on: Effect4_engine.E4_mailbox, qcheck-stm (STM, STM_sequential, STM_domain),
   Stm_support.
   The model is hand OCaml: a mailbox is host code, whose meaning no Lean definition owns. The
   evidence is host-only: finite runs on this machine; no theorem reaches it.

   Observations: Push answers its stamp or a refusal; Pop answers its batch; Length the waiting
   count; Stats the counters pushed, popped, refused, wakes and length. `contended` is left out:
   it counts lock contention, which is timing, not meaning. *)

open Effect4_engine

module type MAILBOX = sig
  type 'a t

  val create : ?wake:(unit -> unit) -> bound:int -> unit -> 'a t
  val push_with : 'a t -> (unit -> 'a) -> (unit, [ `Full ]) result
  val pop_batch : 'a t -> max:int -> 'a list
  val length : 'a t -> int
  val stats : 'a t -> E4_mailbox.stats
end

let bound = 4

module Spec (M : MAILBOX) = struct
  type cmd =
    | Push
    | Pop of int
    | Length
    | Stats

  let show_cmd = function
    | Push -> "Push"
    | Pop m -> "Pop " ^ string_of_int m
    | Length -> "Length"
    | Stats -> "Stats"
  ;;

  type state =
    { q : int list (** the stamps waiting, oldest first *)
    ; next : int (** the stamp the next accepted push takes *)
    ; outstanding : bool
      (** M4: a wake was delivered and the mailbox has not drained since *)
    ; pushed : int
    ; popped : int
    ; refused : int
    ; wakes : int
    }

  type sut =
    { mailbox : int M.t
    ; stamp : int Atomic.t
    }

  let init_state =
    { q = []
    ; next = 1
    ; outstanding = false
    ; pushed = 0
    ; popped = 0
    ; refused = 0
    ; wakes = 0
    }
  ;;

  let arb_of g = QCheck.make ~print:show_cmd g
  let gen_pop = QCheck.Gen.(map (fun m -> Pop m) (int_range 1 3))

  let arb_cmd _ =
    arb_of QCheck.Gen.(oneof [ return Push; gen_pop; return Length; return Stats ])
  ;;

  let arb_producer _ =
    arb_of
      QCheck.Gen.(oneof_weighted [ 3, return Push; 1, return Length; 1, return Stats ])
  ;;

  let arb_consumer _ =
    arb_of QCheck.Gen.(oneof_weighted [ 3, gen_pop; 1, return Length; 1, return Stats ])
  ;;

  let rec take n = function
    | [] -> []
    | x :: r -> if n = 0 then [] else x :: take (n - 1) r
  ;;

  let rec drop n l =
    if n = 0
    then l
    else (
      match l with
      | [] -> []
      | _ :: r -> drop (n - 1) r)
  ;;

  let next_state c s =
    match c with
    | Push ->
      if List.length s.q >= bound
      then { s with refused = s.refused + 1 }
      else
        { s with
          q = s.q @ [ s.next ]
        ; next = s.next + 1
        ; pushed = s.pushed + 1
        ; outstanding = true
        ; wakes = (if s.outstanding then s.wakes else s.wakes + 1)
        }
    | Pop m ->
      let rest = drop m s.q in
      let popped = s.popped + List.length (take m s.q) in
      if List.is_empty rest
      then { s with q = rest; popped; outstanding = false }
      else { s with q = rest; popped; wakes = s.wakes + 1 }
    | Length | Stats -> s
  ;;

  let init_sut () = { mailbox = M.create ~wake:ignore ~bound (); stamp = Atomic.make 0 }
  let cleanup _ = ()
  let precond _ _ = true

  (* Each call's exception is captured as a value (STM.protect), so a race that raises is a result
     the postcondition refuses, never an escaping exception. *)
  let push sut =
    let taken = ref 0 in
    match
      M.push_with sut.mailbox (fun () ->
        let k = Atomic.fetch_and_add sut.stamp 1 + 1 in
        taken := k;
        k)
    with
    | Ok () -> Some !taken
    | Error `Full -> None
  ;;

  let counters (st : E4_mailbox.stats) =
    [ st.pushed; st.popped; st.refused; st.wakes; st.length ]
  ;;

  let run c sut =
    match c with
    | Push -> STM.Res (STM.result (STM.option STM.int) STM.exn, STM.protect push sut)
    | Pop m ->
      STM.Res
        ( STM.result (STM.list STM.int) STM.exn
        , STM.protect (fun () -> M.pop_batch sut.mailbox ~max:m) () )
    | Length -> STM.Res (STM.result STM.int STM.exn, STM.protect M.length sut.mailbox)
    | Stats ->
      STM.Res
        ( STM.result (STM.list STM.int) STM.exn
        , STM.protect (fun () -> counters (M.stats sut.mailbox)) () )
  ;;

  let postcond c s (res : STM.res) =
    match c, res with
    | ( Push
      , STM.Res
          ((STM.Result (STM.Option STM.Int, STM.Exn), _), (r : (int option, exn) result))
      ) ->
      (match r with
       | Ok (Some k) -> List.length s.q < bound && Int.equal k s.next
       | Ok None -> List.length s.q >= bound
       | Error _ -> false)
    | ( Pop m
      , STM.Res ((STM.Result (STM.List STM.Int, STM.Exn), _), (r : (int list, exn) result))
      ) ->
      (match r with
       | Ok xs -> List.equal Int.equal xs (take m s.q)
       | Error _ -> false)
    | Length, STM.Res ((STM.Result (STM.Int, STM.Exn), _), (r : (int, exn) result)) ->
      (match r with
       | Ok n -> Int.equal n (List.length s.q)
       | Error _ -> false)
    | ( Stats
      , STM.Res ((STM.Result (STM.List STM.Int, STM.Exn), _), (r : (int list, exn) result))
      ) ->
      (match r with
       | Ok xs ->
         List.equal
           Int.equal
           xs
           [ s.pushed; s.popped; s.refused; s.wakes; List.length s.q ]
       | Error _ -> false)
    | _ -> false
  ;;
end

(* The red controls' mailboxes: E4_mailbox's own algorithm without its lock, one of them with the
   bound check off by one, one taking the stamp before the bound check. Only the named difference
   separates each from e4_mailbox.ml. *)
module Unlocked (P : sig
    val full : len:int -> bound:int -> bool
    val stamp_first : bool
  end) : MAILBOX = struct
  type 'a t =
    { q : 'a Queue.t
    ; bound : int
    ; wake : (unit -> unit) option
    ; mutable outstanding : bool
    ; mutable pushed : int
    ; mutable popped : int
    ; mutable refused : int
    ; mutable wakes : int
    }

  let create ?wake ~bound () =
    { q = Queue.create ()
    ; bound
    ; wake
    ; outstanding = false
    ; pushed = 0
    ; popped = 0
    ; refused = 0
    ; wakes = 0
    }
  ;;

  let push_with t make =
    let early = if P.stamp_first then Some (make ()) else None in
    if P.full ~len:(Queue.length t.q) ~bound:t.bound
    then (
      t.refused <- t.refused + 1;
      Error `Full)
    else (
      Queue.push
        (match early with
         | Some x -> x
         | None -> make ())
        t.q;
      t.pushed <- t.pushed + 1;
      (match t.wake with
       | Some wake when not t.outstanding ->
         t.outstanding <- true;
         t.wakes <- t.wakes + 1;
         wake ()
       | _ -> ());
      Ok ())
  ;;

  let pop_batch t ~max =
    let rec go n acc =
      if n = 0 || Queue.is_empty t.q
      then List.rev acc
      else go (n - 1) (Queue.pop t.q :: acc)
    in
    let batch = go max [] in
    t.popped <- t.popped + List.length batch;
    (match t.wake with
     | Some wake when not (Queue.is_empty t.q) ->
       t.wakes <- t.wakes + 1;
       wake ()
     | _ -> t.outstanding <- false);
    batch
  ;;

  let length t = Queue.length t.q

  let stats t =
    { E4_mailbox.pushed = t.pushed
    ; popped = t.popped
    ; refused = t.refused
    ; wakes = t.wakes
    ; contended = 0
    ; length = Queue.length t.q
    }
  ;;
end

module Racy = Unlocked (struct
    let full ~len ~bound = len >= bound
    let stamp_first = false
  end)

module Off_by_one = Unlocked (struct
    let full ~len ~bound = len > bound
    let stamp_first = false
  end)

module Stamp_first = Unlocked (struct
    let full ~len ~bound = len >= bound
    let stamp_first = true
  end)

module Real = Spec (E4_mailbox)
module Racy_spec = Spec (Racy)
module Off_spec = Spec (Off_by_one)
module Stamp_spec = Spec (Stamp_first)
module Seq_real = STM_sequential.Make (Real)
module Seq_off = STM_sequential.Make (Off_spec)
module Seq_stamp = STM_sequential.Make (Stamp_spec)
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
    [ Seq_real.agree_test ~count:500 ~name:"S1 E4_mailbox, sequential"
    ; Seq_off.neg_agree_test ~count:500 ~name:"S2 red: bound off by one, sequential"
    ; Seq_stamp.neg_agree_test
        ~count:500
        ~name:"S3 red: stamp taken before the bound check, sequential"
    ; par_test
        ~neg:false
        ~name:"P1 E4_mailbox, one producer and one consumer domain"
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
        ~name:"P3 E4_mailbox, two producer domains"
        ~count:200
        ~repeats:25
        ~ok:Par_real.all_interleavings_ok
        two_producers
        Par_real.agree_prop_par
    ]
;;
