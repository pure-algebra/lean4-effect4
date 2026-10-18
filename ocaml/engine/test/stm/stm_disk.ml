(* stm_disk -- E4_disk, the owned disk writer, against a model of its stores under qcheck-stm
   (plan E2).

   What it is: each store holds the nodes schema, A and B and one root, docs/a, that names A or B.
   Two slots, 0 and 1, each hold at most one writer: a slot opens a writer, advances docs/a to
   the other node (one transaction: E4_disk.commit), reads the head, and closes. The model is, per
   store, the slot that holds its writer (CS4 and PK6: one writer, a second open refused with
   Locked) and docs/a's head and generation.
     S1 sequential: E4_disk agrees with the model on one store shared by both slots.
     S2 red control: a slot whose close drops its writer without closing it disagrees: the lock
        stays held, so the next open is refused where the model opens it.
     P1 parallel (STM_domain): two stores, one per slot, each writer opened in the prefix; then
        each domain advances and reads its own store. Writers of different stores commit at once
        without interfering.
     K1 one store, and two domains open it at once: exactly one passes the writer lock. Until
        E4_lock, the in-process registry was a Hashtbl checked and filled with no mutex, and
        Unix.lockf does not refuse a second descriptor of one process, so both passed
        (receipt-estate.md, 2026-10-18).
     K2 one store whose writer slot 0 holds; domain 0 advances while domain 1 tries to open. The
        open is refused with Locked and the holder's commits succeed. Until E4_cas.open_rw_exn
        took the lock first, the refused opener removed the live writer's control.tmp, and the
        holder's commit failed on its rename.
   Depends on: Effect4_engine_cas (E4_disk, E4_cas, E4_control, E4_admission, E4_fault, E4_lock),
   Disk_test_support (the nodes, a temporary directory), qcheck-stm, Stm_support.
   The model is hand OCaml: the writer's ownership is host code, whose meaning no Lean definition
   owns; test_disk_stm.ml compares the writer's commands with Lean's Cas transitions. The evidence
   is host-only: finite runs on this machine; no theorem reaches it. *)

open Effect4_engine_cas
module T = Disk_test_support

let initial =
  T.transaction
    [ T.schema; T.a; T.b ]
    [ E4_control.Create ("docs/a", E4_control.Swap, T.target T.aa) ]
;;

(* [stores] is 1 (both slots share one store) or 2 (slot s owns store s). [opened] lists the
   slots whose writer is open when a run starts. With [leaky_close], a close drops the slot's
   writer without closing it. *)
module Spec (G : sig
    val stores : int
    val opened : int list
    val leaky_close : bool
  end) =
struct
  type cmd =
    | Open of int
    | Close of int
    | Advance of int
    | Head of int

  let show_cmd = function
    | Open s -> "Open " ^ string_of_int s
    | Close s -> "Close " ^ string_of_int s
    | Advance s -> "Advance " ^ string_of_int s
    | Head s -> "Head " ^ string_of_int s
  ;;

  (* Per store: the slot whose writer holds it, and docs/a's head (A or B) and generation. *)
  type store =
    { holder : int option
    ; on_a : bool
    ; gen : int
    }

  type state = store list

  type sut =
    { dirs : string array
    ; slots : E4_disk.t option array
    ; leaked : E4_disk.t list ref
    }

  let store_of s = if G.stores = 1 then 0 else s

  let init_state =
    List.init G.stores (fun i ->
      { holder = List.find_opt (fun s -> Int.equal (store_of s) i) G.opened
      ; on_a = true
      ; gen = 1
      })
  ;;

  let arb_of g = QCheck.make ~print:show_cmd g
  let holds st s = Option.equal Int.equal (List.nth st (store_of s)).holder (Some s)

  let gen_slot ~slots st =
    QCheck.Gen.(
      slots
      >>= fun s ->
      oneof_weighted
        [ (if holds st s then 0 else 3), return (Open s)
        ; 1, return (Close s)
        ; 3, return (Advance s)
        ; 1, return (Head s)
        ])
  ;;

  let arb_cmd st = arb_of (gen_slot ~slots:(QCheck.Gen.int_bound 1) st)
  let head_word on_a gen = (if on_a then "A " else "B ") ^ string_of_int gen

  (* The model's answer and next state, one function so the two never drift apart. *)
  let step c st =
    let set s v = List.mapi (fun i x -> if i = store_of s then v else x) st in
    match c with
    | Open s ->
      let x = List.nth st (store_of s) in
      (match x.holder with
       | None -> "opened", set s { x with holder = Some s }
       | Some _ -> "locked", st)
    | Close s ->
      let x = List.nth st (store_of s) in
      if holds st s then "closed", set s { x with holder = None } else "idle", st
    | Advance s ->
      let x = List.nth st (store_of s) in
      if holds st s
      then
        ( "advanced " ^ string_of_int (x.gen + 1)
        , set s { x with on_a = not x.on_a; gen = x.gen + 1 } )
      else "no writer", st
    | Head s ->
      let x = List.nth st (store_of s) in
      (if holds st s then head_word x.on_a x.gen else "no writer"), st
  ;;

  let next_state c st = snd (step c st)

  let precond c st =
    match c with
    | Open s -> not (holds st s)
    | _ -> true
  ;;

  let init_sut () =
    let dirs =
      Array.init G.stores (fun _ ->
        let dir = T.temp () in
        let disk = T.open_ dir in
        ignore (T.get (E4_disk.commit disk initial));
        E4_disk.close disk;
        dir)
    in
    let slots = Array.make 2 None in
    List.iter (fun s -> slots.(s) <- Some (T.open_ dirs.(store_of s))) G.opened;
    { dirs; slots; leaked = ref [] }
  ;;

  let cleanup sut =
    Array.iter (Option.iter E4_disk.close) sut.slots;
    List.iter E4_disk.close !(sut.leaked);
    Array.iter T.remove sut.dirs
  ;;

  let head disk =
    match E4_disk.image disk with
    | Error why -> "refused " ^ T.admission_observation why
    | Ok image ->
      (match T.root image "docs/a" with
       | None -> "no root"
       | Some r ->
         head_word (E4_addr.Addr.equal r.head.digest T.aa) (Z.to_int r.head.generation))
  ;;

  let advance disk =
    match E4_disk.image disk with
    | Error why -> "refused " ^ T.admission_observation why
    | Ok image ->
      (match T.root image "docs/a" with
       | None -> "no root"
       | Some r ->
         let next = if E4_addr.Addr.equal r.head.digest T.aa then T.ba else T.aa in
         (match
            E4_disk.commit
              disk
              (T.transaction [] [ E4_control.Advance ("docs/a", r.head, T.target next) ])
          with
          | Ok { E4_cas.receipt_moves = [ E4_cas.Advanced g ]; _ } ->
            "advanced " ^ Z.to_string g
          | result -> "refused " ^ T.transaction_observation result))
  ;;

  let answer c sut =
    match c with
    | Open s ->
      (match E4_disk.open_ ~dir:sut.dirs.(store_of s) T.opts with
       | Ok disk ->
         sut.slots.(s) <- Some disk;
         "opened"
       | Error (E4_admission.Fault (E4_fault.Locked _)) -> "locked"
       | Error why -> "refused " ^ T.admission_observation why)
    | Close s ->
      (match sut.slots.(s) with
       | None -> "idle"
       | Some disk ->
         if G.leaky_close then sut.leaked := disk :: !(sut.leaked) else E4_disk.close disk;
         sut.slots.(s) <- None;
         "closed")
    | Advance s ->
      (match sut.slots.(s) with
       | None -> "no writer"
       | Some disk -> advance disk)
    | Head s ->
      (match sut.slots.(s) with
       | None -> "no writer"
       | Some disk -> head disk)
  ;;

  let run c sut = STM.Res (STM.result STM.string STM.exn, STM.protect (answer c) sut)

  let postcond c st (r : STM.res) =
    match r with
    | STM.Res ((STM.Result (STM.String, STM.Exn), _), (r : (string, exn) result)) ->
      (match r with
       | Ok a -> String.equal a (fst (step c st))
       | Error _ -> false)
    | _ -> false
  ;;
end

module One = Spec (struct
    let stores = 1
    let opened = []
    let leaky_close = false
  end)

module Leaky = Spec (struct
    let stores = 1
    let opened = []
    let leaky_close = true
  end)

module Two = Spec (struct
    let stores = 2
    let opened = [ 0; 1 ]
    let leaky_close = false
  end)

module Held = Spec (struct
    let stores = 1
    let opened = [ 0 ]
    let leaky_close = false
  end)

module Seq_one = STM_sequential.Make (One)
module Seq_leaky = STM_sequential.Make (Leaky)
module Par_one = STM_domain.Make (One)
module Par_two = STM_domain.Make (Two)
module Par_held = STM_domain.Make (Held)

(* A slot's own commands while it holds its writer: advance and read, never open or close. *)
let arb_owner_two s _ =
  Two.arb_of
    QCheck.Gen.(oneof_weighted [ 3, return (Two.Advance s); 1, return (Two.Head s) ])
;;

let arb_owner_held _ =
  Held.arb_of
    QCheck.Gen.(oneof_weighted [ 3, return (Held.Advance 0); 1, return (Held.Head 0) ])
;;

(* Slot 1 trying the store slot 0 holds: open, read, close; never advance. *)
let arb_opener_held _ =
  Held.arb_of
    QCheck.Gen.(
      oneof_weighted
        [ 3, return (Held.Open 1); 1, return (Held.Head 1); 1, return (Held.Close 1) ])
;;

(* One slot's opens, reads and closes of the store both slots share. *)
let arb_open_close s st =
  One.arb_of
    QCheck.Gen.(
      oneof_weighted
        [ (if One.holds st s then 0 else 3), return (One.Open s)
        ; 1, return (One.Close s)
        ; 1, return (One.Head s)
        ])
;;

let () =
  let open Stm_support in
  let two_stores =
    Par_two.arb_triple 3 6 (fun st -> Two.arb_cmd st) (arb_owner_two 0) (arb_owner_two 1)
  in
  let racing_opens =
    Par_one.arb_triple 4 6 One.arb_cmd (arb_open_close 0) (arb_open_close 1)
  in
  let refused_opener =
    Par_held.arb_triple 2 6 arb_owner_held arb_owner_held arb_opener_held
  in
  run
    [ Seq_one.agree_test
        ~count:200
        ~name:"S1 E4_disk, one store and two slots, sequential"
    ; Seq_leaky.neg_agree_test
        ~count:300
        ~name:"S2 red: a close that leaves the writer open, sequential"
    ; par_test
        ~neg:false
        ~name:"P1 E4_disk, two stores, each advanced by its own domain"
        ~count:30
        ~repeats:4
        ~ok:Par_two.all_interleavings_ok
        two_stores
        Par_two.agree_prop_par
    ; par_test
        ~neg:false
        ~name:"K1 two domains open one store, and one passes the lock"
        ~count:60
        ~repeats:10
        ~ok:Par_one.all_interleavings_ok
        racing_opens
        Par_one.agree_prop_par
    ; par_test
        ~neg:false
        ~name:"K2 a refused open leaves the holder's commits intact"
        ~count:60
        ~repeats:10
        ~ok:Par_held.all_interleavings_ok
        refused_opener
        Par_held.agree_prop_par
    ]
;;
