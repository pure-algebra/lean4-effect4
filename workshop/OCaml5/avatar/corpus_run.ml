(* The avatar's interpreter for the corpus DSL (`corpus_dsl.ml`). One step is one service
   operation; the same text is interpreted by `corpus_rc112.mjs` over rc.112. *)

open Deep_fibers
open Corpus_dsl

let globals : value array = Array.make 64 Vunit

(* The stack of flags saved by the `mask` steps of the fiber currently on the OCaml stack. *)
let masked : value list ref = ref []

let rec vof slots = function
  | Lit n -> Vnat n
  | Local i -> slots.(i)
  | Global g -> globals.(g)
  | List xs -> Vlist (List.map (vof slots) xs)

let iof slots a = match vof slots a with Vnat n -> n | Vhandle h -> h | _ -> 0
let hof slots a = match vof slots a with Vhandle h -> h | Vnat n -> n | _ -> 0

let handles slots a =
  match vof slots a with
  | Vlist xs -> List.map (function Vhandle h -> h | Vnat n -> n | _ -> 0) xs
  | Vhandle h -> [ h ]
  | Vnat n -> [ n ]
  | _ -> []

let ints slots a =
  match vof slots a with
  | Vlist xs -> List.map (function Vnat n -> n | Vhandle h -> h | _ -> 0) xs
  | Vnat n -> [ n ]
  | _ -> []

let step slots (st : step) : value =
  let a i = List.nth st.args i in
  match st.op with
  (* fibers *)
  | "fork" -> Effect.perform (Op_fork (iof slots (a 0), false))
  | "forkDetach" -> Effect.perform (Op_fork (iof slots (a 0), true))
  | "join" -> Effect.perform (Op_join (hof slots (a 0)))
  | "awaitValue" -> Effect.perform (Op_await_value (hof slots (a 0)))
  | "awaitError" -> Effect.perform (Op_await_error (hof slots (a 0)))
  | "interrupt" -> Effect.perform (Op_interrupt (hof slots (a 0)))
  | "interruptAll" -> Effect.perform (Op_interrupt_all (handles slots (a 0)))
  | "awaitAll" -> Effect.perform (Op_await_all (handles slots (a 0)))
  | "childrenSnapshot" -> Effect.perform (Op_snapshot_children ())
  | "awaitChildren" -> Effect.perform (Op_await_new_children (vof slots (a 0)))
  | "raceAll" -> Effect.perform (Op_race_all (if st.args = [] then [] else ints slots (a 0)))
  | "yield" ->
    push_row (Rop ("yield", Vunit));
    let v = Effect.perform (Op_yield_now 0) in
    push_row (Ranswer ("yield", Vunit));
    v
  (* `WithFiberAction.setInterruptible` answers the previous flag, and the DSL brackets on
     it, so nested masks nest the way `Effect.uninterruptible` regions do. `masked` is the
     stack of saved flags of the enclosing `mask`s. *)
  | "mask" ->
    let previous = Effect.perform (Op_set_interruptible false) in
    masked := previous :: !masked;
    previous
  | "unmask" ->
    let previous = match !masked with p :: rest -> masked := rest; p | [] -> Vbool true in
    Effect.perform (Op_set_interruptible (match previous with Vbool b -> b | _ -> true))
  | "never" -> Effect.perform (Op_never ())
  | "started" -> Effect.perform (Op_started ())
  | "cleanups" -> Effect.perform (Op_cleanups ())
  | "refuse" -> Effect.perform (Op_refuse "raceAll")
  (* refs *)
  | "refMake" -> Effect.perform (Op_ref_make (iof slots (a 0)))
  | "refGet" -> Effect.perform (Op_ref_get (hof slots (a 0)))
  | "refSet" -> Effect.perform (Op_ref_set (hof slots (a 0), iof slots (a 1)))
  | "refUpdate" -> Effect.perform (Op_ref_update (hof slots (a 0), iof slots (a 1)))
  | "refModify" -> Effect.perform (Op_ref_modify (hof slots (a 0), iof slots (a 1)))
  | "refGetAndSet" -> Effect.perform (Op_ref_get_and_set (hof slots (a 0), iof slots (a 1)))
  | "refTryTake" -> Effect.perform (Op_ref_try_take (hof slots (a 0), iof slots (a 1)))
  (* deferreds *)
  | "defMake" -> Effect.perform (Op_def_make ())
  | "defSucceed" -> Effect.perform (Op_def_succeed (hof slots (a 0), iof slots (a 1)))
  | "defFail" -> Effect.perform (Op_def_fail (hof slots (a 0), iof slots (a 1)))
  | "defIsDone" -> Effect.perform (Op_def_is_done (hof slots (a 0)))
  | "defPoll" -> Effect.perform (Op_def_poll (hof slots (a 0)))
  | "defAwaitValue" -> Effect.perform (Op_def_await_value (hof slots (a 0)))
  | "defAwaitError" -> Effect.perform (Op_def_await_error (hof slots (a 0)))
  (* scopes *)
  | "scopeMake" -> Effect.perform (Op_scope_make ())
  | "scopeAdd" -> Effect.perform (Op_scope_add (hof slots (a 0), iof slots (a 1)))
  | "scopeRemove" -> Effect.perform (Op_scope_remove (hof slots (a 0), iof slots (a 1)))
  | "scopeClose" -> Effect.perform (Op_scope_close (hof slots (a 0)))
  (* layers *)
  | "layerBuild" -> Effect.perform (Op_layer_build (iof slots (a 0)))
  | "layerProvideCount" -> Effect.perform (Op_layer_provide_count (iof slots (a 0)))
  | "layerScopeOf" -> Effect.perform (Op_layer_scope_of (hof slots (a 0)))
  | "layerClose" -> Effect.perform (Op_layer_close ())
  (* terminals *)
  | "succeed" -> Vnat (iof slots (a 0))
  | "failWith" -> raise (Efail_exn (iof slots (a 0)))
  | "ret" -> vof slots (a 0)
  | other -> failwith ("unknown corpus op " ^ other)

let run_steps (steps : step list) : value =
  let slots = Array.make (List.length steps + 1) Vunit in
  let last = ref Vunit in
  List.iteri
    (fun i st ->
      let v = step slots st in
      slots.(i) <- v;
      (match st.publish with Some g -> globals.(g) <- v | None -> ());
      last := v)
    steps;
  !last

(* Install the program's root table. A code the program does not declare falls back to the
   standard body table of `harness/trace/fiber-tail.ts`, so a corpus program can reuse the
   golden bodies (0 succeeds 11, 1 succeeds 22, 2 fails 1, 3 fails 2, 4 never). *)
let install (p : prog) : unit =
  Array.fill globals 0 (Array.length globals) Vunit;
  masked := [];
  body_of_code :=
    fun code ->
      match List.assoc_opt code p.roots with
      | None -> Fibers_fixture.body code
      | Some steps ->
        fun () ->
          Fun.protect
            ~finally:(fun () -> state.cleanups <- state.cleanups @ [ code ])
            (fun () ->
              state.started <- state.started @ [ code ];
              run_steps steps)

let program (p : prog) : unit -> value = fun () -> run_steps p.main
