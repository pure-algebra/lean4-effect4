(* A0 deliverable 2: the JS closure boundary, both ways, under js_of_ocaml 5.7.1
   `--enable effects`.

   Four probes:
     A  an OCaml closure exported to JS and called back from JS with a JS closure argument
        (the `caml_js_wrap_callback` -> `caml_callback` path, `jslib.js:304-318`, `:70-113`);
     B  a real JS `function` held in OCaml state, called from inside an effect handler, with
        the JS closure's captured mutable variable observed after the call;
     C  the crux: `perform` inside an OCaml callback invoked from JS -- does it reach the
        handler installed outside the JS call? C1 is the plain case, C2 the nested case (the
        JS call happens inside a *resumed* continuation), C3 the control with no JS in the
        middle;
     D  the value profile at the boundary: `.l` arity, `caml_call_gen` partial and
        over-application (spike O3 §7).

   Everything crossing the boundary is an `int` or a `string`, per the O3 value profile,
   except the two closure values themselves, which are the point of the probe. *)

type jsval  (* an opaque JavaScript value; jsoo represents it directly *)

external log : string -> unit = "a0_log"
external dump : unit -> unit = "a0_dump"

(* A: hand JS an OCaml closure of two arguments; JS wraps it and calls it back with an int
   and a JS closure. *)
external call_ocaml_from_js : (int -> jsval -> int) -> int = "a0_call_ocaml_from_js"

(* Call a JS closure held on the OCaml side. *)
external js_call1 : jsval -> int -> int = "a0_js_call1"

(* B: a real JS function with a captured mutable variable, and a reader for it. *)
external make_js_closure : unit -> jsval = "a0_make_js_closure"
external read_js_counter : unit -> int = "a0_read_counter"

(* C: JS invokes an OCaml thunk. *)
external invoke_from_js : (unit -> int) -> int = "a0_invoke_from_js"

(* D: the representation of a closure as JS sees it. *)
external probe_repr : jsval -> string = "a0_probe_repr"
external probe_ocaml_closure : (int -> int -> int) -> string = "a0_probe_repr"
external apply_partial : (int -> int -> int) -> string = "a0_apply_partial"

type _ Effect.t += Ask : int -> int Effect.t

exception Boom

let handler_ran = ref 0

(* The scheduler-shaped handler: one deep handler, installed once, outside every JS call. *)
let run (main : unit -> unit) : unit =
  let open Effect.Deep in
  match_with main ()
    { retc = (fun () -> log "K:retc");
      exnc = (fun e -> log ("K:exnc " ^ Printexc.to_string e));
      effc =
        (fun (type a) (eff : a Effect.t) : ((a, unit) continuation -> unit) option ->
          match eff with
          | Ask n ->
            Some
              (fun k ->
                incr handler_ran;
                log (Printf.sprintf "H:handled Ask %d" n);
                continue k (n * 10))
          | _ -> None) }

let () =
  dump ();
  (* --------------------------------------------------------------- probe D: values *)
  log ("D:ocaml-closure-repr " ^ probe_ocaml_closure (fun a b -> a + b));
  log ("D:partial-application " ^ apply_partial (fun a b -> a + b));

  (* --------------------------------------------------------------- probe A *)
  (* JS wraps this OCaml closure and calls it with (7, jsClosure). The OCaml body calls the
     JS closure it was handed. *)
  let a =
    call_ocaml_from_js (fun n f ->
        log (Printf.sprintf "A:ocaml-callback-entered n=%d" n);
        log ("A:js-closure-repr " ^ probe_repr f);
        let r = js_call1 f n in
        log (Printf.sprintf "A:js-closure-returned %d" r);
        r + 1)
  in
  log (Printf.sprintf "A:result %d" a);

  (* --------------------------------------------------------------- probe B *)
  let cell : jsval option ref = ref None in
  cell := Some (make_js_closure ());
  log (Printf.sprintf "B:counter-before %d" (read_js_counter ()));
  run (fun () ->
      (* the JS closure is called from inside the handler's dynamic extent, through an
         effect: `perform (Ask _)` first, then the stored JS closure. *)
      let v = Effect.perform (Ask 4) in
      log (Printf.sprintf "B:perform-answered %d" v);
      let f = match !cell with Some f -> f | None -> assert false in
      let r = js_call1 f v in
      log (Printf.sprintf "B:js-closure-in-handler-returned %d" r));
  log (Printf.sprintf "B:counter-after %d" (read_js_counter ()));

  (* --------------------------------------------------------------- probe C1 *)
  (* A handler is installed here; inside it, JS calls an OCaml thunk that performs. *)
  run (fun () ->
      log "C1:before";
      (try
         let r = invoke_from_js (fun () -> Effect.perform (Ask 1)) in
         log (Printf.sprintf "C1:returned %d" r)
       with e -> log ("C1:caught-in-ocaml " ^ Printexc.to_string e));
      log "C1:after");

  (* --------------------------------------------------------------- probe C2 *)
  (* The nested case: the JS call happens inside a *resumed* continuation, so the OCaml
     stack under the JS frame is one that `caml_resume_stack` reinstalled. *)
  run (fun () ->
      log "C2:before";
      let v = Effect.perform (Ask 2) in
      log (Printf.sprintf "C2:resumed %d" v);
      (try
         let r = invoke_from_js (fun () -> Effect.perform (Ask 3)) in
         log (Printf.sprintf "C2:returned %d" r)
       with e -> log ("C2:caught-in-ocaml " ^ Printexc.to_string e));
      log "C2:after");

  (* --------------------------------------------------------------- probe C3 (control) *)
  run (fun () ->
      log "C3:before";
      let r = (fun () -> Effect.perform (Ask 5)) () in
      log (Printf.sprintf "C3:returned %d" r));

  log (Printf.sprintf "H:handler-ran %d" !handler_ran)
