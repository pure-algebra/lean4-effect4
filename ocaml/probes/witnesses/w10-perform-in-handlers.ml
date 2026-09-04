(* Witness 10: perform from inside retc and from inside exnc. Both run on the PARENT
   stack after the child was freed (do_return / raise_notrace, interp.c:575-594,
   :980-1000; frame_runstack / fiber_exn_handler, amd64.S:1003-1024), so their performs
   are seen by the enclosing handler, not by the handler they belong to. *)
open Effect
open Effect.Deep
type _ Effect.t += Number : int Effect.t
exception Boom
let row s = print_string s; print_newline ()
let () =
  let r =
    try_with (fun () ->
      let a =
        match_with (fun () -> row "inner-body\tvalue"; 1) ()
          { retc = (fun v -> row "in-retc"; v + perform Number);
            exnc = (fun e -> raise e);
            effc = (fun (type a) (_ : a Effect.t) -> row "inner-forward"; None) } in
      row (Printf.sprintf "a\t%d" a);
      let b =
        match_with (fun () -> row "inner-body\traise"; raise Boom) ()
          { retc = (fun v -> row "unreachable"; v);
            exnc = (fun _ -> row "in-exnc"; perform Number);
            effc = (fun (type a) (_ : a Effect.t) -> row "inner-forward"; None) } in
      row (Printf.sprintf "b\t%d" b);
      a + b) ()
      { effc = (fun (type a) (e : a Effect.t) ->
          match e with
          | Number -> Some (fun (k : (a, int) continuation) ->
              row "outer-handled\tNumber";
              row "continue\t100";
              continue k 100)
          | _ -> None) }
  in
  row (Printf.sprintf "value\t%d" r)
