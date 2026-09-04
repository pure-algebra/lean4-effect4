(* Witness 05: an inner handler that answers None, so `reperform` walks to the outer
   handler; the outer continues, and the restored chain still has the inner handler
   in it for the next perform.
   Transcribes `forwarded` of effects5_capabilities.ml:55-64.
   Machine arms: reperform-with-parent (interp.c:1383-1398, amd64.S:915-925) appending
   the current stack to the continuation chain's tail, then resume setting the
   OUTERMOST captured stack's parent to the resumer (interp.c:1295-1296). *)
open Effect
open Effect.Deep
type _ Effect.t += Number : int Effect.t | Outer : int Effect.t
let row s = print_string s; print_newline ()
let inner value main =
  try_with main ()
    { effc = (fun (type a) (e : a Effect.t) ->
        match e with
        | Number -> Some (fun (k : (a, int) continuation) ->
            row "inner-handled\tNumber";
            row (Printf.sprintf "continue\t%d" value);
            continue k value)
        | _ -> row "inner-forward"; None) }
let () =
  let r =
    try_with (fun () ->
      inner 2 (fun () ->
        row "perform\tOuter";
        let o = perform Outer in
        row (Printf.sprintf "got\t%d" o);
        row "perform\tNumber";
        let n = perform Number in
        row (Printf.sprintf "got\t%d" n);
        o + n)) ()
      { effc = (fun (type a) (e : a Effect.t) ->
          match e with
          | Outer -> Some (fun (k : (a, int) continuation) ->
              row "outer-handled\tOuter";
              row "continue\t40";
              continue k 40)
          | _ -> row "outer-forward"; None) }
  in
  row (Printf.sprintf "value\t%d" r)
