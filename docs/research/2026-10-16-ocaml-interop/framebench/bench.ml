(* bench.ml -- the framing kernel's writers, before and after F6, in one process.
   old_frame.ml is `git show 81f9a4354:ocaml/eff/eff_frame.ml`; landed_frame.ml is the branch's
   ocaml/eff/eff_frame.ml; pool_frame.ml adds a per-domain pool of payload buffers (measured, not
   landed). Each figure is the median of five CPU-time samples of at least 0.1 s. *)
type v = Nat of int | Str of string | Bool of bool | List of v list | Ctor of int * v list

module type F = sig
  val emit_nat : Buffer.t -> int -> unit
  val emit_string : Buffer.t -> string -> unit
  val emit_bool : Buffer.t -> bool -> unit
  val emit_list : Buffer.t -> (Buffer.t -> 'a -> unit) -> 'a list -> unit
  val emit_ctor : Buffer.t -> int -> (Buffer.t -> unit) -> unit
  val to_string : (Buffer.t -> 'a -> unit) -> 'a -> string
end

module E (F : F) = struct
  let rec emit b = function
    | Nat n -> F.emit_nat b n
    | Str s -> F.emit_string b s
    | Bool x -> F.emit_bool b x
    | List xs -> F.emit_list b emit xs
    | Ctor (i, a) -> F.emit_ctor b i (fun p -> List.iter (emit p) a)
  let to_bytes v = F.to_string emit v
end

module O = E (Old_frame)
module L = E (Landed_frame)
module P = E (Pool_frame)

let todo i =
  Ctor (0, [ List [ Str "done"; Str "id"; Str "title" ];
             List [ Bool (i mod 2 = 0); Nat i; Str (Printf.sprintf "item %d" i) ] ])

let sample f =
  let rec go n =
    let t0 = Sys.time () in
    for _ = 1 to n do ignore (Sys.opaque_identity (f ())) done;
    let dt = Sys.time () -. t0 in
    if dt < 0.1 then go (n * 2) else dt /. float_of_int n
  in
  go 1

let time f = List.nth (List.sort Float.compare (List.init 5 (fun _ -> sample f))) 2

let () =
  let deep = let rec go d = if d = 0 then Nat 1 else List [ go (d - 1); Nat d ] in go 40 in
  List.iter
    (fun (name, v) ->
      if O.to_bytes v <> L.to_bytes v || O.to_bytes v <> P.to_bytes v then failwith "bytes differ";
      let o = time (fun () -> O.to_bytes v) and l = time (fun () -> L.to_bytes v)
      and p = time (fun () -> P.to_bytes v) in
      Printf.printf "%-11s old %7.2f us  landed %7.2f us (x%.2f)  pool %7.2f us (x%.2f)\n" name
        (o *. 1e6) (l *. 1e6) (o /. l) (p *. 1e6) (o /. p))
    [ ("100 to-dos", List (List.init 100 todo)); ("depth 40", deep); ("one to-do", todo 7) ]
