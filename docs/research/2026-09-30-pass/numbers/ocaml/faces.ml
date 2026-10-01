(* Numbers seat, probe 2: the OCaml engine on the faces program.

   What it is: a thin driver over the built engine library (ocaml/_build, cut at be15b062).
   It reads the canonical program bytes as hex (argv 1, printed by ../Faces.lean), decodes
   them through the engine's own `load_bytes` (Eff_wire, then E4_program), drives the run
   `Api.run` drives -- [evaluate root; flush] -- at fuel 1000 on both instances, and prints
   the outcome and the root exit as the engine renders them. It also prints the outcome of
   the instance's own generated `Effect4.Api.run`.

   Then it evaluates the same five operations with the OCaml forms the LCNF table emits
   (src/OCaml5/Lcnf/Translate.lean:162-176; E4_nat.div / E4_nat.rem through
   ocaml/engine/externs.txt:163-164), so each engine number can be traced to one operation.

   Depends on: effect4_engine, effect4_eff, effect4_clock (zarith). Writes nothing. *)

open Effect4_engine

module Run (En : E4_engine.ENGINE) = struct
  let go (bytes : string) =
    match En.load_bytes bytes ~fuel:1000 with
    | None -> Printf.printf "%-4s decode refused\n" En.name
    | Some t ->
      let t = En.drive t in
      Printf.printf "%-4s outcome=%s root_exit=%s\n" En.name (En.outcome t)
        (match En.root_exit t with None -> "<none>" | Some s -> s);
      (match En.of_bytes bytes with
       | Some p -> Printf.printf "%-4s generated Api.run outcome=%s\n" En.name (En.api_run p ~fuel:1000)
       | None -> Printf.printf "%-4s of_bytes refused\n" En.name)
end

module RF = Run (E4_engine.Fast)
module RR = Run (E4_engine.Ref)

(* The table's forms, written out: raw `+` for Nat.add (Translate.lean:162), the saturating
   product for Nat.mul (:163-169), `max 0 (a - b)` for Nat.sub (:172-174), `<` for Nat.decLt
   (:160), E4_nat.div / E4_nat.rem for Nat.div / Nat.mod. *)
let add a b = a + b
let mul a b = if a = 0 then 0 else if b > max_int / a then max_int else a * b
let sub a b = max 0 (a - b)

let () =
  let hex = Sys.argv.(1) in
  (match E4_hex.to_bytes hex with
   | None -> print_endline "hex refused"
   | Some bytes ->
     Printf.printf "bytes %d\n" (String.length bytes);
     RF.go bytes;
     RR.go bytes);
  Printf.printf "max_int=%d int_size=%d\n" max_int Sys.int_size;
  let a0 = add 4503599627370496 4503599627370497 in
  let a1 = sub a0 9007199254740991 in
  let a2 = mul 4503599627370496 512 in
  let a3 = add a2 (add a2 5) in
  let a4 = mul a0 512 in
  Printf.printf "a0=%d a1=%d a2=%d a3=%d a4=%d\n" a0 a1 a2 a3 a4;
  Printf.printf "lt(a3,1)=%b div(a3,2)=%d sub(sub(a3,a2),a2)=%d mod(a4,1000)=%d\n"
    (a3 < 1) (E4_nat.div a3 2) (sub (sub a3 a2) a2) (E4_nat.rem a4 1000)
