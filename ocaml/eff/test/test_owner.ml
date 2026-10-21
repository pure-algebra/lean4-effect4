(* test_owner.ml -- the program types at their owner, read by a client.

   What it is: a client of Eff_types as slice 1.2a declares it: each Lean type its own module,
   its type `t`, its constructors and fields by their Lean names (Eff.Succeed, Ty.Never, Val.Nat).
   It builds programs over the Eff-Stmt-Stmts cycle, traverses them with their operation type
   kept, and reads the generated tables and the program codec on them.
   Depends on: Eff_types, Eff_ctors, Eff_codec.

   Properties:
   O1  One traversal of the cycle (Eff, Stmt, Stmts) serves programs over two operation types:
       its type parameter is kept (a polymorphic recursion at 'op).        tested
   O2  The generated tables name the owner's constructors by the Lean names. tested
   O3  The program codec (Lean's exact embedding, lowered) writes a program built here and
       reads back the same bytes, and a record of the owner (ServiceKey) by its fields
       inside a program that holds it.                                    tested
   O4  The cycle's 'op is invariant (OCaml checks a recursive group against
       approximations): a program shared at two operation types is a value
       or a function, never an expansive expression.                       by construction
       (`ocamlopt`: `body` below is a function for this reason) *)

open Eff_types

let failures = ref 0

let check name ok =
  Printf.printf "%s  %s\n" (if ok then "PASS" else "FAIL") name;
  if not ok then incr failures
;;

let rec size_eff : 'op. 'op Eff.t -> int = function
  | Eff.Gen ss -> 1 + size_stmts ss
  | Eff.Bind (a, b) -> 1 + size_eff a + size_eff b
  | Eff.Suspend e -> 1 + size_eff e
  | _ -> 1

and size_stmts : 'op. 'op Stmts.t -> int = function
  | Stmts.Nil -> 0
  | Stmts.Cons (s, rest) -> size_stmt s + size_stmts rest

and size_stmt : 'op. 'op Stmt.t -> int = function
  | Stmt.BindYield e | Stmt.YieldDiscard e -> size_eff e
  | Stmt.IfElse (_, a, b) -> 1 + size_stmts a + size_stmts b
  | Stmt.WhileTrue b -> 1 + size_stmts b
  | Stmt.Ret _ | Stmt.BreakLoop -> 1
;;

let nat n = Term.Lit (Lit.Nat (Z.of_int n))
let body () : 'op Stmts.t = Stmts.Cons (Stmt.Ret (nat 1), Stmts.Nil)

let program op : 'op Eff.t =
  Eff.Gen (Stmts.Cons (Stmt.BindYield (Eff.Perform (op, nat 0)), body ()))
;;

let () =
  let native : NativeOp.t Eff.t = program NativeOp.ClockNow in
  let named : string Eff.t = program "row" in
  check
    "O1 one traversal at NativeOp.t and at string, 'op kept"
    (size_eff native = 3 && size_eff named = 3);
  check
    "O2 the constructor tables name Ty.Never and Eff.Succeed by the Lean names"
    (Eff_ctors.ctor_name_ty Ty.Never = "never"
     && Eff_ctors.ctor_name_eff (Eff.Succeed (nat 0)) = "succeed");
  let bytes = Eff_codec.encode_program native in
  check
    "O3 a program built here reads back to the same bytes"
    (match Eff_codec.decode_program bytes with
     | Some p -> Eff_codec.encode_program p = bytes
     | None -> false);
  let key = { ServiceKey.name = Z.of_int 1; service = Z.of_int 2 } in
  check
    "O3 a record of the owner by its fields reads back"
    (match Eff_codec.decode_program (Eff_codec.encode_program (Eff.Service key)) with
     | Some (Eff.Service k) ->
       Z.equal k.ServiceKey.name (Z.of_int 1) && Z.equal k.ServiceKey.service (Z.of_int 2)
     | _ -> false);
  if !failures > 0 then exit 1
;;
