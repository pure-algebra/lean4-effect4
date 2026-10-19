(* ok_facade -- an installed client of the public facade (R6.2): the frozen paths, the type
   equalities, one run. It ignores its argument: the program is written here through the facade.
   Depends on: Effect4 (effect4_gen.effect4, installed). *)
let program : Effect4.Program.NativeOp.t Effect4.Program.Eff.t =
  Effect4.Program.Eff.Succeed (Effect4.Program.Term.Lit (Effect4.Program.Lit.Nat 42))

(* The facade's types are the owner's and the implementation's, not copies. *)
let (_ : Eff_types.NativeOp.t Eff_types.Eff.t) = program
let of_program =
  if Sys.opaque_identity true then Effect4.Run.Tree.of_program
  else Effect4_gen.Api_gen.run_tree_of_program
let _tree = of_program [] 100 program
let (_ : Effect4.Store.Val.t) = Effect4.Store.Val.Nat 7
let (_ : Effect4.Tool.Native.Workspace.t) = Effect4.Tool.Native.start
let (_ : Effect4.Program.Check.Memo.t) = Effect4.Program.Check.Memo.empty
let (_ : Effect4_gen.Api_gen.memo) = Effect4.Program.Check.Memo.empty
let _loop_with = Effect4.Program.Authoring.loop_with

let () =
  match Effect4.Run.Tree.settle [] 100 Effect4.Run.Tree.Host.silent () program with
  | Some (steps, _) ->
    Printf.printf "settled after %d steps; a nat is %s\n" steps
      (Effect4.Run.Kit.ty_text Effect4.Program.Ty.Nat)
  | None -> print_endline "not settled"
