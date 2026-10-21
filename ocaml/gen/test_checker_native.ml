(* V1 generated checker controls.
   P1 Module asks equal the source checker on the complete verdict.
   P2 A learned oracle retains positive extension answers and rechecks new rows.
   P3 Empty layers and reference refusals retain their source behavior.
   P4 Public explanation values can be learned without exposing Checked fields.
   These are finite native observations, not a translation theorem. *)
open Eff_types
module A = Effect4_gen.Api_gen

let check name condition =
  if not condition then failwith name;
  Printf.printf "PASS %s\n" name
;;

let app : A.sig_app = { rows = []; services = []; types = [] }
let nat : NativeOp.t Eff.t = Eff.Succeed (Term.Lit (Lit.Nat (Z.of_int 7)))
let bad : NativeOp.t Eff.t = Eff.Succeed (Term.Var (Z.of_int 0))

let decl : DefDecl.t =
  { name = "id"
  ; request = Ty.Nat
  ; answer = Ty.Nat
  ; error = Ty.Never
  ; requires = []
  ; role = DefRole.Plain
  ; params = []
  }
;;

let block : NativeOp.t Eff.t =
  Eff.Defs ([ decl ], Effs.Cons (bad, Effs.Nil), nat, LayerTerms.Nil)
;;

let empty : NativeOp.t Eff.t = Eff.Defs ([], Effs.Nil, nat, LayerTerms.Nil)

let layers : NativeOp.t Eff.t =
  Eff.Defs
    ([], Effs.Nil, nat, LayerTerms.Cons (LayerTerm.EffectDiscard bad, LayerTerms.Nil))
;;

let mismatch : NativeOp.t Eff.t =
  Eff.Defs
    ( [ decl ]
    , Effs.Nil
    , Eff.ProvideLayer (LayerTerm.Ref [ Z.of_int 9 ], false, nat)
    , LayerTerms.Nil )
;;

let ask oracle input =
  A.program_check_checked_read_verdict (A.program_check_checked_ask oracle input)
;;

let key program = A.CheckInput_module (app, [], program)

let row name answer : Row.t =
  { name
  ; spelling = name
  ; shape = RowShape.Call
  ; trailing = []
  ; kind = RowKind.Async
  ; request = Ty.Unit
  ; answer
  ; error = Ty.Never
  ; requires = []
  ; cite = "V1 fixture"
  ; type_args = []
  ; registration = Registration.External
  }
;;

let sig1 : A.sig_data =
  { app = { app with rows = [ row "a" Ty.Nat ] }; holes = []; part = A.PartSig_root }
;;

let sig2 : A.sig_data =
  { sig1 with app = { app with rows = [ row "a" Ty.Nat; row "b" Ty.String ] } }
;;

let call index : NativeOp.t Eff.t =
  Eff.Perform (NativeOp.External (Z.of_int index), Term.Lit Lit.Unit)
;;

let part sig_ index = A.CheckInput_part (sig_, [], call index)

let () =
  List.iteri
    (fun index program ->
       check
         (Printf.sprintf "module-full-verdict-%d" index)
         (ask A.program_check_oracle_uncached (key program)
          = A.program_check_run (key program)))
    [ nat; bad; block; empty; layers; mismatch ];
  check
    "empty-spine-accepted"
    (Result.is_ok (ask A.program_check_oracle_uncached (key empty)).result);
  check
    "layer-refusal-projected"
    (match (ask A.program_check_oracle_uncached (key layers)).result with
     | Error why -> List.equal Z.equal why.site [ Z.of_int 2; Z.zero; Z.zero ]
     | Ok _ -> false);
  check
    "reference-precedes-mismatch"
    (match (ask A.program_check_oracle_uncached (key mismatch)).result with
     | Error { reason = A.TypeReason_referenceIllFormed _; _ } -> true
     | _ -> false);
  let old = A.program_check_checked_ask A.program_check_oracle_uncached (part sig1 0) in
  let negative =
    A.program_check_checked_ask A.program_check_oracle_uncached (part sig1 1)
  in
  let memo =
    A.program_check_memo_learn
      (A.program_check_memo_learn A.program_check_memo_empty old)
      negative
  in
  let oracle =
    A.program_check_memo_oracle
      memo
      (A.program_check_hit_rule_or_
         A.program_check_hit_rule_exact
         A.program_check_extension)
  in
  check
    "positive-extension-complete-verdict"
    (ask oracle (part sig2 0) = A.program_check_run (part sig2 0));
  check
    "negative-new-row-rechecked"
    (ask oracle (part sig2 1) = A.program_check_run (part sig2 1)
     && Result.is_ok (ask oracle (part sig2 1)).result
     && Result.is_error (ask A.program_check_oracle_uncached (part sig1 1)).result);
  let explained = A.program_check_explain oracle (key layers) in
  let learned = A.program_check_memo_learn memo explained in
  check
    "explanation-learn-keeps-verdict"
    (ask (A.program_check_memo_oracle learned A.program_check_hit_rule_exact) (key layers)
     = A.program_check_run (key layers))
;;
