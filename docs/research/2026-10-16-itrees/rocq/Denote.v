(** * Denote: an interaction-tree meaning of a fragment of Effect4's [Eff]

    The syntax is [E4.Eff_types], which rocq-of-ocaml made from the LCNF route's
    [ocaml/eff/eff_types.ml] (split into its components by [gen/split_types.ml]). Nothing of the
    syntax is copied by hand. What this file writes by hand is the meaning: a transcription of
    Lean's [denoteRows] ([src/Effect4/Laws/Program/DenoteRows.lean]) and of the compiler's
    arms for definitions ([suspendBodyAt], [src/Effect4/Program/Compile.lean]), as an
    interaction tree. Each arm names the Lean definition it transcribes.

    The fragment: [succeed], [fail], [sync], [suspend], [bind], [select], the host rows
    ([perform (external i)]), the three cell rows ([refMake], [refGet], [refSet]), definitions
    ([defs], [call], [invoke], [param]), the context ([provideContext], [withFiber (context _)])
    and loops ([iterate]). Every other constructor answers [outside], a marked exit that no Lean
    run writes, so a program that reaches it cannot agree with a recorded run by accident.

    What differs from Lean's tree:
    - Definitions are recursive: a call is an event [Run] that [mrec] answers, so a definition
      that calls itself is a meaning, not a refusal. Lean's [denoteRows] has no definition arm.
    - A loop is [ITree.iter], with no budget. Lean's [denoteRowsB k] cuts it at [k]; a loop that
      never ends here is a silent infinite run, not a budget cut.
    - The context is a value the meaning carries. Lean decodes it ([Val.context?]); here it is
      kept as it is, which is enough because no context reaches a host call or an exit in the
      fixtures (checked by their agreement, [TodoCheck.v]). *)

From Stdlib Require Import List ZArith String Bool.
Import ListNotations.
From ITree Require Import ITree.
Import ITreeNotations.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import E4.Eff_types.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

(** ** Exits *)

(** An exit, as a host call's continuation and the root see it: a success with its value, or a
    failure with the exit's whole image, which the meaning passes on and never reads. *)
Inductive exitv : Set :=
| Success (v : val_)
| Failure (image : val_).

(** The image of an exit, [exitImage] in Lean: [ctor 0 [v]] for a success. *)
Definition exit_image (e : exitv) : val_ :=
  match e with Success v => Val_ctor 0 [v] | Failure image => image end.

(** The exit an exit image writes, as a reply on a tape carries it. *)
Definition exit_of_image (image : val_) : exitv :=
  match image with Val_ctor 0 [v] => Success v | _ => Failure image end.

(** [errOf]'s image ([Program.errOf], [src/Effect4/Machine/Term.lean]): a natural is a tag, a
    string a text, a pair of strings a tagged failure. Lean reads any other value through
    [Payload.image]; here it is a payload as it stands (not exercised by the fixtures). *)
Definition err_image (v : val_) : val_ :=
  match v with
  | Val_nat n => Val_ctor 1 [Val_nat n]
  | Val_str s => Val_ctor 3 [Val_str s]
  | Val_list [Val_str tag; Val_str message] => Val_ctor 2 [Val_str tag; Val_str message]
  | v => Val_ctor 4 [v]
  end.

(** [Exit.failure (Cause.fail (errOf v))]: one fail reason with no annotation. *)
Definition fail_exit (v : val_) : exitv :=
  Failure (Val_ctor 1 [Val_ctor 0 [Val_list [Val_ctor 0 [err_image v; Val_ctor 0 [Val_list []]]]]]).

(** Two marked exits: a term of the wrong shape, and a constructor outside the fragment. *)
Definition bad_shape : exitv := Failure (Val_str "denote: bad shape").
Definition outside : exitv := Failure (Val_str "denote: outside the fragment").

(** ** Terms ([evalTerm], [src/Effect4/Machine/Term.lean]) *)

Definition lit_val (l : lit) : val_ :=
  match l with
  | Lit_unit => Val_unit
  | Lit_nat n => Val_nat n
  | Lit_bool b => Val_bool b
  | Lit_str s => Val_str s
  end.

(** The atoms the fixtures use, each as [NativeAtom.eval] answers it at these arguments. Any other
    atom, and these atoms at other arguments, refuse ([None]), as Lean refuses outside its table. *)
Definition atom (name : string) (vs : list val_) : option val_ :=
  if String.eqb name "pair" then match vs with [a; b] => Some (Val_list [a; b]) | _ => None end
  else if String.eqb name "fst" then match vs with [Val_list (a :: _)] => Some a | _ => None end
  else if String.eqb name "snd" then match vs with [Val_list (_ :: b :: _)] => Some b | _ => None end
  else if String.eqb name "eq" then
    match vs with
    | [Val_nat a; Val_nat b] => Some (Val_bool (Z.eqb a b))
    | [Val_str a; Val_str b] => Some (Val_bool (String.eqb a b))
    | [Val_bool a; Val_bool b] => Some (Val_bool (Bool.eqb a b))
    | _ => None
    end
  else if String.eqb name "some" then match vs with [a] => Some (Val_some a) | _ => None end
  else if String.eqb name "none" then match vs with [] => Some Val_none | _ => None end
  else if String.eqb name "and" then
    match vs with [Val_bool a; Val_bool b] => Some (Val_bool (a && b)) | _ => None end
  else if String.eqb name "not" then match vs with [Val_bool b] => Some (Val_bool (negb b)) | _ => None end
  else if String.eqb name "lt" then
    match vs with [Val_nat a; Val_nat b] => Some (Val_bool (Z.ltb a b)) | _ => None end
  else if String.eqb name "mul" then
    match vs with [Val_nat a; Val_nat b] => Some (Val_nat (a * b)) | _ => None end
  else None.

(** Records ([Machine.Record], [src/Effect4/Machine/Record.lean]): a record is the frame
    [ctor 0 [names; values]], its fields ascending by their bytes. *)
Fixpoint zip_names (ns : list string) (vs : list val_) : option (list (string * val_)) :=
  match ns, vs with
  | [], [] => Some []
  | n :: ns', v :: vs' => option_map (cons (n, v)) (zip_names ns' vs')
  | _, _ => None
  end.

Fixpoint insert_field (f : string * val_) (l : list (string * val_)) : list (string * val_) :=
  match l with
  | [] => [f]
  | g :: rest => if String.ltb (fst g) (fst f) then g :: insert_field f rest else f :: l
  end.

(** The standard [fold_right], named in full: the translation library's [fold_right] takes
    OCaml's argument order (function, list, initial value). *)
Definition canon (l : list (string * val_)) : list (string * val_) :=
  Stdlib.Lists.List.fold_right insert_field [] l.

Fixpoint nodup_names (ns : list string) : bool :=
  match ns with
  | [] => true
  | n :: rest => negb (existsb (String.eqb n) rest) && nodup_names rest
  end.

Definition frame (fs : list (string * val_)) : val_ :=
  Val_ctor 0 [Val_list (map (fun f => Val_str (fst f)) fs); Val_list (map snd fs)].

Definition record_build (ns : list string) (vs : list val_) : option val_ :=
  match zip_names ns vs with
  | Some fs => if nodup_names ns then Some (frame (canon fs)) else None
  | None => None
  end.

Fixpoint read_columns (ns vs : list val_) : option (list (string * val_)) :=
  match ns, vs with
  | [], [] => Some []
  | Val_str n :: ns', v :: vs' => option_map (cons (n, v)) (read_columns ns' vs')
  | _, _ => None
  end.

Fixpoint first_of (n : string) (l : list (string * val_)) : option val_ :=
  match l with
  | [] => None
  | (m, v) :: rest => if String.eqb m n then Some v else first_of n rest
  end.

Definition record_read (optional : bool) (v : val_) (n : string) : option val_ :=
  match v with
  | Val_ctor 0 [Val_list ns; Val_list vs] =>
    match read_columns ns vs with
    | Some fs =>
      if nodup_names (map fst fs) then
        let found := first_of n fs in
        if optional then Some (match found with Some x => Val_some x | None => Val_none end)
        else found
      else None
    | None => None
    end
  | _ => None
  end.

Fixpoint eval_term (env : list val_) (t : term) {struct t} : option val_ :=
  match t with
  | Term_var i => nth_error env (Z.to_nat i)
  | Term_lit l => Some (lit_val l)
  | Term_app name args =>
    match eval_terms env args with Some vs => atom name vs | None => None end
  | Term_record _ names args =>
    match eval_terms env args with Some vs => record_build names vs | None => None end
  | Term_field mode target name =>
    match eval_term env target with
    | Some v => record_read (match mode with FieldReadMode_optional => true | _ => false end) v name
    | None => None
    end
  | _ => None
  end
with eval_terms (env : list val_) (ts : terms) {struct ts} : option (list val_) :=
  match ts with
  | Terms_nil => Some []
  | Terms_cons t rest =>
    match eval_term env t, eval_terms env rest with
    | Some v, Some vs => Some (v :: vs)
    | _, _ => None
    end
  end.

(** [Decision.decide] ([src/Effect4/Program/Decision.lean]): which branch, and what it binds.
    An option's [none] chooses the first branch, its [some a] the second, binding [a]. *)
Definition decide (d : decision) (v : val_) : option (bool * list val_) :=
  match d, v with
  | Decision_bool, Val_bool b => Some (b, [])
  | Decision_option, Val_none => Some (true, [])
  | Decision_option, Val_some a => Some (false, [a])
  | _, _ => None
  end.

(** ** Events *)

(** A host row: its position and the request. The answer is the exit the reply gives. *)
Variant RowE : Type -> Type :=
| Row (i : int) (request : val_) : RowE exitv.

(** The three cell rows of the store ([SyncOp]); each answers a value. *)
Variant StoreE : Type -> Type :=
| RefMake (initial : val_) : StoreE val_
| RefGet (cell : val_) : StoreE val_
| RefSet (cell v : val_) : StoreE val_.

(** A frame of the parameters' stack: the programs an invocation passed and the caller's
    environment they run in ([ArgSite]). *)
Definition frame_args : Set := (list (eff native_op) * list val_)%type.

(** Run a program at an environment, a parameters' stack and a context: the event a call, an
    invocation and a parameter's run raise, and [mrec] answers. *)
Variant RunE : Type -> Type :=
| Run (e : eff native_op) (env : list val_) (params : list frame_args) (ctx : val_) : RunE exitv.

Fixpoint effs_list (es : effs native_op) : list (eff native_op) :=
  match es with Effs_nil => [] | Effs_cons e rest => e :: effs_list rest end.

(** ** The meaning *)

(** The events a meaning raises before [mrec] answers its runs. *)
Notation E0 := (RunE +' StoreE +' RowE).

Section Denote.

Context (bodies : list (eff native_op)).

(** Sequencing: a failure ends the sequence with itself ([seqRows]). *)
Definition seq (t : itree E0 exitv) (k : val_ -> itree E0 exitv) : itree E0 exitv :=
  ITree.bind t (fun x => match x with Success v => k v | Failure _ => Ret x end).

Definition ret_val (o : option val_) : itree E0 exitv :=
  Ret (match o with Some v => Success v | None => bad_shape end).

(** One loop round at the cursor [c] ([loopStep], [src/Effect4/Laws/Program/DenoteRowsB.lean]):
    [inr c'] runs again at [c'], [inl ex] ends the loop with [ex]. *)
Definition loop_step (body : list val_ -> itree E0 exitv) (env : list val_) (test step result : term)
    (c : val_) : itree E0 (val_ + exitv) :=
  match eval_term (env ++ [c]) test with
  | Some (Val_bool true) =>
    ITree.bind (body (env ++ [c])) (fun x =>
      match x with
      | Failure _ => Ret (inr x)
      | Success a =>
        match eval_term (env ++ [c; a]) step with
        | Some c' => Ret (inl c')
        | None => Ret (inr bad_shape)
        end
      end)
  | Some (Val_bool false) =>
    Ret (inr (match eval_term (env ++ [c]) result with Some v => Success v | None => bad_shape end))
  | _ => Ret (inr bad_shape)
  end.

Fixpoint denote (e : eff native_op) (env : list val_) (ps : list frame_args) (ctx : val_)
    {struct e} : itree E0 exitv :=
  match e with
  | Eff_succeed t => ret_val (eval_term env t)
  | Eff_fail t =>
    Ret (match eval_term env t with Some v => fail_exit v | None => bad_shape end)
  | Eff_sync t => Ret (Success (match eval_term env t with Some v => v | None => Val_unit end))
  | Eff_suspend b => denote b env ps ctx
  | Eff_perform op r =>
    match eval_term env r with
    | None => Ret bad_shape
    | Some v =>
      match op with
      (* a host row: one call, whose reply is the continuation's exit ([rowCall]) *)
      | NativeOp_external i => trigger (Row i v)
      | NativeOp_refMake => ITree.map Success (trigger (RefMake v))
      | NativeOp_refGet => ITree.map Success (trigger (RefGet v))
      | NativeOp_refSet =>
        match v with
        | Val_list [c; w] => ITree.map Success (trigger (RefSet c w))
        | _ => Ret bad_shape
        end
      (* a call: definition [k]'s body at the request alone, an empty frame pushed
         ([suspendBodyAt]'s [call] arm) *)
      | NativeOp_call k =>
        match nth_error bodies (Z.to_nat k) with
        | Some body => trigger (Run body [v] (([], []) :: ps) ctx)
        | None => Ret bad_shape
        end
      (* a parameter: the innermost invocation's program [i], at its caller's environment and
         the request, at the stack below that invocation *)
      | NativeOp_param i =>
        match ps with
        | (args, fenv) :: below =>
          match nth_error args (Z.to_nat i) with
          | Some a => trigger (Run a (fenv ++ [v]) below ctx)
          | None => Ret bad_shape
          end
        | [] => Ret bad_shape
        end
      | _ => Ret outside
      end
    end
  | Eff_bind a b => seq (denote a env ps ctx) (fun v => denote b (env ++ [v]) ps ctx)
  | Eff_select t d a b =>
    match option_map (decide d) (eval_term env t) with
    | Some (Some (true, bound)) => denote a (env ++ bound) ps ctx
    | Some (Some (false, bound)) => denote b (env ++ bound) ps ctx
    | _ => Ret bad_shape
    end
  | Eff_provideContext t b =>
    match eval_term env t with Some c => denote b env ps c | None => Ret bad_shape end
  | Eff_withFiber (ActionTerm_context _) => Ret (Success ctx)
  | Eff_defs _ _ main _ => denote main env ps ctx
  (* an invocation: as a call, with its programs pushed at this environment *)
  | Eff_invoke k r args =>
    match eval_term env r, nth_error bodies (Z.to_nat k) with
    | Some v, Some body => trigger (Run body [v] ((effs_list args, env) :: ps) ctx)
    | _, _ => Ret bad_shape
    end
  | Eff_iterate _ initial test step result body =>
    match eval_term env initial with
    | Some c0 =>
      ITree.iter (loop_step (fun env' => denote body env' ps ctx) env test step result) c0
    | None => Ret bad_shape
    end
  | _ => Ret outside
  end.

End Denote.

(** The definitions of a program's root block ([defBodyPath]): none outside a block. *)
Definition bodies_of (main : eff native_op) : list (eff native_op) :=
  match main with Eff_defs _ bs _ _ => effs_list bs | _ => [] end.

(** **The meaning of a program**: its root at the empty environment, stack and context, each
    call answered by the definitions ([mrec]). The tree raises only cell rows and host rows. *)
Definition meaning (main : eff native_op) : itree (StoreE +' RowE) exitv :=
  mrec (fun T (r : RunE T) =>
    match r in RunE T return itree E0 T with
    | Run e env ps ctx => denote (bodies_of main) e env ps ctx
    end)
    (Run main [] [] Val_unit).
