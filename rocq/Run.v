(* The comparison lane's development (rocq/README.md), moved unchanged from the study of
   2026-10-16:
   git:98a29895b800556365a2edc9924f3ed12787b820:docs/research/2026-10-16-itrees/rocq/Run.v.
   The study's README and its other files stay there. *)

(** * Run: hosts for the meaning, a frontier as a node, and a fuelled observer

    The meaning ([Denote.meaning]) raises cell rows and host rows. Here the cells are a state
    ([h_store], Lean's [storeHandler] on the three cell rows), and a host row is answered by a
    reply tape ([h_tape]): each call takes the next exit, as Lean's [tapeHandler] does
    ([src/Effect4/Laws/Program/DenoteRows.lean]). The tape host records each call it answers.

    A call that the tape cannot answer is a frontier. It is the event [Waits], whose answer type
    is empty, so the tree stops at that node. A frontier is therefore a node of its own: not an
    exit ([Ret]) and not a divergence (an endless run of [Tau]). This is the distinction
    DB-03 asks for ([docs/DESIGN-BASIS.md]); a budget plays no part in it.

    [observe_n] reads a finished tree with fuel. It is a computing device for checks; no
    statement here is made at a fuel. *)

From Stdlib Require Import List ZArith String.
Import ListNotations.
From ITree Require Import ITree Basics.Basics Events.State.
Import ITreeNotations Basics.Basics.Monads.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import E4.Eff_types E4.Denote.

Local Open Scope Z_scope.
Local Open Scope list_scope.

(** A call waits on the host: its row and request. No answer exists. *)
Variant WaitE : Type -> Type :=
| Waits (i : int) (request : val_) : WaitE void.

(** The cells of the store, by their index. A cell is the handle [handle 2 k] ([Value.cell]). *)
Definition cells : Type := list val_.

Fixpoint set_nth (l : cells) (k : nat) (v : val_) : cells :=
  match l, k with
  | [], _ => []
  | _ :: rest, O => v :: rest
  | x :: rest, S k' => x :: set_nth rest k' v
  end.

Definition cell_index (v : val_) : option nat :=
  match v with Val_handle kind k => if Z.eqb kind 2 then Some (Z.to_nat k) else None | _ => None end.

(** The cell rows on the cells; a row at a value that is no cell answers [unit], as
    [storeHandler] answers a row it does not apply. *)
Definition h_store {F : Type -> Type} : StoreE ~> stateT cells (itree F) :=
  fun T e =>
    match e in StoreE T return stateT cells (itree F) T with
    | RefMake v => fun s => Ret (s ++ [v], Val_handle 2 (Z.of_nat (Stdlib.Lists.List.length s)))
    | RefGet c => fun s =>
      Ret (s, match cell_index c with
              | Some k => match nth_error s k with Some v => v | None => Val_unit end
              | None => Val_unit
              end)
    | RefSet c w => fun s =>
      Ret (match cell_index c with Some k => set_nth s k w | None => s end, Val_unit)
    end.

(** The cells answered, the host rows passed on. *)
Definition h_cells : (StoreE +' RowE) ~> stateT cells (itree RowE) :=
  fun T e s =>
    match e with
    | inl1 c => h_store _ c s
    | inr1 r => ITree.map (fun x => (s, x)) (trigger r)
    end.

(** One answered call: its row, its request, and the exit it was answered with. *)
Definition call : Type := (int * val_ * exitv)%type.

(** **The reply tape as a host**: the next exit answers, and the call is recorded. An empty
    tape leaves the call waiting: the frontier node [Waits]. *)
Definition h_tape : RowE ~> stateT (list exitv * list call) (itree WaitE) :=
  fun T e =>
    match e in RowE T return stateT (list exitv * list call) (itree WaitE) T with
    | Row i v => fun st =>
      match fst st with
      | a :: rest => Ret ((rest, snd st ++ [(i, v, a)]), a)
      | [] => ITree.bind (trigger (Waits i v)) (fun x : void => match x with end)
      end
    end.

(** **A program run under a reply tape**: the tape left and the calls answered, then the cells
    and the root's exit. *)
Definition run_tape (main : eff native_op) (tape : list exitv)
    : itree WaitE ((list exitv * list call) * (cells * exitv)) :=
  interp_state h_tape (interp_state h_cells (meaning main) []) (tape, []).

(** What a fuelled reading finds: an exit, a waiting call, or no answer within the fuel. *)
Inductive outcome (R : Type) : Type :=
| Done (r : R)
| Waiting (i : int) (request : val_)
| Unfinished.
Arguments Done {R}.
Arguments Waiting {R}.
Arguments Unfinished {R}.

Fixpoint observe_n {R : Type} (n : nat) (t : itree WaitE R) : outcome R :=
  match n with
  | O => Unfinished
  | S n' =>
    match observe t with
    | RetF r => Done r
    | TauF t' => observe_n n' t'
    | VisF e _ => match e with Waits i v => Waiting i v end
    end
  end.
