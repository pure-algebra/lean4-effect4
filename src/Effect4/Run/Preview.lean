import Effect4.Run.Kit

/-!
# Run.Preview — the preview profile, its admitted reply tape, and rejected tape diagnostics

Slice P of `docs/research/2026-10-17-proof-scout/README.md` (§7.6).

* `Preview.admit`: admits a program and its application to the preview profile (version 1):
  1. `admitProgram` accepts them, so the application and program are checked and every reached row
     has its columns;
  2. `Tree.outsideAt` finds no unsupported form;
  3. every external row the program reaches has closed columns (`rowIsGeneric = false`) and no host
     handle in its answer (`hasHandle = false`).
* `Preview.checkedTape`: the reply tape of the call tree that admits each reply at its row
  (`Kit.replyFault`) before passing it. A refused reply is not consumed and leaves the call waiting.
* `Preview.rejected`: reads a stopped run under a reply tape; a call that waits with a tape entry
  left gets that entry and its `Kit.ReplyFault`, distinguishing a rejected reply from an exhausted
  tape.

The laws are in `Effect4.Laws.Api.Preview`.
-/

set_option autoImplicit false

deriving instance DecidableEq, Repr for Effect4.Run.Kit.ReplyFault

namespace Effect4.Run.Preview

open Effect4 Effect4.Machine Effect4.Program Effect4.Store

/-! ## The preview profile (version 1) -/

/-- Why a program and its application are outside the preview profile (version 1). -/
inductive Refusal where
  /-- Program admission refused the program or the application (`admitProgram`). -/
  | admission (why : AdmitRefusal)
  /-- The program contains a form outside the call tree's arms at `path` (`Tree.outsideAt`). -/
  | outsideTree (path : List Nat)
  /-- The program reaches a host row at `path` whose normalized columns contain a type variable. -/
  | genericRow (path : List Nat) (row : Nat)
  /-- The program reaches a host row at `path` whose normalized answer mentions a host handle. -/
  | handleAnswer (path : List Nat) (row : Nat)
deriving DecidableEq, Repr

/-- Whether a row's normalized columns have any type variable. -/
def rowIsGeneric (r : Program.Row) : Bool :=
  !(r.request.varsOf ++ r.answer.varsOf ++ r.error.varsOf).isEmpty

/-- Whether a type mentions a host handle (`Ty.spelledNames`). -/
def hasHandle (t : Ty) : Bool :=
  t.spelledNames.any Prod.fst

/-- Check one node of a program for a host row outside the preview profile. -/
def rowFaultAt (app : SigApp) (node : NativeEff) (path : List Nat) : Option Refusal :=
  match node with
  | .perform (.external i) _ =>
    match (app.rows[i]?).map Program.Row.normalizeTypes with
    | none => none
    | some r =>
      if rowIsGeneric r then some (.genericRow path i)
      else if hasHandle r.answer then some (.handleAnswer path i)
      else none
  | _ => none

/-- The first node of the program whose host row is outside the preview profile, by its address in
program order (`foldMapAt_eff`). -/
def outsideProfileAt (app : SigApp) (program : NativeEff) : Option Refusal :=
  foldMapAt_eff none (fun a b => a <|> b) [] program (rowFaultAt app)

/-- **Admit a program and its application to the preview profile (version 1).**
1. Program admission (`admitProgram`) accepts them, so the application and program are checked and
   every reached row has its columns.
2. `Tree.outsideAt` finds no form outside the call tree's arms.
3. Every external row the program reaches has closed columns (no type variable in its request,
   answer or error) and no handle in its answer (`outsideProfileAt`). -/
def admit (app : SigApp) (program : NativeEff) : Except Refusal (AdmittedProgram program app) :=
  match admitProgram program app with
  | .error why => .error (.admission why)
  | .ok admitted =>
    match Tree.outsideAt program with
    | some path => .error (.outsideTree path)
    | none =>
      match outsideProfileAt app program with
      | some why => .error why
      | none => .ok admitted

/-! ## The checked reply tape and rejected entry diagnostics -/

/-- **A reply tape whose replies are admitted at their row first** (`Kit.replyFault`). A reply
that the row refuses is not given, and the call waits: a frontier, never a guessed value. -/
def checkedTape (app : SigApp) : Tree.Host (List ExitV) := fun row _ tape =>
  match tape with
  | [] => none
  | ex :: rest => if (Kit.replyFault app row ex).isNone then some (ex, rest) else none

/-- A rejected tape entry at a waiting call: the row index, the tape entry that was refused, and
its `Kit.ReplyFault`. -/
structure Rejected where
  row : Nat
  exit : ExitV
  fault : Kit.ReplyFault
deriving DecidableEq

/-- **Read a stopped run for a rejected tape entry.** A call that waits with a tape entry left
gets that entry and its `Kit.ReplyFault`. When the tape is empty, or the run did not stop waiting
on a call, or the entry fits the row, `none`. -/
def rejected (app : SigApp) (o : Tree.Outcome (List ExitV)) : Option Rejected :=
  match o.stop, o.state with
  | .waiting row _, ex :: _ =>
    (Kit.replyFault app row ex).map fun fault => ⟨row, ex, fault⟩
  | _, _ => none

end Effect4.Run.Preview
