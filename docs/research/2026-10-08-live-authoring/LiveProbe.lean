import Effect4.Run.Tape
import Effect4.Modules.Queue.Defs
import Effect4.Api.Author
import Effect4.Program.Typing.Annotate
import Effect4.Program.Typing.Parts

/-!
# Probe LIVE-1: an edit that keeps its focus's type splices the address table (2026-10-08)

Research note `docs/research/2026-10-08-live-authoring.md`, section 4. This file is no battery:
no root reaches it. Run it with `scratch/lean-slot.sh lake env lean <this file>`. Each line is a
finite evaluation. Nothing here is a theorem.

* **Part A, the splice.** At every address of a program in three programs, the edit wraps the
  sub-program in `suspend`, which keeps its type. The probe compares two tables of the edited
  program: the table computed again from the root (`annotate`), and the splice. The splice is
  the old table outside the edited subtree, with the new sub-program's own table at the focus's
  environment in its place.
* **Part B, the reach of an edit that changes the type.** The edit `exit` changes the answer
  column. The probe counts the entries outside the subtree that change.
* **Part C, an edit session as a pure machine.** `Live.step` takes one edit. It splices when
  the focus's type is kept, and computes again from the root when it is not. A run of edits is a
  fold of `Live.step`. The probe checks the session's invariant after each run: its table is the
  table of its program.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Probe.Live

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring Effect4.Modules

/-! ## Three programs -/

def firstRow : RowDef := Row.host "L.first" (.list (.var 0)) (.option (.var 0))

/-- A queue, a host call, an offer: seat HOST's client, filling 1. -/
def clientA : Module NativeOp :=
  { rows := [firstRow], main := eff do
      let q ← Queue.bounded .nat 1
      let o ← Row.call firstRow (app "cons" [nat 1, nilT])
      let _ ← Queue.offer .nat q (nat 3)
      return o }

/-- A loop of offers, then a take. -/
def loopB : Module NativeOp :=
  { main := eff do
      let q ← Queue.bounded .nat 4
      let _ ← forRange (nat 0) (nat 3) fun i => Queue.offer .nat q i
      let x ← Queue.take .nat q
      return x }

/-- A handler, a finalizer and a choice. -/
def handlerC : Module NativeOp :=
  { main := catchCause "c"
      (onExit "e" (ifElse (bool true) (succeed (nat 1)) (fail (str "no"))) (succeed unit))
      (succeed (nat 0)) }

def builtOf (m : Module NativeOp) : Option Api.Built := (Api.Author.build m).toOption

def sigOf (b : Api.Built) : Signature NativeOp := SigApp.signature ⟨b.table, []⟩

/-! ## Part A: the splice -/

/-- The address `p` is inside the subtree at `a`. -/
def under (a p : List Nat) : Bool := a.isPrefixOf p

/-- **The splice**: the old table before the subtree at `a`, the new sub-program's own table at
the focus's environment with its addresses under `a`, and the old table after the subtree. The
table lists a node before its children, so a subtree is one contiguous segment. -/
def splice (old : List Table.Entry) (a : List Nat) (sub : List Table.Entry) : List Table.Entry :=
  let pre := old.takeWhile fun e => !under a e.path
  let post := (old.dropWhile fun e => !under a e.path).dropWhile fun e => under a e.path
  pre ++ sub.map (fun e => { e with path := a ++ e.path }) ++ post

/-- One edit at `a`: the edited program, and the edited sub-program's own table at the focus's
environment. `none` where `a` holds no typed program, or where the edit refuses. -/
def editAt (s : Signature NativeOp) (p : NativeEff) (a : List Nat) (edit : NativeEff → NativeEff) :
    Option (NativeEff × Focus NativeOp × NativeEff) :=
  (focusAt s [] p a).bind fun f =>
    match (Node.eff p).replaceAt a (.eff (edit f.program)) with
    | some (.eff p') => some (p', f, edit f.program)
    | _ => none

/-- Part A at every address of a program: how many addresses hold a typed program, how many
edits keep the type, and at how many of those the splice equals the table computed again. -/
def spliceReport (m : Module NativeOp) (edit : NativeEff → NativeEff) : Option (Nat × Nat × Nat) :=
  (builtOf m).map fun b =>
    let s := sigOf b
    let p := b.program
    let old := annotate s [] p
    let results := (Node.addresses (.eff p)).filterMap fun a =>
      (editAt s p a edit).map fun (p', f, q') =>
        let kept := decide (effTy s f.env q' = some f.ty)
        let agrees := decide (annotate s [] p' = splice old a (annotate s f.env q'))
        (kept, kept && agrees)
    (results.length, (results.filter (·.1)).length, (results.filter (·.2)).length)

#eval (spliceReport clientA .suspend, spliceReport loopB .suspend, spliceReport handlerC .suspend)

-- finite evaluation: `suspend` keeps the type at every typed address, and at each the splice is
-- the table computed again from the root
#guard (spliceReport clientA .suspend).map (fun r => decide (r.1 = r.2.1 ∧ r.2.1 = r.2.2)) =
  some true
#guard (spliceReport loopB .suspend).map (fun r => decide (r.1 = r.2.1 ∧ r.2.1 = r.2.2)) =
  some true
#guard (spliceReport handlerC .suspend).map (fun r => decide (r.1 = r.2.1 ∧ r.2.1 = r.2.2)) =
  some true

/-! ## Part B: the reach of an edit that changes the type -/

/-- Part B at every address: the size of the edited subtree, and the count of the entries
outside it whose environment or answer changed, for the edits that change the type. -/
def reachReport (m : Module NativeOp) (edit : NativeEff → NativeEff) :
    Option (List (List Nat × Nat × Nat)) :=
  (builtOf m).map fun b =>
    let s := sigOf b
    let p := b.program
    let old := annotate s [] p
    (Node.addresses (.eff p)).filterMap fun a =>
      (editAt s p a edit).bind fun (p', f, q') =>
        if effTy s f.env q' = some f.ty then none
        else
          let new := annotate s [] p'
          let outsideOld := old.filter fun e => !under a e.path
          let outsideNew := new.filter fun e => !under a e.path
          let changed := (outsideOld.zip outsideNew).filter fun (x, y) => x != y
          some (a, (new.filter fun e => under a e.path).length, changed.length)

#eval (reachReport handlerC .exit).map (·.take 12)

-- finite evaluation: an edit that changes the type reaches entries outside its subtree: the
-- nodes above it, and the siblings that read its type
#guard (reachReport handlerC .exit).map (fun r => r.any fun x => x.2.2 > 0) = some true

/-! ## Part C: an edit session as a pure machine -/

/-- **The state of an edit session**: the signature, the program, and its address table. -/
structure Live where
  sig : Signature NativeOp
  program : NativeEff
  table : List Table.Entry

/-- **One edit**: the replacement of the sub-program at `a` by `edit` of it. It splices the table
where the focus's type is kept, and computes it again from the root where it is not. The second
answer is the addresses to show again. `none` where the edit does not apply. -/
def Live.step (l : Live) (a : List Nat) (edit : NativeEff → NativeEff) :
    Option (Live × List (List Nat)) :=
  (editAt l.sig l.program a edit).map fun (p', f, q') =>
    if effTy l.sig f.env q' = some f.ty then
      let sub := annotate l.sig f.env q'
      (⟨l.sig, p', splice l.table a sub⟩, sub.map fun e => a ++ e.path)
    else
      let new := annotate l.sig [] p'
      (⟨l.sig, p', new⟩, (new.filter fun e => !(l.table.contains e)).map (·.path))

/-- A run of edits: the fold of `Live.step`, skipping an edit that does not apply. -/
def Live.run (l : Live) (edits : List (List Nat × (NativeEff → NativeEff))) : Live :=
  edits.foldl (fun l (a, edit) => ((l.step a edit).map (·.1)).getD l) l

def Live.ofBuilt (b : Api.Built) : Live := ⟨sigOf b, b.program, annotate (sigOf b) [] b.program⟩

/-- The session's invariant: its table is the table of its program. -/
def Live.coherent (l : Live) : Bool := decide (l.table = annotate l.sig [] l.program)

/-- A run of edits at the first `k` addresses of the program, each `suspend`, then one `exit`
at the root's first child, then `suspend` again at the same addresses. -/
def script (b : Api.Built) (k : Nat) : List (List Nat × (NativeEff → NativeEff)) :=
  let as := (Node.addresses (.eff b.program)).take k
  as.map (·, .suspend) ++ [([0], .exit)] ++ as.map (·, .suspend)

#eval (builtOf handlerC).map fun b => (Live.ofBuilt b |>.run (script b 8)).coherent
#eval (builtOf loopB).map fun b => (Live.ofBuilt b |>.run (script b 8)).coherent

-- finite evaluation: after a run of edits that keep and change types, the session's table is
-- the table of its program
#guard (builtOf handlerC).map (fun b => (Live.ofBuilt b |>.run (script b 8)).coherent) = some true
#guard (builtOf loopB).map (fun b => (Live.ofBuilt b |>.run (script b 8)).coherent) = some true

-- the addresses to show again after one edit that keeps the type: the new subtree only
#eval (builtOf loopB).bind fun b =>
  ((Live.ofBuilt b).step [0] .suspend).map fun (l', shown) =>
    (shown.length, l'.table.length, (Node.addresses (.eff b.program)).length)

end Probe.Live
