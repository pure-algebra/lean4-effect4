import Effect4.Program.Check
import Effect4.Program.Edit

/-!
# Program.Typing.SourceSession — the edit engine over a sketch as written

**The question.** An agent edits a program as written: its layer references stay, so two uses of
one layer keep one memo key at run time. The session keeps the sketch as written and its source
table (`Sketch.sourceTable`, `Program/Typing/Source.lean`). One feed with a policy decides a draft,
a kept commit item, a fill's certification and a recheck. Every check it makes goes through a
certified oracle (`Check.Oracle`, `Program/Check.lean`), so a memo changes cost, never an answer.

## The face

| Operation | It takes | It answers |
| --- | --- | --- |
| `SourceSession.open` | an oracle, an application and a sketch | the session, from the module check's table |
| `SourceSession.feed` | an oracle, a policy, a session and an edit | the next session and the journal's step, or a located refusal |
| `SourceSession.partKey` | a session, an address and a filling | the part check that decides the filling in its expansion |
| `SourceSession.view` | a session | the source table, its refusals and the root type |
| `SourceSession.focusAt` | a session and an address | the sub-program as written, with the table's environment and type there |

## What `feed` does

The edit applies to the sketch as written (`Sketch.edit`). An address that holds no program
refuses `noProgram`, except under `draft`, which records an unchanged step.

- **At the root**, every policy asks the module key and never splices.
- **`recheck`** asks the module key and refuses a candidate that does not check.
- **`draft`** splices where the expanded edit agrees, the focus is typed and the part check keeps
  the focus's type. Both sketches must have no ill-formed reference. Any other draft asks the
  module key. A draft never refuses.
- **`keepExact`** asks the filling's part key inside the candidate's expansion. A changed or
  refused part type refuses `notKept`. A kept part splices where the expanded edit agrees.
  Both sketches must have no ill-formed reference. Otherwise it rechecks and compares root and local types.

The session's invariant is `SourceSession.Coherent`: its table is the sketch's source table.
The laws live in `Laws/Program/SourceTable.lean`. `EditSession.feed` (`Program/Edit.lean`) stays as
the reference of the draft policy's law, `SourceSession.feed_draft`.

## What this module is not

- It runs nothing. A run of a program with references redirects each reference to its target.
- It counts no cost. The cost is read off the definitions, and no theorem counts it.
-/

set_option autoImplicit false
set_option maxRecDepth 20000
namespace Effect4.Program
open Check Check.Internal

/-- **The sketch after an edit**: a filling (`Sketch.fillAt`) or an omission (`Sketch.omitAt`).
`none` where the address holds no program. -/
def Sketch.edit (s : Sketch) (app : SigApp) : Edit → Option Sketch
  | .fill a q => s.fillAt a q
  | .omitAt a row => s.omitAt app a row

/-- **The edit of an expansion at the same address**: a filling by the new expansion's
sub-program there, and an omission as it is. `none` where the new expansion holds no program at
the address. -/
def Edit.expanded (x : Sketch) : Edit → Option Edit
  | .fill a _ =>
    match (Node.eff x.program).at_ a with
    | some (.eff q) => some (.fill a q)
    | _ => none
  | .omitAt a row => some (.omitAt a row)

/-- **What a delta shows, at the source's addresses**: the addresses of a copy are dropped. -/
def Edit.Delta.atSource (sites : List (List Nat)) : Edit.Delta → Edit.Delta
  | .spliced shown => .spliced (shown.filter fun a => !Table.belowSite sites a)
  | d => d

/-- **A source session**: an application, a sketch as written over it, and the table the session
keeps. Its invariant is `SourceSession.Coherent`. -/
structure SourceSession where
  /-- the application the sketch is checked against -/
  app : SigApp
  /-- the sketch as written: its program keeps its layer references -/
  sketch : Sketch
  /-- the source table: the expansion's table at the source's addresses -/
  table : List Table.Entry

namespace SourceSession

/-- **The session's invariant**: its table is its sketch's source table. -/
def Coherent (s : SourceSession) : Prop := s.table = s.sketch.sourceTable s.app

/-- **What the session shows, as an edit session**: a view of an edit session draws it. -/
def shown (s : SourceSession) : EditSession := ⟨s.app, s.sketch, s.table⟩

/-- **View** a session: its table, the table's distinct refusals, and the root type
(`SourceSession.reached_view`). -/
def view (s : SourceSession) : EditSession.View := s.shown.view

/-- **The focus at a source address**: the sub-program as written, with the environment and the
type that the table holds there. -/
def focusAt (s : SourceSession) (path : List Nat) : Option (Focus NativeOp) :=
  match (Node.eff s.sketch.program).at_ path, Table.typedAt s.table path with
  | some (.eff q), some (env, ty) => some ⟨q, env, ty⟩
  | _, _ => none

/-- **Open** a session on a sketch: the module check's table, asked through the oracle. -/
def «open» (o : Oracle) (app : SigApp) (sketch : Sketch) : Checked SourceSession := do
  let v ← Checked.ask o (.module app sketch.holes sketch.program)
  pure ⟨app, sketch, v.table⟩

/-- **The part check of a candidate below the root**: the candidate expansion's sub-program at the
address, at that address's signature, in the old focus's environment. `none` at the root, at an
untyped focus, or where the expansion holds no program. -/
def candidatePartKey (s : SourceSession) (path : List Nat) (candidate : Sketch) : Option CheckInput :=
  match path, s.focusAt path, (Node.eff candidate.expand.program).at_ path with
  | _ :: _, some old, some (.eff q) =>
      some (.part (sketchSigData candidate.expand s.app path) old.env q)
  | _, _, _ => none

/-- **The part key of a filling**: the one owner of part keys, for the fill set and the memo. -/
def partKey (s : SourceSession) (path : List Nat) (q : NativeEff) : Option CheckInput :=
  (s.sketch.fillAt path q).bind (s.candidatePartKey path)

/-- **Whether the expansion moved only at the edited address**: the old expansion's own edit there
gives the candidate's expansion. Otherwise an edit inside a referenced layer moved every copy, or
an edit changed a reference, and a splice would be wrong. -/
def expandedEditAgrees (s : SourceSession) (candidate : Sketch) (edit : Edit) : Bool :=
  let expanded := candidate.expand
  match Edit.expanded expanded edit with
  | some expandedEdit =>
      decide ((s.sketch.expand.edit s.app expandedEdit).map (fun y => (y.program, y.holes)) =
        some (expanded.program, expanded.holes))
  | none => false

/-- A splice needs expansion agreement and no whole-document reference refusal on either side. -/
def canSplice (s : SourceSession) (candidate : Sketch) (edit : Edit) : Bool :=
  s.expandedEditAgrees candidate edit && s.sketch.program.firstRefFault.isNone &&
    candidate.program.firstRefFault.isNone

end SourceSession

/-- **How a feed decides an edit.** -/
inductive FeedPolicy where
  /-- apply the edit; splice where the part keeps its type, else recheck; never refuse -/
  | draft
  /-- accept only a filling whose part type and the root and local types stay -/
  | keepExact
  /-- apply the edit, recheck, and refuse a candidate that does not check -/
  | recheck
deriving DecidableEq

/-- **Why a feed refuses**, in the order the feed tests. -/
inductive FeedRefusal where
  /-- the address holds no program -/
  | noProgram (path : List Nat)
  /-- the table holds no typed focus at the address -/
  | noFocus (path : List Nat)
  /-- `keepExact`: the part's verdict differs from the focus's type -/
  | notKept (focus : TyEnv × EffTy) (verdict : Except TypeRefusal EffTy)
  /-- the candidate does not check: its refusals -/
  | refused (why : List TypeRefusal)
  /-- `keepExact`: the root type would change -/
  | typeChanged (old : Option EffTy) (new : EffTy)
  /-- `keepExact`: the focus's environment or type would change -/
  | localChanged (old new : Option (TyEnv × EffTy))
deriving DecidableEq

namespace SourceSession

/-- **Finish a feed** after its module check: a draft accepts; any other policy refuses a candidate
that does not check; `keepExact` also compares the root and local types. -/
def finish (policy : FeedPolicy) (s next : SourceSession) (edit : Edit)
    (step : Edit.Step) (v : Verdict) : Except FeedRefusal (SourceSession × Edit.Step) :=
  match policy, v.result with
  | .draft, _ => .ok (next, step)
  | _, .error _ => .error (.refused next.view.refusals)
  | .recheck, .ok _ => .ok (next, step)
  | .keepExact, .ok ty =>
      if s.view.type != some ty then .error (.typeChanged s.view.type ty)
      else if edit.path != [] && Table.typedAt s.table edit.path != Table.typedAt next.table edit.path
      then .error (.localChanged (Table.typedAt s.table edit.path) (Table.typedAt next.table edit.path))
      else .ok (next, step)

/-- **Recheck** a candidate: ask its module key, then finish under the policy. -/
def recheck (o : Oracle) (policy : FeedPolicy) (s : SourceSession) (candidate : Sketch)
    (edit : Edit) (old : NativeEff) : Checked (Except FeedRefusal (SourceSession × Edit.Step)) := do
  let v ← Checked.ask o (.module s.app candidate.holes candidate.program)
  let next : SourceSession := ⟨s.app, candidate, v.table⟩
  pure (finish policy s next edit ⟨edit, some old, .rechecked⟩ v)

/-- **Splice** a part's table, placed at the edited address and shown at the source's addresses,
in place of the edited subtree's entries. -/
def splice (s : SourceSession) (candidate : Sketch) (edit : Edit) (old : NativeEff)
    (part : Verdict) : SourceSession × Edit.Step :=
  let sub := Table.atSource candidate.sites candidate.program.firstRefFault (place edit.path part).table
  let next : SourceSession := ⟨s.app, candidate, Table.splice s.table edit.path sub⟩
  (next, ⟨edit, some old, .spliced (sub.map (·.path))⟩)

/-- **Whether a draft may splice the edit at a focus of this type.** A filling may. An omission may
where its hole row declares exactly the focus's type, with closed, normal and formed columns. This
is the condition of `EditSession.feed`'s omission arm, the reference of `SourceSession.feed_draft`. -/
def draftOmitAllows (edit : Edit) (ty : EffTy) : Bool :=
  match edit with
  | .fill .. => true
  | .omitAt _ row =>
      decide (row = Row.hole row.name ty.answer ty.error ty.requires.elems) &&
        ty.answer.closed && ty.error.closed && decide (ty.answer.normalize = ty.answer) &&
        decide (ty.error.normalize = ty.error) &&
        (Formation.check (Formation.instantiatedSites row.normalizeTypes [])).isNone

/-- **Feed** one edit under a policy: the next session and the journal's step, or a refusal. Every
check is asked through the oracle, so the trace records it. -/
def feed (o : Oracle) (policy : FeedPolicy) (s : SourceSession) (edit : Edit) :
    Checked (Except FeedRefusal (SourceSession × Edit.Step)) := do
  match (Node.eff s.sketch.program).at_ edit.path, s.sketch.edit s.app edit with
  | some (.eff old), some candidate =>
      match edit.path with
      | [] => s.recheck o policy candidate edit old
      | _ :: _ =>
          match policy with
          | .recheck => s.recheck o policy candidate edit old
          | .draft =>
              match s.focusAt edit.path, s.view.type with
              | some focus, some _ =>
                  if !s.canSplice candidate edit || !draftOmitAllows edit focus.ty then
                    s.recheck o policy candidate edit old
                  else
                    match s.candidatePartKey edit.path candidate with
                    | none => s.recheck o policy candidate edit old
                    | some key =>
                        let part ← Checked.ask o key
                        match part.result with
                        | .ok ty =>
                            if ty = focus.ty then pure (.ok (s.splice candidate edit old part))
                            else s.recheck o policy candidate edit old
                        | .error _ => s.recheck o policy candidate edit old
              | _, _ => s.recheck o policy candidate edit old
          | .keepExact =>
              match s.focusAt edit.path with
              | none => pure (.error (.noFocus edit.path))
              | some focus =>
                  match s.candidatePartKey edit.path candidate with
                  | none => pure (.error (.noFocus edit.path))
                  | some key =>
                      let part ← Checked.ask o key
                      match part.result with
                      | .error _ => pure (.error (.notKept (focus.env, focus.ty) part.result))
                      | .ok ty =>
                          if ty != focus.ty then pure (.error (.notKept (focus.env, focus.ty) part.result))
                          else if s.canSplice candidate edit then
                            pure (.ok (s.splice candidate edit old part))
                          else s.recheck o policy candidate edit old
  | _, _ =>
      match policy with
      | .draft => pure (.ok (s, ⟨edit, none, .unchanged⟩))
      | _ => pure (.error (.noProgram edit.path))

end SourceSession

end Effect4.Program
