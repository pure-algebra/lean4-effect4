import Controls
import Tools.Session.Snapshot

/-!
Finite editor probe. Placement: PLAN.md, analysis_snapshot_agrees and
incremental_analysis_agrees. No theorem about cached or incremental analysis is claimed.
The empty application and policy version are fixed here, not omitted from a generic cache.
-/
namespace DetProbe.LiveView
open Effect4 Effect4.Program Effect4.Program.Authoring
open DetProbe.Controls

inductive Status where
  | typing (why : TypeRefusal)
  | bodyNeeded
  | outside (why : Fault)
  | analyzed (summary : State)

def Status.code : Status → String
  | .typing _ => "typing-refusal"
  | .bodyNeeded => "body-summary-needed"
  | .outside _ => "outside-fragment"
  | .analyzed _ => "fragment-check-passed-unproved"

/-- Nonempty hole tables conservatively defer analysis, including unused declarations. -/
def classify (sketch : Sketch) : Status :=
  match sketch.check with
  | .error why => .typing why
  | .ok _ =>
    if !sketch.holes.isEmpty then .bodyNeeded
    else match inspect sketch.program with
      | .error (.typing why) => .typing why
      | .error (.fragment why) => .outside why
      | .ok summary => .analyzed summary

structure Stamp where
  generation : Nat
  revision : Nat
  bytes : Store.Bytes × Store.Bytes
  policy : Nat := 1
  deriving DecidableEq

structure Report where
  stamp : Stamp
  status : Status

def analyzeSnapshot (sketch : Sketch) (generation revision : Nat) : Report :=
  ⟨⟨generation, revision, sketch.encode, 1⟩, classify sketch⟩

/-- A late response is hidden unless all input identity fields still match. -/
def visible (current : Stamp) (report : Report) : Option Status :=
  if current = report.stamp then some report.status else none

def privateAlias : S :=
  bind "r" (Ref.make (nat 0)) (bind "s" (Ref.make (nat 0))
  (bind "a" (succeed (var "r"))
    (workers (setWorker "a" 1) (setWorker "s" 2) Forms.void)))

def before : EditSession := EditSession.open {} ⟨program privateAlias, []⟩
-- Both aliases have type Ref<Nat>. The continuation text is unchanged.
def edited : EditSession × Edit.Delta := before.feed (.fill [1, 1, 0] (.succeed (.var 1)))
def after : EditSession := edited.1

#guard match edited.2 with | .spliced _ => true | _ => false
#guard before.view.type = after.view.type
#guard before.view.refusals.isEmpty && after.view.refusals.isEmpty
#guard (classify before.sketch).code == "fragment-check-passed-unproved"
#guard (classify after.sketch).code == "outside-fragment"
#eval (edited.2, (classify before.sketch).code, (classify after.sketch).code)

/-- Ordinary type refusal survives unchanged, rather than becoming a fragment error. -/
def illTyped : NativeEff := .bind (.succeed (.lit .unit)) (.succeed (.var 99))
#guard match Api.explain illTyped, inspect illTyped with
  | some why, .error (.typing retained) => decide (why = retained)
  | _, _ => false
#guard (classify ⟨illTyped, []⟩).code == "typing-refusal"
#guard (classify ⟨program sharedWrites, []⟩).code == "outside-fragment"

/-- A typed omission becomes pending behavior analysis, not a type error. -/
def omitted : EditSession :=
  (before.feed (.omitAt [1, 1, 1] (Row.hole "work" .unit .never []))).1
#guard omitted.view.type.isSome && omitted.view.refusals.isEmpty
#guard !omitted.sketch.holes.isEmpty
#guard (classify omitted.sketch).code == "body-summary-needed"

/-- Exact snapshot identity includes holes; a filled hole keeps its declaration. -/
def report : Report := analyzeSnapshot before.sketch 3 8
#guard (visible report.stamp report).isSome
#guard (visible {report.stamp with revision := 9} report).isNone
#guard (visible {report.stamp with generation := 4} report).isNone
#guard (visible {report.stamp with policy := 2} report).isNone
#guard (visible {report.stamp with bytes := after.sketch.encode} report).isNone
#guard (visible {report.stamp with bytes := omitted.sketch.encode} report).isNone

def extraHole : Sketch := {before.sketch with holes := [Row.hole "unused" .unit .never []]}
#guard extraHole.encode.1 = before.sketch.encode.1
#guard extraHole.encode.2 != before.sketch.encode.2
#guard (visible {report.stamp with bytes := extraHole.encode} report).isNone
#guard (classify extraHole).code == "body-summary-needed"

-- The existing snapshot cache also resolves a changed input freshly.
#guard match Tools.Session.Snapshot.resolve after.sketch.encode
    (Tools.Session.Snapshot.prepare before.sketch.encode) with
  | some session => decide (session.sketch.encode = after.sketch.encode)
  | none => false

-- Two values have the same access metadata. Metadata is not syntax identity.
def noAccesses (p : NativeEff) : Bool := match inspect p with
  | .ok s => s.env.isEmpty && s.origins.isEmpty && s.accesses.isEmpty &&
      s.workers.isEmpty && s.joined.isEmpty && !s.worker
  | .error _ => false
#guard noAccesses (.succeed (.lit (.nat 1))) && noAccesses (.succeed (.lit (.nat 2)))
#guard (Sketch.encode ⟨.succeed (.lit (.nat 1)), []⟩).1 !=
  (Sketch.encode ⟨.succeed (.lit (.nat 2)), []⟩).1
#eval ["typing-refusal", "outside-fragment", "body-summary-needed", "fragment-check-passed-unproved"]

end DetProbe.LiveView
