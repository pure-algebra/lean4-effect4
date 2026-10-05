import Effect4.Api.Author
import Effect4.Codegen.Forms

/-!
# Test.Dogfood.Stage — how far an rc.112 program gets

Decisions row 206 (ruled 2026-10-04) makes the five model-probe programs tracked acceptance tests.
Their rc.112 sources and recorded runs are reference texts under `Test/Dogfood/rc112/`, and
`Test/Dogfood/README.md` holds one plan row per program. Each battery of this folder encodes one
program as far as the language expresses it today. It pins how far the encoding gets, and it pins
every refused part with the build's own refusal.

This module holds the words the five batteries share:

* `verdict`: where a build stops, as the kind of the build's located refusal. It is the model
  probe's `verdict` (`git:ce2ece4f:docs/research/2026-09-30-model-probe/programs/ProbeRefusals.lean`),
  unchanged: the refusal sum `Api.BuildRefusal` has the same four constructors today.
* `typingReason?`: the checker's whole reason, for a pin that names the expected type.
* `Answer` and `Reach`: the stage one battery measures, one value per program.
* `formAdmits`: whether the form table admits an rc.112 head (DI-39, DI-89; requirement R10).
* `PartReach`, `recordOf` and `partReach`: how far one error payload part gets (decisions row
  120): built, run to its record, printed as a module with its payload class (part E2) or
  refused by name, and read back.

A slice of row 204 moves a program when one of its pins turns red: a refused part builds, or a
run reaches rc.112's answer. The slice then edits the battery to the next spelling, and the
README's row moves with it.
-/

set_option autoImplicit false

namespace Test.Dogfood

open Effect4 Effect4.Program Effect4.Program.Authoring

/-- Where a build stops, as a short word: `"built"`, or the kind of the build's located refusal.
A typing refusal names its reason's head word (`TypeReason.head`). -/
def verdict (m : Module NativeOp) : String :=
  match Effect4.Api.Author.build m with
  | .ok _ => "built"
  | .error (.scope _) => "scope"
  | .error (.typing r) => "typing: " ++ r.reason.head
  | .error (.admission _) => "admission"
  | .error (.serviceCarrier _ _ none) => "serviceCarrier: signature none"
  | .error (.serviceCarrier _ _ (some _)) => "serviceCarrier: signature disagrees"

/-- A module whose only field is its main program. -/
def program (src : Src NativeOp) : Module NativeOp := { main := src }

/-- The checker's reason when the build refuses at a type, and `none` otherwise. -/
def typingReason? (m : Module NativeOp) : Option TypeReason :=
  match Effect4.Api.Author.build m with
  | .error (.typing r) => some r.reason
  | _ => none

/-- How a run's root exit compares with the answer rc.112 gave on the recorded run
(`Test/Dogfood/rc112/hostruns.log`). -/
inductive Answer
  /-- The root exit is rc.112's answer, in the value spelling the battery names. -/
  | rc112
  /-- The root exits with another answer. -/
  | differs
  /-- The root has no exit when the run stops. -/
  | unfinished
  /-- The build admits no part of the program, so nothing runs. -/
  | notRun
deriving DecidableEq, Repr

/-- A run's root exit against rc.112's answer, both in the battery's value spelling. -/
def answerOf (exit : Option Effect4.Machine.ExitV) (rc112 : Effect4.Machine.ExitV) : Answer :=
  match exit with
  | none => .unfinished
  | some e => if e = rc112 then .rc112 else .differs

/-- How far one program gets today: the stage its README row quotes.

* `refused`: each part of the rc.112 program that the language refuses, with its `verdict`;
* `admitted`: `Api.Author.build` elaborates, types and admits the battery's program;
* `answer`: its run against rc.112's recorded answer;
* `printed`: `Api.print` answers TypeScript syntax for it;
* `readBack`: `Api.readable` holds, so reading its printing gives the program back. -/
structure Reach where
  refused : List (String × String)
  admitted : Bool
  answer : Answer
  printed : Bool
  readBack : Bool
deriving DecidableEq, Repr

/-- The printing stages of a built program, against its own row table. -/
def printedOf (b : Effect4.Api.Built) : Bool × Bool :=
  ((Effect4.Api.print b.program b.table).isOk, Effect4.Api.readable b.program b.table)

/-- Whether the form table (`Effect4.Codegen.Forms.all`) admits a head. DI-39 rules form rows for
`catchTag` and five more heads; DI-89 names `retry`, `catchTag`, `forEach` and `all`. -/
def formAdmits (head : String) : Bool := Effect4.Codegen.Forms.all.any (·.head == head)

/-! ## Error payload parts (decisions row 120)

Since the error payload carrier landed (part E1), a typed failure may carry a record. A battery
measures each payload part of its program apart from the program's own stage: the build's
verdict, whether the run fails with the part's record as its first typed failure, what the module
printer answers, and whether the printed module reads back. Since part E2 the module declares one
`Data.TaggedError` class per tagged payload type and constructs the payload with `new`
(`Codegen/Classes.lean`); a class it cannot declare is refused by name, with the tag. -/

/-- How far one payload part gets. -/
structure PartReach where
  /-- The build's verdict (`verdict`). -/
  verdict : String
  /-- The run's root exit fails with the part's record as its first typed failure. -/
  failsWith : Bool
  /-- The module printer's answer (`Api.emitModule`): `"printed"`, or its refusal by name. -/
  printed : String
  /-- Reading the printed module (`Api.readModule`) gives the program back. -/
  readBack : Bool
deriving DecidableEq, Repr

/-- A record value, its fields in canonical order. -/
def recordOf (names : List String) (values : List Effect4.Machine.Val) : Effect4.Machine.Val :=
  (Effect4.Machine.Record.build names values).getD .unit

/-- A class refusal's reason, as a word. -/
def classReason : ClassRefusal → String
  | .notIdentifier => "notIdentifier"
  | .collides => "collides"
  | .fieldsDiffer => "fieldsDiffer"
  | .construction => "construction"
  | .unreadable => "unreadable"

/-- The module printer's answer on a built program, by name: a payload class it cannot declare is
named with its tag and the reason (`ClassRefusal`). -/
def printVerdict (b : Effect4.Api.Built) : String :=
  match Effect4.Api.emitModule "main" b.program b.table with
  | .ok _ => "printed"
  | .error (.print (.payloadClass tag why)) => "refused: payloadClass " ++ tag ++ " " ++ classReason why
  | .error (.print (.internalAction name)) => "refused: " ++ name
  | .error (.print (.typeSpelling name)) => "refused: typeSpelling " ++ name
  | .error _ => "refused"

/-- Whether the printed module reads back to the built program. -/
def readBackVerdict (b : Effect4.Api.Built) : Bool :=
  match Effect4.Api.printModule "main" b.program b.table with
  | some m => decide (Effect4.Api.readModule m b.table = .ok b.program)
  | none => false

/-- How far a payload part gets: its build, its run against the record it must fail with, its
printing as a module and its reading back. -/
def partReach (m : Module NativeOp) (record : Effect4.Machine.Val) : PartReach :=
  match Effect4.Api.Author.build m with
  | .ok b =>
    { verdict := "built"
      failsWith := match b.runSync with
        | .failure c => firstErrorValue? c == some record
        | .success _ => false
      printed := printVerdict b
      readBack := readBackVerdict b }
  | .error _ => { verdict := verdict m, failsWith := false, printed := "not built", readBack := false }

/-! ## Controls of the shared words -/

-- `verdict`: a green control and one red control per kind the batteries pin.
#guard verdict (program (succeed (nat 1))) = "built"
#guard verdict (program (Ref.get (str "x"))) = "typing: requestNotSubtype"
#guard verdict (program (fail (app "pair" [str "T", nat 1]))) = "typing: errorNotAdmitted"
#guard verdict (program (succeed (var "unbound"))) = "scope"
#guard verdict
    { services := [{ key := ⟨⟨12⟩, ⟨12⟩⟩, carrier := .string }]
      main := succeed unit } = "serviceCarrier: signature none"
-- `typingReason?`: the reason of a refused build, and nothing for a built one.
#guard typingReason? (program (Ref.get (str "x"))) =
  some (.requestNotSubtype "refGet" .string (.refOf (.var 0)))
#guard typingReason? (program (succeed (nat 1))) = none
-- `answerOf`: the three readings of a root exit.
#guard answerOf (some (.success (.nat 1))) (.success (.nat 1)) = .rc112
#guard answerOf (some (.success (.nat 0))) (.success (.nat 1)) = .differs
#guard answerOf none (.success (.nat 1)) = .unfinished
-- `formAdmits`: a head the table holds, and one it does not.
#guard formAdmits "Effect.andThen"
#guard !formAdmits "Effect.catchTag"
-- `partReach`: a payload part that builds, runs to its record, prints as a module with its class
-- and reads back; a part whose class the module cannot declare, refused by name with its tag; a
-- red control whose expected record differs; and a part the checker refuses.
#guard partReach (program (fail (record [("_tag", false, .lit "E"), ("n", false, .nat)]
    [("_tag", str "E"), ("n", nat 1)]))) (recordOf ["_tag", "n"] [.str "E", .nat 1]) =
  ⟨"built", true, "printed", true⟩
#guard partReach (program (fail (record [("_tag", false, .lit "Effect"), ("n", false, .nat)]
    [("_tag", str "Effect"), ("n", nat 1)]))) (recordOf ["_tag", "n"] [.str "Effect", .nat 1]) =
  ⟨"built", true, "refused: payloadClass Effect collides", false⟩
#guard (partReach (program (fail (record [("_tag", false, .lit "E"), ("n", false, .nat)]
    [("_tag", str "E"), ("n", nat 1)]))) (recordOf ["_tag", "n"] [.str "E", .nat 2])).failsWith =
  false
#guard (partReach (program (fail (bool true))) .unit).verdict = "typing: errorNotAdmitted"

end Test.Dogfood
