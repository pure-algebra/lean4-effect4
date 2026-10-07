import Effect4.Laws.Program.DenoteRows
import Effect4.Laws.Program.DenoteRowsAppend
import Effect4.Laws.Program.DenoteRowsR
import Test.Dogfood.Scenario.Todo
import Test.Dogfood.Scenario.Routing

/-!
# The call tree over the host rows: the battery of slices H1, H2 and H3

Each line is a finite evaluation, a reader or a control.
-/

namespace Test.Program.DenoteRowsContract

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring Effect4.Program.Denote
open Effect4.Program.Sched
open Test.Dogfood.Scenario.Todo
open Test.Dogfood.P2HandlerLayers (built?)

/-- One host row: a number in, a number out, a tagged failure. -/
def wait : Row := (Row.host "H.wait" .nat .nat (.prod .string .string) "battery").row
/-- One host row that answers an external handle. -/
def kvMake : Row := (Row.host "K.make" .unit NativeOp.kvTy (.prod .string .string) "battery").row
def call (i : Nat) (n : Term) : NativeEff := .perform (.external i) n
def num (n : Nat) : Term := .lit (.nat n)
/-- Three calls in sequence: each request is the reply before it. -/
def chain : NativeEff := .bind (call 0 (num 1)) (.bind (call 0 (.var 0)) (call 0 (.var 1)))
/-- A cell made and read: a program with no host call. -/
def cell : NativeEff := .bind (.perform .refMake (num 7)) (.perform .refGet (.var 0))
/-- Whether a request is this text. The request's type is a column's carrier, so the comparison
names `Val`. -/
def isStr (v : Val) (text : String) : Bool := decide (v = .str text)

/-! ## Slice H1: the tree of a real program -/

-- finite evaluation: the tree of `add` at an empty title is a leaf, so it holds no call
#guard (built? (request (add (str "")))).map (fun b =>
    match denoteRows b.table b.program [] with
    | .pure ex => decide (ex = .failure (Cause.fail (.tagged "EmptyTitle" "a title is required")))
    | .vis _ _ => false) = some true
-- finite evaluation: the tree of `add` at a title is one call of row 0 with the title
#guard (built? (request (add (str "milk")))).map (fun b =>
    match denoteRows b.table b.program [] with
    | .vis (.inr ⟨i, sent⟩) _ => decide (i.val = 0) && isStr sent "milk"
    | _ => false) = some true
-- finite evaluation: a failure of the repository is the exit of `complete`, whatever it is
#guard (built? (request (complete (nat 1)))).map (fun b =>
    match denoteRows b.table b.program [] with
    | .vis (.inr ⟨i, _⟩) k =>
      decide (i.val = 2) &&
        (match k (.failure (Cause.fail (.tagged "SqlError" "locked"))) with
         | .pure ex => decide (ex = .failure (Cause.fail (.tagged "SqlError" "locked")))
         | .vis _ _ => false)
    | _ => false) = some true

-- finite evaluation (the routing scenario, in the fragment by row 310): the first node is the call of
-- the configuration. At an answer with another token the tree is a leaf with the handler's
-- response: it holds no call of the repository
#guard (built? (Test.Dogfood.Scenario.Routing.request "secret" 2 "2")).map (fun b =>
    match denoteRows b.table b.program [] with
    | .vis (.inr ⟨i, _⟩) k =>
      decide (i.val = 0) &&
        (match k (.success (Test.Dogfood.Scenario.Routing.configOf "other" 20)) with
         | .pure (.success _) => true
         | _ => false)
    | _ => false) = some true
-- finite evaluation: with the request's token the next node is the call of the repository, and
-- its failure with an infrastructure tag is the tree's exit: no handler takes it
#guard (built? (Test.Dogfood.Scenario.Routing.request "secret" 2 "2")).map (fun b =>
    match denoteRows b.table b.program [] with
    | .vis (.inr ⟨_, _⟩) k =>
      (match k (.success (Test.Dogfood.Scenario.Routing.configOf "secret" 20)) with
       | .vis (.inr ⟨j, _⟩) next =>
         decide (j.val = 1) &&
           (match next (.failure (Cause.fail (.tagged "SqlError" "locked"))) with
            | .pure ex => decide (ex = .failure (Cause.fail (.tagged "SqlError" "locked")))
            | .vis _ _ => false)
       | _ => false)
    | _ => false) = some true

-- reader (`meaningUnder_straight`): a program with no call reads no reply, under any reply tape
example (tape : ReplyTape) :
    meaningRows [wait] cell [] Stores.empty tape = some (meaning cell [] Stores.empty, tape) :=
  meaningUnder_straight (tapeHandler [wait]) cell [] Stores.empty tape rfl
-- control: the law stops at a call. With no reply the meaning is the frontier
#guard (meaningRows [wait] chain [] Stores.empty []).isNone

-- control (the fragment): a row that answers a handle is outside it
#guard StraightRows [kvMake] (call 0 (.lit .unit)) = false
-- finite evaluation (the fragment): the routing program is inside it, by its `catchIf` arm
#guard (built? (Test.Dogfood.Scenario.Routing.request "secret" 2 "2")).map
    (fun b => StraightRows b.table b.program) = some true
-- control (the table's domain): the checker refuses a position outside the table
#guard ((Effect4.Api.Author.Internal.finishBuild (call 3 (num 1)) [wait] []).toOption).isNone

/-! ## Slice H2: an appended table -/

-- reader (`meaningUnder_append`): three calls keep their meaning under a host of a longer table
example {σ : Type} (host : Effects.Handler (RowSig ([wait] ++ [kvMake])) (StateT σ Option))
    (s : Stores) (state : σ) :
    meaningUnder host chain [] s state =
      meaningUnder (restrictRows [wait] [kvMake] host) chain [] s state :=
  meaningUnder_append [wait] [kvMake] host chain [] s state rfl
-- control (the premise): a call of the appended row is outside the old table's fragment. A host
-- of the longer table answers it, and the restricted host is not asked
#guard StraightRows [wait] (call 1 (num 1)) = false
#guard (meaningRows ([wait] ++ [wait]) (call 1 (num 1)) [] Stores.empty [.success (.nat 5)]).map (·.1.1)
    = some (.success (.nat 5)) &&
  (meaningUnder (restrictRows [wait] [wait] (tapeHandler ([wait] ++ [wait]))) (call 1 (num 1)) []
      Stores.empty [.success (.nat 5)]).map (·.1.1) = some outsideExit

/-! ## Slice H3: the reference machine's term -/

-- reader (`denoteR_straightRows`): the reference machine's term of three calls, erased, is their
-- tree read into the reference machine's signature
example (p : Point) (h : Agreement.depth chain ≤ p.fuel) :
    eraseControl (denoteR chain chain p) =
      Effects.interpret (toRef [wait]) (denoteRows [wait] chain p.env) :=
  denoteR_straightRows chain [wait] chain p rfl h

end Test.Program.DenoteRowsContract
