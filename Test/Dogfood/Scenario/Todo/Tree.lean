import Test.Dogfood.Scenario.Todo
import Test.Dogfood.Scenario.Routing.Calls
import Effect4.Laws.Api.AuthorBuild
import Effect4.Laws.Auto.KernelRfl
import Effect4.Laws.Program.Validated
import Effect4.Laws.Api.HostDrive

/-!
# The to-do application's call trees

The claims packet's slice TREE (`docs/research/2026-10-07-packet-application-claims.md`, §3.9):
the tree forms of the to-do claims over `denoteRows` (`src/Effect4/Laws/Program/DenoteRows.lean`).
Each statement here is a step of a claim of `Test/Dogfood/Scenario/Todo/Claims.lean`, which reads
it on a run through a theorem of the session's meaning.

* **A built entry is its elaboration** (`builtAt_program`): a build retains its elaboration
  (`Effect4.Api.Author.build_retains`), and each entry elaborates at a free argument by
  computation. `aesop` closes each such equation that it reaches from its statement (decisions row
  376 (3); `#auto_census`), and `kernel_rfl` the others, as `Test/Dogfood/Proofs/HostRouting.lean`
  does for the routing request. An entry at its argument is its open program under one bind of
  the argument.
* **The fragment.** Each program is in `StraightRows`, has no cause handler, calls only external
  rows, over a table whose reply columns are closed: the premises of `held_in_tree` and of H8
  and H9.
* **The tree forms.** `add` at the empty title is one leaf (`add_empty_tree`). A failing answer of
  `complete`'s one call is its exit (`complete_failure_meaning`). Under the protocol of `setDone`,
  `complete`'s tree meets the postcondition "the requested to-do" (`complete_sat`).
* **The trees under the reference model.** The model, read as a host (`Run.reactorHost`), runs
  `add` at a title that is not empty (`add_on_model`), `list` (`list_on_model`), and `complete` in
  its two cases (`complete_on_model_found`, `complete_on_model_missing`). The model's answer at a
  call is `Run.reactorHost_answer`'s (`src/Effect4/Laws/Api/HostDrive.lean`).

Reach: the four entries at every argument that the statements name. Nothing here reads a run.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Test.Dogfood.Scenario.Todo

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring Effect4.Program.Denote
open Effect4.Run.CallTree (NoCauseHandler treeWaits treeWaits_eq)
open Effect4.Run (rowsProtocol declaredProtocol reactorHost reactorHost_answer)
open Effect4.Laws.Auto
open Test.Dogfood.Scenario (ok)

/-! ## 1. A built entry is its elaboration -/

/-- The open program of an entry, read off its elaboration. -/
def openOf (name : String) : NativeEff :=
  match (application.entry? name).map application.openProgram with
  | some (.ok p) => p
  | _ => .succeed (.lit .unit)

/-- `add` at a title: the open program under one bind of the title. -/
def addAt (title : String) : NativeEff := .bind (.succeed (.lit (.str title))) (openOf "add")

/-- `complete` at an id: the open program under one bind of the id. -/
def completeAt (id : Nat) : NativeEff := .bind (.succeed (.lit (.nat id))) (openOf "complete")

/-- `list`: the open program, which has no parameter. -/
def listAt : NativeEff := openOf "list"

/-- **A built entry's program is its elaboration, over the application's table.** A step of every
to-do claim: it reads the program off the elaboration, which the kernel computes with free
arguments, where the build's checker does not. -/
theorem builtAt_program {name : String} {args : List TermSrc} {b : Api.Built} {p : NativeEff}
    (h : builtAt name args = some b)
    (hp : (application.entry? name).map (fun e => elaborateModule (application.moduleOf e args)) =
      some (.ok p)) :
    b.program = p ∧ b.table = application.table := by
  unfold builtAt at h
  cases he : application.entry? name with
  | none =>
    rw [he] at h
    cases h
  | some e =>
    rw [he] at h hp
    have hp' : elaborateModule (application.moduleOf e args) = .ok p := Option.some.inj hp
    cases hbuild : Effect4.Api.Author.build (application.moduleOf e args) with
    | error why =>
      have hnone : Test.Dogfood.P2HandlerLayers.built? (application.moduleOf e args) = none := by
        unfold Test.Dogfood.P2HandlerLayers.built?
        rw [hbuild]
        rfl
      rw [Option.bind_some, hnone] at h
      cases h
    | ok b' =>
      have hsome : Test.Dogfood.P2HandlerLayers.built? (application.moduleOf e args) = some b' := by
        unfold Test.Dogfood.P2HandlerLayers.built?
        rw [hbuild]
        rfl
      rw [Option.bind_some, hsome] at h
      cases h
      obtain ⟨hprog, htable, -⟩ := Effect4.Api.Author.build_retains hbuild
      rw [hp'] at hprog
      exact ⟨(Except.ok.inj hprog).symm, htable.trans (Application.moduleOf_table _ _ _)⟩

/-- The kernel elaborates `add` at a free title. A step of `add_empty_calls_nothing` and
`list_after_add`. -/
theorem add_elaborates (title : String) :
    (application.entry? "add").map (fun e => elaborateModule (application.moduleOf e [str title])) =
      some (.ok (addAt title)) := by
  aesop

/-- The kernel elaborates `complete` at a free id. A step of the three claims of `complete`. -/
theorem complete_elaborates (id : Nat) :
    (application.entry? "complete").map
        (fun e => elaborateModule (application.moduleOf e [nat id])) =
      some (.ok (completeAt id)) := by
  kernel_rfl

/-- The kernel elaborates `list`. A step of `list_after_add`. -/
theorem list_elaborates :
    (application.entry? "list").map (fun e => elaborateModule (application.moduleOf e [])) =
      some (.ok listAt) := by
  aesop

/-! ## 2. The fragment -/

/-- `add` is in the row fragment at every title. A step of `add_empty_calls_nothing` and
`list_after_add`. -/
theorem add_straight (title : String) : StraightRows application.table (addAt title) = true := by
  aesop

/-- `complete` is in the row fragment at every id. A step of the three claims of `complete`. -/
theorem complete_straight (id : Nat) :
    StraightRows application.table (completeAt id) = true := by
  aesop

/-- `list` is in the row fragment. A step of `list_after_add`. -/
theorem list_straight : StraightRows application.table listAt = true := by
  aesop

/-- `add` has no cause handler at any title. A step of `add_empty_calls_nothing`. -/
theorem add_noCause (title : String) : NoCauseHandler (addAt title) = true := by
  aesop

/-- `add` calls only external rows at any title. A step of `add_empty_calls_nothing`. -/
theorem add_externalOnly (title : String) : SourceScope.ExternalOnly (addAt title) := by
  aesop

/-- The repository's reply columns are closed. A step of `add_empty_calls_nothing`. -/
theorem table_concrete : SourceScope.ConcreteReplies application.table := by
  aesop

/-! ## 3. The tree forms -/

/-- The failure of an empty title, at the root. -/
def emptyTitleExit : ExitV := .failure (Cause.fail (.tagged "EmptyTitle" "a title is required"))

/-- **`add` at the empty title is one leaf**: its tree makes no call. The tree form of
`add_empty_calls_nothing`. -/
theorem add_empty_tree : denoteRows application.table (addAt "") [] = .pure emptyTitleExit := by
  aesop

/-- Under any tape, the tree of `add` at the empty title finishes at its leaf and waits at no
call. A step of `add_empty_calls_nothing`. -/
theorem add_empty_waits_nothing (T : ReplyTape) :
    treeWaits application.table (addAt "") T = .finished emptyTitleExit := by
  aesop

/-- **A failing answer of `complete`'s one call is its exit**, under the reply tape, at every id
and every cause, with the rest of the tape unread. The tree form of `complete_failure_escapes`. -/
theorem complete_failure_meaning (id : Nat) (cause : CauseV) (rest : ReplyTape) :
    meaningRows application.table (completeAt id) [] Stores.empty (.failure cause :: rest) =
      some ((.failure cause, Stores.empty), rest) := by
  aesop

/-- The part of `complete`'s open program after its one call: the selection on the answer. -/
def completeSel : NativeEff :=
  match openOf "complete" with
  | .bind _ sel => sel
  | _ => .succeed (.lit .unit)

/-- **The tree of `complete`**: one call of `setDone` at `(id, true)`, then the selection on the
answer. A step of `complete_sat` and `complete_on_model`. -/
theorem complete_tree (id : Nat) :
    denoteRows application.table (completeAt id) [] =
      .vis (.inr ⟨⟨2, by decide⟩, .list [.nat id, .bool true]⟩)
        (fun a => seqRows (fun v => denoteRows application.table completeSel [.nat id, v]) a) := by
  aesop

/-- The postcondition of `complete` under `setDone`'s protocol: a successful exit keeps the
promise at the request `(id, true)`. -/
def requested (id : Nat) (ex : ExitV) : Prop :=
  ∀ v, ex = .success v → setDoneProtocol.keeps (.list [.nat id, .bool true]) (.some v) = true

/-- **Under the protocol of `setDone`, the tree of `complete` answers the requested to-do**: at
every id, the tree meets `requested` under the stores and the application's protocols
(`Effects.Program.Sat`). Only an answer `some v` leads to a success, `v`, and the protocol's
promise at that answer is the postcondition. The tree form of `complete_answers_requested`. -/
theorem complete_sat (id : Nat) :
    Effects.Program.Sat (rowsProtocol application.table protocols) (requested id)
      (denoteRows application.table (completeAt id) []) := by
  rw [complete_tree id]
  intro a ha
  cases a with
  | failure c => exact fun v hv => nomatch hv
  | success x =>
    cases x with
    | some v =>
      have hkeep : setDoneProtocol.keeps (.list [.nat id, .bool true]) (.some v) = true := ha
      exact fun w hw => by
        cases hw
        exact hkeep
    | unit | bool _ | nat _ | str _ | bytes _ | list _ | pair _ _ | none | ctor _ _ | ref _ _
    | handle _ _ | negInt _ | float _ => exact fun v hv => nomatch hv

/-! ## 4. The trees under the reference model -/

/-- **`list` under the model** answers the stored to-dos and leaves the model's state. A step of
`list_after_add`. -/
theorem list_on_model (st : Repo) :
    hostRun (reactorHost application.table repository) listAt [] Stores.empty st =
      some (.success (.list (st.2.map todoOf)), (Stores.empty, st)) := by
  aesop

/-- The test of `add`'s open program: the title against the empty one. -/
def addTest : Term :=
  match openOf "add" with
  | .select t _ _ _ => t
  | _ => .lit .unit

/-- The arm of `add`'s open program at an empty title. -/
def addThen : NativeEff :=
  match openOf "add" with
  | .select _ _ a _ => a
  | _ => .succeed (.lit .unit)

/-- The arm of `add`'s open program at another title. -/
def addElse : NativeEff :=
  match openOf "add" with
  | .select _ _ _ b => b
  | _ => .succeed (.lit .unit)

/-- The test of `add` at a title is the title's comparison with the empty one. A step of
`add_tree`. -/
theorem add_test (title : String) :
    evalTerm [.str title] addTest = some (.bool (title == "")) := by
  aesop

/-- **`add` at a title that is not empty calls `insert` with the title**, and its exit is the
answer. A step of `add_on_model`. -/
theorem add_tree (title : String) (hne : title ≠ "") :
    denoteRows application.table (addAt title) [] =
      .vis (.inr ⟨⟨0, by decide⟩, .str title⟩) .pure := by
  have hsel : denoteRows application.table (addAt title) [] =
      denoteRows application.table (.select addTest .bool addThen addElse) [.str title] := by
    kernel_rfl
  rw [hsel, denoteRows, add_test, Option.bind_some, Decision.decide, beq_eq_false_iff_ne.mpr hne]
  kernel_rfl

/-- **`add` under the model** at a title that is not empty stores the to-do under the next id and
answers it. A step of `list_after_add`. -/
theorem add_on_model (title : String) (hne : title ≠ "") (st : Repo) :
    hostRun (reactorHost application.table repository) (addAt title) [] Stores.empty st =
      some (.success (todo st.1 title false),
        (Stores.empty, (st.1 + 1, st.2 ++ [(st.1, title, false)]))) := by
  unfold hostRun
  rw [add_tree title hne]
  kernel_rfl

/-- The model's `setDone` at `true` on one stored to-do: it marks the to-do of the id done. -/
def markDone (id : Nat) (e : Nat × String × Bool) : Nat × String × Bool :=
  if e.1 == id then (e.1, e.2.1, true) else e

/-- Marking keeps a to-do's id. A step of `find_markDone`. -/
theorem markDone_fst (id : Nat) (e : Nat × String × Bool) : (markDone id e).1 = e.1 := by
  unfold markDone
  split <;> rfl

/-- Marking keeps a to-do's title. A step of `complete_idempotent`. -/
theorem markDone_title (id : Nat) (e : Nat × String × Bool) : (markDone id e).2.1 = e.2.1 := by
  unfold markDone
  split <;> rfl

/-- Marking twice is marking once. A step of `map_markDone_idem`. -/
theorem markDone_idem (id : Nat) (e : Nat × String × Bool) :
    markDone id (markDone id e) = markDone id e := by
  unfold markDone
  split <;> rfl

/-- After marking, the to-do of the id is found where it was, marked. A step of
`complete_idempotent`. -/
theorem find_markDone (id : Nat) (l : List (Nat × String × Bool)) :
    (l.map (markDone id)).find? (·.1 == id) = (l.find? (·.1 == id)).map (markDone id) := by
  rw [List.find?_map]
  congr 2
  funext e
  simp only [Function.comp, markDone_fst]

/-- Marking the stored to-dos twice is marking them once. A step of `complete_idempotent`. -/
theorem map_markDone_idem (id : Nat) (l : List (Nat × String × Bool)) :
    (l.map (markDone id)).map (markDone id) = l.map (markDone id) := by
  rw [List.map_map]
  congr 1
  funext e
  exact markDone_idem id e

/-- The row the host is asked at `setDone`'s position, as the table registers it. -/
def setDoneRow : Row := (application.table[2]'(by decide)).normalizeTypes

/-- The table registers `setDone` at position 2. A step of the trees of `complete` under the
model. -/
theorem setDone_row : externalRow application.table 2 = some setDoneRow := by
  aesop

/-- The model's answer to `setDone` at `(id, true)`, by what it finds at the id. A step of the
trees of `complete` under the model. -/
theorem repository_setDone (id : Nat) (st : Repo) :
    repository setDoneRow (.list [.nat id, .bool true]) st =
      match st.2.find? (·.1 == id) with
      | some entry => some (ok (.some (todo id entry.2.1 true)), (st.1, st.2.map (markDone id)))
      | none => some (ok .none, st) := by
  kernel_rfl

/-- The exit of `complete` at an answer `none`: the missing to-do's failure. -/
def notFoundExit (id : Nat) : ExitV :=
  match denoteRows application.table completeSel [.nat id, .none] with
  | .pure ex => ex
  | _ => .success .unit

/-- At an answer `none`, the tree of `complete` is the missing to-do's failure. -/
theorem complete_none (id : Nat) :
    denoteRows application.table completeSel [.nat id, .none] = .pure (notFoundExit id) := by
  aesop

/-- At an answer `some v`, the tree of `complete` succeeds with `v`. -/
theorem complete_some (id : Nat) (v : Val) :
    denoteRows application.table completeSel [.nat id, .some v] = .pure (.success v) := by
  aesop

/-- **`complete` under the model, where the id is stored**: it answers the to-do marked done, and
the model marks it. A step of `complete_idempotent`. -/
theorem complete_on_model_found (id : Nat) (st : Repo) (entry : Nat × String × Bool)
    (hfind : st.2.find? (·.1 == id) = some entry) :
    hostRun (reactorHost application.table repository) (completeAt id) [] Stores.empty st =
      some (.success (todo id entry.2.1 true), (Stores.empty, (st.1, st.2.map (markDone id)))) := by
  have hrep : repository setDoneRow (.list [.nat id, .bool true]) st =
      some (ok (.some (todo id entry.2.1 true)), (st.1, st.2.map (markDone id))) := by
    rw [repository_setDone, hfind]
  have hans := reactorHost_answer application.table repository (i := 2) (by decide) setDone_row
    hrep
  unfold hostRun
  rw [complete_tree id, Effects.Comodel.run_vis_some _ _
    (show (rowsHost (reactorHost application.table repository)).answer
        (.inr ⟨⟨2, by decide⟩, .list [.nat id, .bool true]⟩) (Stores.empty, st) =
      some (.success (.some (todo id entry.2.1 true)),
        (Stores.empty, (st.1, st.2.map (markDone id)))) by
    show ((reactorHost application.table repository).answer _ st).map _ = _
    rw [hans]
    rfl)]
  show (rowsHost _).run
    (denoteRows application.table completeSel [.nat id, .some (todo id entry.2.1 true)]) _ = _
  rw [complete_some]
  rfl

/-- **`complete` under the model, where the id is not stored**: it fails with the missing to-do,
and the model's state stays. A step of `complete_idempotent`. -/
theorem complete_on_model_missing (id : Nat) (st : Repo)
    (hfind : st.2.find? (·.1 == id) = none) :
    hostRun (reactorHost application.table repository) (completeAt id) [] Stores.empty st =
      some (notFoundExit id, (Stores.empty, st)) := by
  have hrep : repository setDoneRow (.list [.nat id, .bool true]) st = some (ok .none, st) := by
    rw [repository_setDone, hfind]
  have hans := reactorHost_answer application.table repository (i := 2) (by decide) setDone_row
    hrep
  unfold hostRun
  rw [complete_tree id, Effects.Comodel.run_vis_some _ _
    (show (rowsHost (reactorHost application.table repository)).answer
        (.inr ⟨⟨2, by decide⟩, .list [.nat id, .bool true]⟩) (Stores.empty, st) =
      some (.success .none, (Stores.empty, st)) by
    show ((reactorHost application.table repository).answer _ st).map _ = _
    rw [hans]
    rfl)]
  show (rowsHost _).run (denoteRows application.table completeSel [.nat id, .none]) _ = _
  rw [complete_none]
  rfl

end Test.Dogfood.Scenario.Todo
