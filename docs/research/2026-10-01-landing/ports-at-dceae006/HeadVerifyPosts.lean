-- Synthesis seat port to the merged head (0c534f06): FitsExit read through H2's ExitOk.
import Effect4.Laws.Program.Typed.Assembly

/-!
# Verifier of seat PROOFS — protocol rows the seat did not check

Base `ea5b28b5`. Three more rows whose protocol does not match the handler, beside the seat's
five (await-by-value, closeScope, scopeAdd, scopeRemove, deferredAwaitCleanup):

* `memoRelease`: the last observer's release answers the layer scope's handle
  (`Machine/Stores.lean:2027-2028`); the post says `ans = unit` (`Typed/Residual.lean:81`).
  `TypedProg` admits a program typed only at `unit` whose real next step is untyped.
* `refModify` (and `refModifySome`): the pre admits a cell declared at any type
  (`Typed/Residual.lean:41-43`); on a `bool` cell the handler answers the old `bool`
  (`Machine/Stores.lean:910-911`, `FnName.modify`), the post says `∃ n, ans = nat n`
  (`:66`). So the seat's proposed per-row adequacy obligation is false at this row as stated:
  the pre holds and no world admits the answer.
* `closeIter`: the walk's answer is its own merged exit (`closeDone`, `success unit` with no
  finalizer failure, `Machine/Stores.lean:1619-1621`; `InterpR.lean:136-145,298-303`); the post
  says the answer is the scope's closing exit (`Typed/Residual.lean:160`).
-/

set_option autoImplicit false

namespace Research.Synthesis.HeadVerifyPosts
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Typed
abbrev W := Effect4.Program.Typed.World

/-! ## memoRelease -/

/-- A store with one memo map holding one built entry for the layer at `[]` (one observer). -/
def memoStore : Stores :=
  let s1 := (syncOpStep (.memoFork none) Stores.empty).map (·.1) |>.getD Stores.empty
  (syncOpStep (.memoBuild [] ⟨0⟩) s1).map (·.1) |>.getD s1

theorem memoRelease_answers_scope :
    ((syncOpStep (.memoRelease [] ⟨0⟩) memoStore).map (·.2)) = some (Val.scopeHandle 1) := by
  decide +kernel

theorem memoRelease_post_excludes (w : W) (cert : StoreCert (.memoRelease [] ⟨0⟩)) :
    ¬ storePost w (.memoRelease [] ⟨0⟩) cert (Val.scopeHandle 1) := by
  intro h
  cases h

def natTy : EffTy := EffTy.pure .nat
/-- Typed at the post's `unit`; at the handle the machine gives, a string at `nat`. -/
def k : Val → RProgram := fun v =>
  if v = Val.unit then .pure (.success (.nat 0)) else .pure (.success (.str "x"))
def memoCode : RProgram := .vis (.inl (.memoRelease [] ⟨0⟩)) k

theorem memo_admitted (root : ProgramSource) (w : W) : TypedProg root w natTy memoCode := by
  refine TypedProg.store (cert := PUnit.unit) trivial ?_
  intro w' _ ans post
  have hans : ans = Val.unit := post
  subst hans
  have hk : k Val.unit = .pure (.success (.nat 0)) := by
    unfold k
    rw [if_pos rfl]
  rw [hk]
  exact TypedProg.pure ⟨trivial, trivial⟩

theorem memo_next_untyped (root : ProgramSource) (w' : W) :
    ¬ TypedProg root w' natTy (k (Val.scopeHandle 1)) := by
  intro h
  have hk : k (Val.scopeHandle 1) = .pure (.success (.str "x")) := by
    unfold k
    rw [if_neg (by intro e; cases e)]
  rw [hk] at h
  exact (TypedProg.pure_inv h).1

/-! ## refModify on a `bool` cell -/

def boolCellStore : Stores :=
  (syncOpStep (.refMake (.bool true)) Stores.empty).map (·.1) |>.getD Stores.empty

theorem refModify_bool_answer :
    ((syncOpStep (.refModify ⟨0⟩ .incr) boolCellStore).map (·.2)) = some (Val.bool true) := by
  decide +kernel

/-- A world declaring cell 0 at `bool`. -/
def wb : W := { initialWorld natTy with Ρ := tableInsert (fun _ => none) ⟨0⟩ .bool }

theorem refModify_pre (root : ProgramSource) (cert : StoreCert (.refModify ⟨0⟩ .incr)) :
    storePre root wb (.refModify ⟨0⟩ .incr) cert := ⟨.bool, rfl⟩

theorem refModify_post_excludes (w' : W) (cert : StoreCert (.refModify ⟨0⟩ .incr)) :
    ¬ storePost w' (.refModify ⟨0⟩ .incr) cert (Val.bool true) := by
  rintro ⟨n, h⟩
  cases h

/-- The seat's adequacy obligation, instantiated at this row, is false: the pre holds, the
handler answers, and no world admits the answer. -/
theorem adequacy_false_refModify (root : ProgramSource) (cert : StoreCert (.refModify ⟨0⟩ .incr)) :
    storePre root wb (.refModify ⟨0⟩ .incr) cert ∧
      ((syncOpStep (.refModify ⟨0⟩ .incr) boolCellStore).map (·.2)) = some (Val.bool true) ∧
      ¬ ∃ w', storePost w' (.refModify ⟨0⟩ .incr) cert (Val.bool true) :=
  ⟨refModify_pre root cert, refModify_bool_answer, fun ⟨w', h⟩ => refModify_post_excludes w' cert h⟩

/-! ## closeIter -/

def failed : ExitV := .failure (Cause.fail (.tag 1))

def isDoneUnit : IterStep EffName EffThunk Val Err Defect FiberId Ann RProgram → Bool
  | .done .unit => true
  | _ => false

/-- With no finalizer failure the walk answers `success unit`, whatever exit closed the scope. -/
theorem closeSeq_done (root : NativeEff) :
    isDoneUnit ((interpR root).iterNext (.store (.closeSeq [] failed [])) .unit).2 = true := rfl

theorem closeIter_post_excludes (w : W) (cert : FiberCert (.closeIter .sequential [] failed)) :
    ¬ fiberPost w (.closeIter .sequential [] failed) cert (.success .unit) := by
  intro h
  cases h

/-! ## The frontier arm: a store step that returns `none`

`evaluateRawR` answers `next .unit` when `syncOpStep` returns `none`
(`Laws/Program/EvaluateR.lean:304`; the native machine answers `syncValue`,
`Machine/Fibers.lean:1169-1171`). The five scope rows have the precondition `True`
(`Typed/Residual.lean:49`), so a typed program may name an unknown scope; `scopeIsClosed`
then answers `unit` where its post says `bool`. An adequacy obligation over `some` results
alone does not see this arm. -/

theorem scopeIsClosed_unknown : syncOpStep (.scopeIsClosed 7) Stores.empty = none := rfl

theorem scopeIsClosed_pre (root : ProgramSource) (w : W) (cert : StoreCert (.scopeIsClosed 7)) :
    storePre root w (.scopeIsClosed 7) cert := trivial

theorem scopeIsClosed_post_excludes_unit (w : W) (cert : StoreCert (.scopeIsClosed 7)) :
    ¬ storePost w (.scopeIsClosed 7) cert Val.unit := by
  rintro ⟨b, h⟩
  cases h

end Research.Synthesis.HeadVerifyPosts

open Research.Synthesis.HeadVerifyPosts in
#print axioms memoRelease_answers_scope
open Research.Synthesis.HeadVerifyPosts in
#print axioms memoRelease_post_excludes
open Research.Synthesis.HeadVerifyPosts in
#print axioms memo_admitted
open Research.Synthesis.HeadVerifyPosts in
#print axioms memo_next_untyped
open Research.Synthesis.HeadVerifyPosts in
#print axioms refModify_bool_answer
open Research.Synthesis.HeadVerifyPosts in
#print axioms refModify_pre
open Research.Synthesis.HeadVerifyPosts in
#print axioms refModify_post_excludes
open Research.Synthesis.HeadVerifyPosts in
#print axioms adequacy_false_refModify
open Research.Synthesis.HeadVerifyPosts in
#print axioms closeSeq_done
open Research.Synthesis.HeadVerifyPosts in
#print axioms closeIter_post_excludes
open Research.Synthesis.HeadVerifyPosts in
#print axioms scopeIsClosed_unknown
open Research.Synthesis.HeadVerifyPosts in
#print axioms scopeIsClosed_pre
open Research.Synthesis.HeadVerifyPosts in
#print axioms scopeIsClosed_post_excludes_unit
