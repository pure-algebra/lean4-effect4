-- Synthesis seat port to the merged head (0c534f06): FitsExit read through H2's ExitOk.
import Effect4.Laws.Program.Typed.Assembly

/-!
# Formal pass, seat PROOFS — red control: three store postconditions exclude the store's answer

Base `efd67af1`. Reading aid for `note.md` §3 G6. The store protocol's postcondition for
`scopeAdd`, `scopeRemove` and `deferredAwaitCleanup` is `∃ b, ans = Val.bool b`
(`Laws/Program/Typed/Residual.lean:70,74`). The store answers `Val.unit` for all three
(`scopeAdd` on an open scope; on a closed one it answers the reified closing exit),
`Machine/Stores.lean:1953-1954,1966-1978`. So no real answer of these rows meets the post, and
`TypedProg`'s store arm, which types the continuation only at answers the post admits, admits a
program whose very next step is untyped: the impossible-post shape the post-Phase C plan
forbids (§5.3), the converse of `E4-SCHED-CE-013`'s `True` posts.

* `scopeRemove_answer`, `awaitCleanup_answer`, `scopeAdd_open_answer`: the store's answers.
* `*_post_excludes`: at every world and certificate, those answers fail the post.
* `admitted`: a continuation that is ill-typed at `unit` is typed at `nat` by the store arm.
* `next_untyped`: the continuation the machine actually runs is untyped at every world.
-/

set_option autoImplicit false

namespace Research.Synthesis.HeadStorePostAdequacy
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Typed
abbrev W := Effect4.Program.Typed.World

/-! ## The store's answers -/

theorem scopeRemove_answer (st : Stores) (scope key : Nat) :
    ∃ st', syncOpStep (.scopeRemove scope key) st = some (st', Val.unit) := ⟨_, rfl⟩

theorem awaitCleanup_answer (st : Stores) (cell : DeferredKey) (waiter : FiberId) (token : Nat) :
    ∃ st', syncOpStep (.deferredAwaitCleanup cell waiter token) st = some (st', Val.unit) :=
  ⟨_, rfl⟩

/-- A store holding one open sequential scope at key 0. -/
def oneScope : Stores :=
  ((syncOpStep (.scopeMake .sequential) Stores.empty).map (·.1)).getD Stores.empty

theorem scopeAdd_open_answer :
    ((syncOpStep (.scopeAdd 0 (.closeChildScope 9)) oneScope).map (·.2)) = some Val.unit := by
  decide +kernel

/-! ## The post excludes them -/

theorem unit_not_bool : ¬ ∃ b, (Val.unit : Val) = Val.bool b := by
  rintro ⟨b, h⟩
  cases h

theorem scopeRemove_post_excludes (w : W) (scope key : Nat) (cert : StoreCert (.scopeRemove scope key)) :
    ¬ storePost w (.scopeRemove scope key) cert Val.unit := unit_not_bool

theorem scopeAdd_post_excludes (w : W) (scope : Nat) (fin : FinName)
    (cert : StoreCert (.scopeAdd scope fin)) :
    ¬ storePost w (.scopeAdd scope fin) cert Val.unit := unit_not_bool

theorem awaitCleanup_post_excludes (w : W) (cell : DeferredKey) (waiter : FiberId) (token : Nat)
    (cert : StoreCert (.deferredAwaitCleanup cell waiter token)) :
    ¬ storePost w (.deferredAwaitCleanup cell waiter token) cert Val.unit := unit_not_bool

/-! ## The program judgment admits an untyped next step -/

def natTy : EffTy := EffTy.pure .nat

/-- Answers a string at `unit`, which the machine gives, and a number at every `bool`, which it
never gives. -/
def k : Val → RProgram := fun v =>
  if v = Val.unit then .pure (.success (.str "x")) else .pure (.success (.nat 0))

def code : RProgram := .vis (.inl (.scopeRemove 0 1)) k

theorem admitted (root : ProgramSource) (w : W) : TypedProg root w natTy code := by
  refine TypedProg.store (cert := PUnit.unit) trivial ?_
  intro w' _ ans post
  obtain ⟨b, rfl⟩ := post
  have hk : k (Val.bool b) = .pure (.success (.nat 0)) := by
    unfold k
    rw [if_neg (by intro h; cases h)]
  rw [hk]
  exact TypedProg.pure ⟨trivial, trivial⟩

theorem next_untyped (root : ProgramSource) (w' : W) : ¬ TypedProg root w' natTy (k Val.unit) := by
  intro h
  have hk : k Val.unit = .pure (.success (.str "x")) := by
    unfold k
    rw [if_pos rfl]
  rw [hk] at h
  exact (TypedProg.pure_inv h).1

/-- Together: a typed program whose store step (any store) leads to an untyped program. -/
theorem store_step_leaves_typing (root : ProgramSource) (w : W) (st : Stores) :
    TypedProg root w natTy code ∧
      ∃ st', syncOpStep (.scopeRemove 0 1) st = some (st', Val.unit) ∧
        ∀ w', ¬ TypedProg root w' natTy (k Val.unit) :=
  ⟨admitted root w, (scopeRemove_answer st 0 1).elim fun st' h => ⟨st', h, next_untyped root⟩⟩

end Research.Synthesis.HeadStorePostAdequacy

open Research.Synthesis.HeadStorePostAdequacy in
#print axioms scopeRemove_answer
open Research.Synthesis.HeadStorePostAdequacy in
#print axioms awaitCleanup_answer
open Research.Synthesis.HeadStorePostAdequacy in
#print axioms scopeAdd_open_answer
open Research.Synthesis.HeadStorePostAdequacy in
#print axioms scopeRemove_post_excludes
open Research.Synthesis.HeadStorePostAdequacy in
#print axioms scopeAdd_post_excludes
open Research.Synthesis.HeadStorePostAdequacy in
#print axioms awaitCleanup_post_excludes
open Research.Synthesis.HeadStorePostAdequacy in
#print axioms admitted
open Research.Synthesis.HeadStorePostAdequacy in
#print axioms next_untyped
open Research.Synthesis.HeadStorePostAdequacy in
#print axioms store_step_leaves_typing
