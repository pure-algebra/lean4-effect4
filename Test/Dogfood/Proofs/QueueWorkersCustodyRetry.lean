import Test.Dogfood.Proofs.QueueWorkersCustodySource
import Effect4.Laws.Machine.AnswerFlowRecursiveFamily

/-!
Concept: translation-simulation R10.
Consumer: QueueWorkers.Assertions.jobs_step, through the typed retry-loop hook.
The actual retry step returns its classified option, retaining its exact payload.
The native body and whole-history source-role producers remain separate obligations.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.QueueWorkersCustody
open Effect4 Effect4.Machine Effect4.Program

/-- The request loop tests whether its cursor still lacks a result. -/
def retryTest (index : Nat) : Term :=
  .app "not" (.cons (.app "isSome" (.cons (.var index) .nil)) .nil)

/-- The actual retry loop uses the returned option as its next cursor. -/
theorem retry_resume (root : NativeEff) (point : Point) (body : NativeEff)
    (shape : loopAt root point = some (retryTest point.env.length, .var (point.env.length + 1), body))
    (cursor answer : Val) : loopResumeAt root point cursor answer = loopNextAt root point answer := by
  have last : (point.env ++ [cursor, answer])[point.env.length + 1]? = some answer := by
    have read : ((point.env ++ [cursor]) ++ [answer])[(point.env ++ [cursor]).length]? = some answer :=
      List.getElem?_concat_length
    simpa only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero, Nat.zero_add, List.append_assoc, List.cons_append, List.nil_append] using read
  simp only [loopResumeAt, shape, evalTerm, last]

/-- A completed retry cursor returns itself from the existing source result expression. -/
theorem retry_finish (root : NativeEff) (point : Point)
    (result : loopResultAt root point = some (.var point.env.length)) (cursor : Val) :
    loopFinishAt root point cursor = .success cursor := by
  have last : (point.env ++ [cursor])[point.env.length]? = some cursor := List.getElem?_concat_length
  simp only [loopFinishAt, result, evalTerm, last]

/-- An unfinished retry cursor executes the actual source body at that waiting option. -/
theorem retry_waiting (root : NativeEff) (point : Point) (body : NativeEff)
    (shape : loopAt root point = some (retryTest point.env.length, .var (point.env.length + 1), body)) :
    loopNextAt root point .none = .continue .none (resolve root (point.childWith 0 .none)) := by
  have last : (point.env ++ [Store.Val.none])[point.env.length]? = some Store.Val.none := List.getElem?_concat_length
  simp only [loopNextAt, shape, retryTest, evalTerm, evalTerms, last, Option.bind_some,
    nativeAtom, NativeAtom.ofName?]
  rfl

/-- A successful retry cursor leaves the loop with the very option that the take classified. -/
theorem retry_obtained (root : NativeEff) (point : Point) (body : NativeEff)
    (shape : loopAt root point = some (retryTest point.env.length, .var (point.env.length + 1), body))
    (result : loopResultAt root point = some (.var point.env.length)) (job : Nat) :
    loopNextAt root point (.some (.nat job)) = .finish (.success (.some (.nat job))) := by
  have last : (point.env ++ [Store.Val.some (.nat job)])[point.env.length]? = some (Store.Val.some (.nat job)) :=
    List.getElem?_concat_length
  simp only [loopNextAt, shape, retryTest, evalTerm, evalTerms, last, Option.bind_some,
    nativeAtom, NativeAtom.ofName?]
  exact congrArg LoopNext.finish (retry_finish root point result (.some (.nat job)))

/-- The actual saved loop consumes its request's current option, never an arbitrary stale answer. -/
theorem retry_classified (root : NativeEff) (point : Point) (body : NativeEff)
    (shape : loopAt root point = some (retryTest point.env.length, .var (point.env.length + 1), body))
    (result : loopResultAt root point = some (.var point.env.length))
    (world : World) (token : Nat) (cursor answer : Val)
    (typed : ValueAt world (.takeOption token) answer) :
    (world.requests token = .waiting ∧ loopResumeAt root point cursor answer =
      .continue .none (resolve root (point.childWith 0 .none))) ∨
    (∃ job, world.requests token = .holding job ∧ answer = .some (.nat job) ∧
      loopResumeAt root point cursor answer = .finish (.success answer)) := by
  change OptionAt world token answer at typed
  unfold OptionAt at typed
  split at typed
  next =>
    exact .inl ⟨typed, (retry_resume root point body shape cursor .none).trans
      (retry_waiting root point body shape)⟩
  next job =>
    exact .inr ⟨job, typed, rfl, (retry_resume root point body shape cursor (.some (.nat job))).trans
      (retry_obtained root point body shape result job)⟩
  next => exact False.elim typed

end Test.Dogfood.Proofs.QueueWorkersCustody
