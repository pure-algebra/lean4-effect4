import Effect4.Laws.Program.Authoring.Lifts
import Effect4.Program.Authoring.Sugar

/-!
# Laws.Program.Authoring.Sugar — the hand-written surface preserves scope

`Program/Authoring/Sugar.lean` is the only hand-written part of the authoring surface (the
binders over a fresh name and the Effect spellings of the native rows, until the row
generator exists, DI-89). Each definition gets the same lemma the generated lifts carry,
named so `authoring_scoped` finds it, and each is one application of the lemmas of the
lifts it is made of. `elaborate_scoped` is the consequence for authors: a program that
elaborates is closed at level `0`.
-/

set_option autoImplicit false

namespace Effect4.Program.Authoring

open Effect4.Program

theorem bindWith_scoped {Op : Type} {first : Src Op} {rest : TermSrc → Src Op}
    (h0 : first.Scoped) (h1 : ∀ r : TermSrc, r.Scoped → (rest r).Scoped) :
    (bindWith first rest).Scoped :=
  ⟨fun env p e h => (bind_scoped _ h0 (h1 _ (var_scoped _))).holds env p e h⟩

theorem flatMap_scoped {Op : Type} (answer : String) {first rest : Src Op}
    (h0 : first.Scoped) (h1 : rest.Scoped) : (flatMap answer first rest).Scoped :=
  bind_scoped answer h0 h1

theorem andThen_scoped {Op : Type} {first rest : Src Op} (h0 : first.Scoped) (h1 : rest.Scoped) :
    (andThen first rest).Scoped :=
  bind_scoped _ h0 h1

theorem map_scoped {Op : Type} (atom : String) {effect : Src Op} (h : effect.Scoped) :
    (map atom effect).Scoped :=
  bindWith_scoped h fun _ hr =>
    succeed_scoped (app_scoped atom (TermSrc.Scoped_cons hr TermSrc.Scoped_nil))

theorem ifElse_scoped {Op : Type} {test : TermSrc} {thenB elseB : Src Op}
    (h0 : test.Scoped) (h1 : thenB.Scoped) (h2 : elseB.Scoped) :
    (ifElse test thenB elseB).Scoped :=
  branch_scoped h0 h1 h2

/-- A pair request is the `pair` atom on two scoped terms. -/
theorem pair_scoped {a b : TermSrc} (h0 : a.Scoped) (h1 : b.Scoped) :
    (app "pair" [a, b]).Scoped :=
  app_scoped "pair" (TermSrc.Scoped_cons h0 (TermSrc.Scoped_cons h1 TermSrc.Scoped_nil))

namespace Ref

theorem make_scoped {value : TermSrc} (h : value.Scoped) : (Ref.make value).Scoped :=
  perform_scoped _ h
theorem get_scoped {ref : TermSrc} (h : ref.Scoped) : (Ref.get ref).Scoped :=
  perform_scoped _ h
theorem set_scoped {ref value : TermSrc} (h0 : ref.Scoped) (h1 : value.Scoped) :
    (Ref.set ref value).Scoped :=
  perform_scoped _ (pair_scoped h0 h1)
theorem getAndSet_scoped {ref value : TermSrc} (h0 : ref.Scoped) (h1 : value.Scoped) :
    (Ref.getAndSet ref value).Scoped :=
  perform_scoped _ (pair_scoped h0 h1)
theorem setAndGet_scoped {ref value : TermSrc} (h0 : ref.Scoped) (h1 : value.Scoped) :
    (Ref.setAndGet ref value).Scoped :=
  perform_scoped _ (pair_scoped h0 h1)
theorem update_scoped (f : Effect4.Machine.FnName) {ref : TermSrc} (h : ref.Scoped) :
    (Ref.update f ref).Scoped :=
  perform_scoped _ h
theorem getAndUpdate_scoped (f : Effect4.Machine.FnName) {ref : TermSrc} (h : ref.Scoped) :
    (Ref.getAndUpdate f ref).Scoped :=
  perform_scoped _ h
theorem updateAndGet_scoped (f : Effect4.Machine.FnName) {ref : TermSrc} (h : ref.Scoped) :
    (Ref.updateAndGet f ref).Scoped :=
  perform_scoped _ h
theorem modify_scoped (f : Effect4.Machine.FnName) {ref : TermSrc} (h : ref.Scoped) :
    (Ref.modify f ref).Scoped :=
  perform_scoped _ h

end Ref

namespace Deferred

theorem make_scoped : Deferred.make.Scoped := perform_scoped _ unit_scoped
theorem isDone_scoped {deferred : TermSrc} (h : deferred.Scoped) : (Deferred.isDone deferred).Scoped :=
  perform_scoped _ h
theorem poll_scoped {deferred : TermSrc} (h : deferred.Scoped) : (Deferred.poll deferred).Scoped :=
  perform_scoped _ h
theorem await_scoped {deferred : TermSrc} (h : deferred.Scoped) : (Deferred.await deferred).Scoped :=
  perform_scoped _ h
theorem succeed_scoped {deferred value : TermSrc} (h0 : deferred.Scoped) (h1 : value.Scoped) :
    (Deferred.succeed deferred value).Scoped :=
  perform_scoped _ (pair_scoped h0 h1)
theorem fail_scoped {deferred error : TermSrc} (h0 : deferred.Scoped) (h1 : error.Scoped) :
    (Deferred.fail deferred error).Scoped :=
  perform_scoped _ (pair_scoped h0 h1)

end Deferred

/-- Scope safety by construction: a program that elaborates is closed at level `0`. -/
theorem elaborate_scoped {Op : Type} {src : Src Op} (h : src.Scoped) {e : Eff Op}
    (he : elaborate src = .ok e) : Eff.scopedAt 0 e = true :=
  h.holds {} [] e he

end Effect4.Program.Authoring
