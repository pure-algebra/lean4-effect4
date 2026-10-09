import Effect4.Library.Stream.Ops
import Effect4.Laws.Program.Authoring.Sugar
import Effect4.Laws.Program.Authoring.Loops
import Effect4.Laws.Program.Authoring.Lifts
import Effect4.Laws.Program.Author

set_option autoImplicit false

namespace Effect4.Stream

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Modules

/-- **A source keeps scope**: its open is scoped, and its pull and its close are scoped at every
scoped handle. The form of `Waiter.Scoped`. -/
structure Source.Scoped (src : Source) : Prop where
  opened : src.opened.Scoped
  pull : ∀ h : TermSrc, h.Scoped → (src.pull h).Scoped
  close : ∀ h : TermSrc, h.Scoped → (src.close h).Scoped

/-- A host stream keeps scope, at every scoped request. -/
theorem Source.host_scoped (elem done : Ty) (openRow pullRow closeRow : RowDef) {request : TermSrc}
    (h : request.Scoped) : (Source.host elem done openRow pullRow closeRow request).Scoped :=
  ⟨Row.call_scoped openRow h, fun _ hh => Row.call_scoped pullRow hh,
    fun _ hh => Row.call_scoped closeRow hh⟩

theorem endStep_scoped {acc leftover : TermSrc} (ha : acc.Scoped) (hl : leftover.Scoped) :
    (endStep acc leftover).Scoped :=
  app_scoped "pair" (TermSrc.Scoped_cons ha (TermSrc.Scoped_cons
    (app_scoped "some" (TermSrc.Scoped_cons hl TermSrc.Scoped_nil)) TermSrc.Scoped_nil))

theorem chunkStep_scoped {next : TermSrc} (hn : next.Scoped) : (chunkStep next).Scoped :=
  app_scoped "pair" (TermSrc.Scoped_cons hn (TermSrc.Scoped_cons
    (app_scoped "none" TermSrc.Scoped_nil) TermSrc.Scoped_nil))

/-- The loop of one opened stream keeps scope, where the source and the step do. -/
theorem drain_scoped {src : Source} (hs : src.Scoped) (accTy : Ty) {zero h : TermSrc}
    {gain : TermSrc → TermSrc → Src NativeOp} (hz : zero.Scoped) (hh : h.Scoped)
    (hg : ∀ a c : TermSrc, a.Scoped → c.Scoped → (gain a c).Scoped) :
    (drain src accTy zero h gain).Scoped :=
  iterateWith_scoped
    (app_scoped "pair" (TermSrc.Scoped_cons hz (TermSrc.Scoped_cons
      (app_scoped "none" TermSrc.Scoped_nil) TermSrc.Scoped_nil)))
    (fun _ hc => app_scoped "not" (TermSrc.Scoped_cons
      (app_scoped "isSome" (TermSrc.Scoped_cons
        (app_scoped "snd" (TermSrc.Scoped_cons hc TermSrc.Scoped_nil)) TermSrc.Scoped_nil))
      TermSrc.Scoped_nil))
    (fun _ hc => bindWith_scoped (hs.pull _ hh) fun _ hanswer =>
      selectTagWith_scoped "End" hanswer
        (fun _ hl => succeed_scoped
          (endStep_scoped (app_scoped "fst" (TermSrc.Scoped_cons hc TermSrc.Scoped_nil)) hl))
        (fun _ hchunk => bindWith_scoped
          (hg _ _ (app_scoped "fst" (TermSrc.Scoped_cons hc TermSrc.Scoped_nil))
            (app_scoped "snd" (TermSrc.Scoped_cons hchunk TermSrc.Scoped_nil)))
          fun _ hnext => succeed_scoped (chunkStep_scoped hnext)))
    (fun _ _ _ hnext => hnext)
    (fun _ hc => hc)

/-- Open, drain and close keep scope. -/
theorem runWith_scoped {src : Source} (hs : src.Scoped) (accTy : Ty) {zero : TermSrc}
    {gain : TermSrc → TermSrc → Src NativeOp} (hz : zero.Scoped)
    (hg : ∀ a c : TermSrc, a.Scoped → c.Scoped → (gain a c).Scoped) :
    (runWith src accTy zero gain).Scoped :=
  scope_scoped (bindWith_scoped (acquireWith_scoped hs.opened hs.close) fun _ hh =>
    drain_scoped hs accTy hz hh hg)

/-- **`runCollect` keeps scope**, where its source does. -/
theorem runCollect_scoped {src : Source} (hs : src.Scoped) : (runCollect src).Scoped :=
  bindWith_scoped
    (runWith_scoped hs _ (app_scoped "nil" TermSrc.Scoped_nil) fun _ _ ha hc =>
      succeed_scoped (app_scoped "append" (TermSrc.Scoped_cons ha
        (TermSrc.Scoped_cons hc TermSrc.Scoped_nil))))
    fun _ hlast => succeed_scoped (app_scoped "fst" (TermSrc.Scoped_cons hlast TermSrc.Scoped_nil))

/-- **`runForEach` keeps scope**, where its source and its body do. -/
theorem runForEach_scoped {src : Source} (hs : src.Scoped) {body : TermSrc → Src NativeOp}
    (hb : ∀ item : TermSrc, item.Scoped → (body item).Scoped) : (runForEach src body).Scoped :=
  andThen_scoped
    (runWith_scoped hs .unit unit_scoped fun _ _ _ hc =>
      andThen_scoped (forEachOf_scoped hc hb) (succeed_scoped unit_scoped))
    (succeed_scoped unit_scoped)

end Effect4.Stream
