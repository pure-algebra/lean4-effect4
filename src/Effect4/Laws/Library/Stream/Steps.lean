import Effect4.Laws.Library.Stream.Model
import Effect4.Library.Stream.Steps
import Effect4.Laws.Step.Reading

set_option autoImplicit false

namespace Effect4.Stream

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Modules

variable {env : Env} {path : List Nat} {vals : List Val}

/-- **The end step agrees with the model**: it reads the value of the finished cursor. -/
theorem endStep_agrees {acc leftover : TermSrc} (c : Cursor) (l : Val)
    (hacc : Reads acc env path vals c.acc) (hl : Reads leftover env path vals l) :
    Reads (endStep acc leftover) env path vals (c.finish l).val :=
  reads_app (.cons hacc (.cons (reads_some hl) .nil)) (atom_pair c.acc (Store.Val.some l))

/-- **The chunk step agrees with the model**: it reads the value of the cursor that goes on. -/
theorem chunkStep_agrees {next : TermSrc} (n : Val) (hn : Reads next env path vals n) :
    Reads (chunkStep next) env path vals (Cursor.gain n).val :=
  reads_app (.cons hn (.cons reads_noneT .nil)) (atom_pair n Store.Val.none)

/-- **The test of the loop reads the model's `live`.** -/
theorem live_agrees {cursor : TermSrc} (c : Cursor)
    (hc : Reads cursor env path vals c.val) :
    Reads (notT (app "isSome" [app "snd" [cursor]])) env path vals (Val.bool c.live) := by
  have hsnd : Reads (app "snd" [cursor]) env path vals
      (match c.ended with | none => Store.Val.none | some l => Store.Val.some l) :=
    reads_app (.cons hc .nil) rfl
  cases hended : c.ended with
  | none =>
    rw [hended] at hsnd
    have h := reads_notT (reads_app (.cons hsnd .nil)
      (show nativeAtom "isSome" [Store.Val.none] = some (Val.bool false) from rfl))
    simpa only [Cursor.live, hended, Option.isNone_none, Bool.not_false] using h
  | some l =>
    rw [hended] at hsnd
    have h := reads_notT (reads_app (.cons hsnd .nil)
      (show nativeAtom "isSome" [Store.Val.some l] = some (Val.bool true) from rfl))
    simpa only [Cursor.live, hended, Option.isNone_some, Bool.not_true] using h

end Effect4.Stream
