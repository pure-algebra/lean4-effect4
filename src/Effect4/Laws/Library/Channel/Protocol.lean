import Effect4.Laws.Library.Channel.Scope
import Effect4.Laws.Library.Pull.Protocol

/-!
# Channel selection under the existing denotation

Placement: channel-batch-transform and channel-completion-transform, compatibility, translation-simulation, R10.
The plan is docs/research/2026-10-09-channel-transforms-plan.md.
The observation is the selected handler's complete exit and resulting stores.
The premises give an exact input observation and elaboration at every actual handler scope.
Consumers are the Channel operations and declaration-backed Stream transformations.
The inline dispatchers make the selection law usable without a stored-call assumption.
Applying these laws to stored entries remains conditional: Denote.meaning does not execute stored calls.
No asynchronous scheduling, nonempty-output admission, whole-stream or host simulation is established.
-/

set_option autoImplicit false
namespace Effect4.Channel
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring Effect4.Modules

private theorem bindAnswer_protocol {self : Src NativeOp}
    {onSuccess onDone : TermSrc → Src NativeOp}
    {env : Env} {path : List Nat} {vals : List Val} {body success done : NativeEff}
    (depth : vals.length = env.names.length)
    (outcome : Exit (Except Val (List Val)) Err Defect FiberId Ann) (stores after : Stores)
    (hb : self env (path ++ [0]) = .ok body)
    (observed : Denote.meaning body vals stores =
      (match outcome with
       | .success (.error leftover) => (.success (Program.Stream.endVal leftover), after)
       | .success (.ok items) => (.success (Program.Stream.chunkVal items), after)
       | .failure cause => (.failure cause, after)))
    (hd : onDone (minted ((env.push [env.mint "answer"]).mint "payload"))
      ((env.push [env.mint "answer"]).push [(env.push [env.mint "answer"]).mint "payload"])
      ((path ++ [1]) ++ [0]) = .ok done)
    (hs : onSuccess (app "snd" [minted ((env.push [env.mint "answer"]).mint "rest")])
      ((env.push [env.mint "answer"]).push [(env.push [env.mint "answer"]).mint "rest"])
      ((path ++ [1]) ++ [1]) = .ok success) :
    ∃ tree,
      (bindWith self fun answer => Pull.matchAnswer answer onSuccess onDone) env path = .ok tree ∧
      Denote.meaning tree vals stores =
        match outcome with
        | .success (.error leftover) =>
            Denote.meaning done ((vals ++ [Program.Stream.endVal leftover]) ++ [leftover]) after
        | .success (.ok items) =>
            Denote.meaning success
              ((vals ++ [Program.Stream.chunkVal items]) ++ [Program.Stream.chunkVal items]) after
        | .failure cause => (.failure cause, after) := by
  have read := reads_minted_last depth (path ++ [1]) "answer" (Program.Stream.endVal .unit)
  obtain ⟨rest, restSource, _⟩ := Pull.matchAnswer_meaning (.error .unit) stores read hd hs
  have selected (reply : Except Val (List Val)) :
      Denote.meaning rest
        (vals ++ [match reply with
          | .error leftover => Program.Stream.endVal leftover
          | .ok items => Program.Stream.chunkVal items]) after =
        match reply with
        | .error leftover =>
            Denote.meaning done ((vals ++ [Program.Stream.endVal leftover]) ++ [leftover]) after
        | .ok items =>
            Denote.meaning success
              ((vals ++ [Program.Stream.chunkVal items]) ++ [Program.Stream.chunkVal items]) after := by
    have readReply := reads_minted_last depth (path ++ [1]) "answer"
      (match reply with
       | .error leftover => Program.Stream.endVal leftover
       | .ok items => Program.Stream.chunkVal items)
    obtain ⟨other, otherSource, chosen⟩ := Pull.matchAnswer_meaning reply after readReply hd hs
    have same : rest = other := Except.ok.inj (restSource.symm.trans otherSource)
    rw [same]
    cases reply <;> exact chosen
  refine ⟨.bind body rest, ?_, ?_⟩
  · change (self env (path ++ [0]) >>= fun b =>
      Pull.matchAnswer (minted (env.mint "answer")) onSuccess onDone
        (env.push [env.mint "answer"]) (path ++ [1]) >>= fun r =>
          Except.ok (Eff.bind b r)) = _
    rw [hb, restSource]
    rfl
  · rw [Denote.meaning_bind, observed]
    cases outcome with
    | success reply =>
      cases reply with
      | error leftover => exact selected (.error leftover)
      | ok items => exact selected (.ok items)
    | failure cause => rfl

/-- Batch mapping selects the wrapped transformation only for Chunk.
End retains its leftover; an input failure retains its cause and resulting stores.
The selected handler's full meaning retains a transformation failure and its stores. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem Internal.mapEffectOf_protocol {self : Src NativeOp} {transform : TermSrc → Src NativeOp}
    {env : Env} {path : List Nat} {vals : List Val} {body success done : NativeEff}
    (depth : vals.length = env.names.length)
    (outcome : Exit (Except Val (List Val)) Err Defect FiberId Ann) (stores after : Stores)
    (hb : self env (path ++ [0]) = .ok body)
    (observed : Denote.meaning body vals stores =
      (match outcome with
       | .success (.error leftover) => (.success (Program.Stream.endVal leftover), after)
       | .success (.ok items) => (.success (Program.Stream.chunkVal items), after)
       | .failure cause => (.failure cause, after)))
    (hd : succeed (Pull.endValue (minted ((env.push [env.mint "answer"]).mint "payload")))
      ((env.push [env.mint "answer"]).push [(env.push [env.mint "answer"]).mint "payload"])
      ((path ++ [1]) ++ [0]) = .ok done)
    (hs : (bindWith
      (transform (app "snd" [minted ((env.push [env.mint "answer"]).mint "rest")]))
      fun mapped => succeed (Pull.chunkValue mapped))
      ((env.push [env.mint "answer"]).push [(env.push [env.mint "answer"]).mint "rest"])
      ((path ++ [1]) ++ [1]) = .ok success) :
    ∃ tree, Internal.mapEffectOf self transform env path = .ok tree ∧
      Denote.meaning tree vals stores =
        match outcome with
        | .success (.error leftover) =>
            Denote.meaning done ((vals ++ [Program.Stream.endVal leftover]) ++ [leftover]) after
        | .success (.ok items) =>
            Denote.meaning success
              ((vals ++ [Program.Stream.chunkVal items]) ++ [Program.Stream.chunkVal items]) after
        | .failure cause => (.failure cause, after) :=
  bindAnswer_protocol depth outcome stores after hb observed hd hs

/-- Completion mapping selects the wrapped transformation only for End.
Chunk retains its batch; input failures and selected-handler failures keep their stores. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem Internal.mapDoneEffectOf_protocol {self : Src NativeOp} {transform : TermSrc → Src NativeOp}
    {env : Env} {path : List Nat} {vals : List Val} {body success done : NativeEff}
    (depth : vals.length = env.names.length)
    (outcome : Exit (Except Val (List Val)) Err Defect FiberId Ann) (stores after : Stores)
    (hb : self env (path ++ [0]) = .ok body)
    (observed : Denote.meaning body vals stores =
      (match outcome with
       | .success (.error leftover) => (.success (Program.Stream.endVal leftover), after)
       | .success (.ok items) => (.success (Program.Stream.chunkVal items), after)
       | .failure cause => (.failure cause, after)))
    (hd : (bindWith
      (transform (minted ((env.push [env.mint "answer"]).mint "payload")))
      fun mapped => succeed (Pull.endValue mapped))
      ((env.push [env.mint "answer"]).push [(env.push [env.mint "answer"]).mint "payload"])
      ((path ++ [1]) ++ [0]) = .ok done)
    (hs : succeed (Pull.chunkValue
      (app "snd" [minted ((env.push [env.mint "answer"]).mint "rest")]))
      ((env.push [env.mint "answer"]).push [(env.push [env.mint "answer"]).mint "rest"])
      ((path ++ [1]) ++ [1]) = .ok success) :
    ∃ tree, Internal.mapDoneEffectOf self transform env path = .ok tree ∧
      Denote.meaning tree vals stores =
        match outcome with
        | .success (.error leftover) =>
            Denote.meaning done ((vals ++ [Program.Stream.endVal leftover]) ++ [leftover]) after
        | .success (.ok items) =>
            Denote.meaning success
              ((vals ++ [Program.Stream.chunkVal items]) ++ [Program.Stream.chunkVal items]) after
        | .failure cause => (.failure cause, after) :=
  bindAnswer_protocol depth outcome stores after hb observed hd hs

end Effect4.Channel
