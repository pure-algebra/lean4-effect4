import Effect4.Laws.Library.Pull.Scope
import Effect4.Laws.Step.Reading
import Effect4.Laws.Step.Checking
import Effect4.Laws.Step.Waiting
import Effect4.Laws.Program.Denote
import Effect4.Laws.Auto.Semantics

/-!
# Pull protocol selection under the existing denotation

Placement: `pull-protocol-selection`, compatibility, `translation-simulation`, R10.
The plan is `docs/research/2026-10-09-pull-protocol-plan.md`.
The observation is the selected handler's exit and resulting stores.
The premises name source elaboration and an exact Chunk or End answer.
The shared denotation supplies bind, selection and cause matching.
The source consumers are Pull's handlers and Stream's drain.
These laws establish no asynchronous, schedule, host Done, nonempty-batch or whole-stream agreement.
Constructor typing serves `step-language-typed`, `store-typing`, R4.
-/

set_option autoImplicit false
namespace Effect4.Pull
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring Effect4.Modules

/-- The shared batch builder reads the existing protocol value. -/
theorem chunkValue_reads {items : TermSrc} {env : Env} {path : List Nat} {vals xs : List Val}
    (h : Reads items env path vals (.list xs)) :
    Reads (chunkValue items) env path vals (Program.Stream.chunkVal xs) :=
  reads_app (.cons (reads_lit (.str "Chunk") env path vals rfl) (.cons h .nil)) rfl

/-- The shared end builder reads the leftover without changing it. -/
theorem endValue_reads {leftover : TermSrc} {env : Env} {path : List Nat}
    {vals : List Val} {value : Val} (h : Reads leftover env path vals value) :
    Reads (endValue leftover) env path vals (Program.Stream.endVal value) :=
  reads_app (.cons (reads_lit (.str "End") env path vals rfl) (.cons h .nil)) rfl

/-- Chunk construction keeps the element type of its list. -/
theorem chunkValue_types {sig : Signature NativeOp} (atoms : sig.atomOf = nativeAtomTy)
    (constPair : sig.constAtom "pair" = true)
    {items : TermSrc} {env : Env} {path : List Nat} {types : List Ty} {A : Ty}
    (h : TypesEach sig items env path types (.list A)) :
    TypesEach sig (chunkValue items) env path types (.prod (.lit "Chunk") (.list A)) := by
  intro flag
  apply types_app (Ts := [.lit "Chunk", .list A])
  · rw [constPair]
    exact .cons (types_lit (.str "Chunk") true) (.cons (h true) .nil)
  · exact atomOf_native atoms (nativeAtomTy_pair _ _)

/-- End construction keeps the leftover's type. -/
theorem endValue_types {sig : Signature NativeOp} (atoms : sig.atomOf = nativeAtomTy)
    (constPair : sig.constAtom "pair" = true)
    {leftover : TermSrc} {env : Env} {path : List Nat} {types : List Ty} {D : Ty}
    (h : TypesEach sig leftover env path types D) :
    TypesEach sig (endValue leftover) env path types (.prod (.lit "End") D) := by
  intro flag
  apply types_app (Ts := [.lit "End", D])
  · rw [constPair]
    exact .cons (types_lit (.str "End") true) (.cons (h true) .nil)
  · exact atomOf_native atoms (nativeAtomTy_pair _ _)

private theorem matchAnswer_tree {answer : TermSrc} {onSuccess onDone : TermSrc → Src NativeOp}
    {env : Env} {path : List Nat} {term : Term} {success done : NativeEff}
    (read : answer env path = .ok term)
    (hd : onDone (minted (env.mint "payload"))
      (env.push [env.mint "payload"]) (path ++ [0]) = .ok done)
    (hs : onSuccess (app "snd" [minted (env.mint "rest")])
      (env.push [env.mint "rest"]) (path ++ [1]) = .ok success) :
    matchAnswer answer onSuccess onDone env path = .ok (.select term (.tag "End") done success) := by
  change (answer env path >>= fun t =>
    onDone (minted (env.mint "payload")) (env.push [env.mint "payload"]) (path ++ [0]) >>=
      fun d => onSuccess (app "snd" [minted (env.mint "rest")])
        (env.push [env.mint "rest"]) (path ++ [1]) >>= fun s =>
          Except.ok (Eff.select t (.tag "End") d s)) = _
  rw [read, hd, hs]
  rfl

/-- Exact protocol answers choose their stated handler and keep the incoming stores.
The end handler receives the leftover; the batch handler's reader projects its tagged list.
The selected handler's complete meaning, including a failure and changed stores, is retained. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem matchAnswer_meaning {answer : TermSrc} {onSuccess onDone : TermSrc → Src NativeOp}
    {env : Env} {path : List Nat} {vals : List Val} {success done : NativeEff}
    (reply : Except Val (List Val)) (stores : Stores)
    (read : Reads answer env path vals
      (match reply with | .error leftover => Program.Stream.endVal leftover
                        | .ok items => Program.Stream.chunkVal items))
    (hd : onDone (minted (env.mint "payload"))
      (env.push [env.mint "payload"]) (path ++ [0]) = .ok done)
    (hs : onSuccess (app "snd" [minted (env.mint "rest")])
      (env.push [env.mint "rest"]) (path ++ [1]) = .ok success) :
    ∃ tree, matchAnswer answer onSuccess onDone env path = .ok tree ∧
      Denote.meaning tree vals stores =
        match reply with
        | .error leftover => Denote.meaning done (vals ++ [leftover]) stores
        | .ok items => Denote.meaning success (vals ++ [Program.Stream.chunkVal items]) stores := by
  obtain ⟨term, termTree, termValue⟩ := read
  refine ⟨.select term (.tag "End") done success, matchAnswer_tree termTree hd hs, ?_⟩
  cases reply with
  | error leftover =>
    apply Denote.meaning_select_true (bound := some leftover)
    rw [termValue]
    rfl
  | ok items =>
    apply Denote.meaning_select_false (bound := some (Program.Stream.chunkVal items))
    rw [termValue]
    rfl

/-- Completion recovery passes an input failure through with all stores left by the input.
For a success it uses the already compiled answer handler, including its failure result. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem catchDone_meaning {self : Src NativeOp} {onDone : TermSrc → Src NativeOp}
    {env : Env} {path : List Nat} {vals : List Val} {body rest : NativeEff} (stores : Stores)
    (hb : self env (path ++ [0]) = .ok body)
    (hr : matchAnswer (minted (env.mint "answer")) (fun chunk => succeed chunk) onDone
      (env.push [env.mint "answer"]) (path ++ [1]) = .ok rest) :
    ∃ tree, catchDone self onDone env path = .ok tree ∧
      Denote.meaning tree vals stores =
        match Denote.meaning body vals stores with
        | (.success value, after) => Denote.meaning rest (vals ++ [value]) after
        | (.failure cause, after) => (.failure cause, after) := by
  refine ⟨.bind body rest, ?_, Denote.meaning_bind body rest vals stores⟩
  change (self env (path ++ [0]) >>= fun b =>
    matchAnswer (minted (env.mint "answer")) (fun chunk => succeed chunk) onDone
      (env.push [env.mint "answer"]) (path ++ [1]) >>= fun r => Except.ok (Eff.bind b r)) = _
  rw [hb, hr]
  rfl

/-- Cause matching chooses once, on the input's exit, with the input's resulting stores.
No result of the success, completion or failure handler re-enters another handler. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem matchEffect_meaning {self : Src NativeOp} {options : Handlers}
    {env : Env} {path : List Nat} {vals : List Val} {body success failure : NativeEff}
    (stores : Stores) (hb : self env (path ++ [0]) = .ok body)
    (hs : matchAnswer (minted (env.mint "value")) options.onSuccess options.onDone
      (env.push [env.mint "value"]) (path ++ [1]) = .ok success)
    (hf : options.onFailure (minted (env.mint "cause"))
      (env.push [env.mint "cause"]) (path ++ [2]) = .ok failure) :
    ∃ tree, matchEffect self options env path = .ok tree ∧
      Denote.meaning tree vals stores =
        match Denote.meaning body vals stores with
        | (.success value, after) => Denote.meaning success (vals ++ [value]) after
        | (.failure cause, after) => Denote.meaning failure (vals ++ [Val.exitErr cause]) after := by
  refine ⟨.matchCause body success failure, ?_, Denote.meaning_matchCause body success failure vals stores⟩
  change (self env (path ++ [0]) >>= fun b =>
    matchAnswer (minted (env.mint "value")) options.onSuccess options.onDone
      (env.push [env.mint "value"]) (path ++ [1]) >>= fun s =>
        options.onFailure (minted (env.mint "cause"))
          (env.push [env.mint "cause"]) (path ++ [2]) >>= fun f =>
            Except.ok (Eff.matchCause b s f)) = _
  rw [hb, hs, hf]
  rfl

/-- Under an exact input observation, Pull chooses its one protocol handler.
All handlers elaborate at their actual scopes. The selected handler receives the input's
resulting stores; its complete exit and final stores are the result. This is a law of the
existing denotation, not a scheduling or host correspondence theorem. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem matchEffect_protocol {self : Src NativeOp} {options : Handlers}
    {env : Env} {path : List Nat} {vals : List Val} {body success done failure : NativeEff}
    (depth : vals.length = env.names.length)
    (outcome : Exit (Except Val (List Val)) Err Defect FiberId Ann) (stores after : Stores)
    (hb : self env (path ++ [0]) = .ok body)
    (observed : Denote.meaning body vals stores =
      (match outcome with
       | .success (.error leftover) => (.success (Program.Stream.endVal leftover), after)
       | .success (.ok items) => (.success (Program.Stream.chunkVal items), after)
       | .failure cause => (.failure cause, after)))
    (hd : options.onDone (minted ((env.push [env.mint "value"]).mint "payload"))
      ((env.push [env.mint "value"]).push [(env.push [env.mint "value"]).mint "payload"])
      ((path ++ [1]) ++ [0]) = .ok done)
    (hs : options.onSuccess (app "snd" [minted ((env.push [env.mint "value"]).mint "rest")])
      ((env.push [env.mint "value"]).push [(env.push [env.mint "value"]).mint "rest"])
      ((path ++ [1]) ++ [1]) = .ok success)
    (hf : options.onFailure (minted (env.mint "cause"))
      (env.push [env.mint "cause"]) (path ++ [2]) = .ok failure) :
    ∃ tree, matchEffect self options env path = .ok tree ∧
      Denote.meaning tree vals stores =
        match outcome with
        | .success (.error leftover) =>
            Denote.meaning done ((vals ++ [Program.Stream.endVal leftover]) ++ [leftover]) after
        | .success (.ok items) =>
            Denote.meaning success
              ((vals ++ [Program.Stream.chunkVal items]) ++ [Program.Stream.chunkVal items]) after
        | .failure cause => Denote.meaning failure (vals ++ [Val.exitErr cause]) after := by
  cases outcome with
  | success reply =>
    cases reply with
    | error leftover =>
      have read := reads_minted_last depth (path ++ [1]) "value" (Program.Stream.endVal leftover)
      obtain ⟨answerTree, answerSource, chosen⟩ := matchAnswer_meaning (.error leftover) after read hd hs
      obtain ⟨tree, treeSource, result⟩ := matchEffect_meaning stores hb answerSource hf
      refine ⟨tree, treeSource, ?_⟩
      rw [result, observed]
      exact chosen
    | ok items =>
      have read := reads_minted_last depth (path ++ [1]) "value" (Program.Stream.chunkVal items)
      obtain ⟨answerTree, answerSource, chosen⟩ := matchAnswer_meaning (.ok items) after read hd hs
      obtain ⟨tree, treeSource, result⟩ := matchEffect_meaning stores hb answerSource hf
      refine ⟨tree, treeSource, ?_⟩
      rw [result, observed]
      exact chosen
  | failure cause =>
    have answerSource := matchAnswer_tree
      (minted_tree (resolve_last env.names (env.mint "value")) (path ++ [1])) hd hs
    obtain ⟨tree, treeSource, result⟩ := matchEffect_meaning stores hb answerSource hf
    refine ⟨tree, treeSource, ?_⟩
    rw [result, observed]

end Effect4.Pull
