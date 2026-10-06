import Effect4.Modules.Waiting
import Effect4.Laws.Program.Authoring.Mask
import Effect4.Laws.Program.Authoring.Loops
import Effect4.Laws.Program.Authoring.Records
import Effect4.Laws.Program.Authoring.Tuples
import Effect4.Laws.Modules.Checking
import Effect4.Laws.Auto.Semantics

/-!
# The laws of the shared pieces of a module that waits (decisions rows 221, 238 and 240)

The pieces are `src/Effect4/Modules/Waiting.lean`: the posted helper, the cleanup on
interruption, the wait at the mask's restore site, and the wrapper in its two forms. This file
names no module.

- **Scope.** Each piece keeps the authoring scope judgment (`Src.Scoped`), by one application of
  the lemmas of the lifts that it is made of. A module's part of the wrapper is a `Waiter`, whose
  attempt is a function of its two exits. So the wrapper's law takes the judgment of the attempt
  for every scoped identity, hint and exit (`Waiter.Scoped`).
- **A minted name in a row's scope.** The wrapper binds a request's identity and its hint with
  `bindWith`, and a module's step reads both under the binder of its own row, the name of the
  cell's current value. A name that no later binder of the scope shadows resolves to its own
  level (`resolve_unshadowed`). The row's own binder shadows no name that `bindWith` mints
  (`mint_current_ne_answer`). So such a name is a caller's term of the row's step, for values
  and for types (`captured_answer_in_row`, `capturedTy_answer_in_row`). The premise that no
  later binder shadows the name stays a premise of each statement. The row's own name reads the
  cell's current value (`reads_minted_last`, `types_minted_last`).

Placement. Scope: concept `initial-algebras-folds`, requirement R4, the scope rule of the claim
`operation-data-scoped` and of the lifts' scope laws, at the surface that a module's author
writes. Its consumer is the scope law of each operation of a module that waits: the Queue's
(`src/Effect4/Laws/Modules/Queue/Ops.lean`) first, and Semaphore's next. The minted names:
concept `translation-simulation`, requirement R10, helpers of a module's attempt laws, parts of
the proposed claims `queue-expansion-agrees` and `semaphore-expansion-agrees`. Their consumers
are the `Captured` and `CapturedTy` premises of a module's step statements, at the operation's
own scope. Reach: every scope. The statements establish no behaviour and no run.
-/

set_option autoImplicit false

namespace Effect4.Modules

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring

/-! ## Scope -/

/-- The posted helpers of a list keep scope: the requests and the answer are scoped at the
node, and every binder between is minted. -/
theorem postAll_scoped {requests answer : TermSrc} (h0 : requests.Scoped) (h1 : answer.Scoped) :
    (postAll requests answer).Scoped :=
  iterateWith_scoped (nat_scoped 0)
    (fun _ hi => app_scoped "lt" (TermSrc.Scoped_cons hi
      (TermSrc.Scoped_cons (app_scoped "length" (TermSrc.Scoped_cons h0 TermSrc.Scoped_nil))
        TermSrc.Scoped_nil)))
    (fun _ hi => selectOptionWith_scoped
      (app_scoped "get" (TermSrc.Scoped_cons h0 (TermSrc.Scoped_cons hi TermSrc.Scoped_nil)))
      (succeed_scoped unit_scoped)
      fun _ hrequest => andThen_scoped
        (withFiber_scoped (Action.fork_scoped posted
          (Deferred.succeed_scoped (field_scoped hrequest "hint") h1)))
        (succeed_scoped unit_scoped))
    (fun _ _ hi _ => app_scoped "succ" (TermSrc.Scoped_cons hi TermSrc.Scoped_nil))
    (fun _ hi => hi)

/-- The cleanup on interruption keeps scope, at every alphabet: the exit's name is minted. -/
theorem onInterrupt_scoped {Op : Type} [ScopedOp Op] {body cleanup : Src Op} (h0 : body.Scoped)
    (h1 : cleanup.Scoped) : (onInterrupt body cleanup).Scoped :=
  onExitWith_scoped h0 fun _ hexit =>
    ifElse_scoped (app_scoped "causeIsInterrupt" (TermSrc.Scoped_cons hexit TermSrc.Scoped_nil))
      h1 (succeed_scoped unit_scoped)

/-- The wait keeps scope, for every restore function that keeps it. -/
theorem waitAt_scoped {restore : Src NativeOp → Src NativeOp} {hint : TermSrc}
    {withdraw : Src NativeOp}
    (hrestore : ∀ e : Src NativeOp, e.Scoped → (restore e).Scoped) (hhint : hint.Scoped)
    (hwithdraw : withdraw.Scoped) : (waitAt restore hint withdraw).Scoped :=
  onInterrupt_scoped (hrestore _ (Deferred.await_scoped hhint)) hwithdraw

/-- **A module's part of the wrapper keeps scope**: its attempt for every scoped identity, hint
and pair of exits, and its withdrawal for every scoped identity. -/
structure Waiter.Scoped (w : Waiter) : Prop where
  attempt : ∀ (id hint : TermSrc) (wait : Src NativeOp) (done : TermSrc → Src NativeOp),
    id.Scoped → hint.Scoped → wait.Scoped → (∀ answer : TermSrc, answer.Scoped →
      (done answer).Scoped) → (w.attempt id hint wait done).Scoped
  withdraw : ∀ id : TermSrc, id.Scoped → (w.withdraw id).Scoped

/-- **The wrapper keeps scope**, where the module's part does: the mask's saved state, the
identity, the loop's two names, the hint and the result are minted. -/
theorem waitRetry_scoped (result : Ty) (ended : String) {w : Waiter} (h : w.Scoped) :
    (waitRetry result ended w).Scoped :=
  uninterruptibleMaskWith_scoped fun _ hrestore =>
    bindWith_scoped (Deferred.make_scoped .unit .never) fun _ hid =>
      bindWith_scoped
        (iterateWith_scoped (app_scoped "none" TermSrc.Scoped_nil)
          (fun _ hcursor => app_scoped "not" (TermSrc.Scoped_cons
            (app_scoped "isSome" (TermSrc.Scoped_cons hcursor TermSrc.Scoped_nil))
            TermSrc.Scoped_nil))
          (fun _ _ => bindWith_scoped (Deferred.make_scoped w.hint .never) fun _ hhint =>
            h.attempt _ _ _ _ hid hhint
              (andThen_scoped (waitAt_scoped hrestore hhint (h.withdraw _ hid))
                (succeed_scoped (app_scoped "none" TermSrc.Scoped_nil)))
              fun _ hanswer => succeed_scoped
                (app_scoped "some" (TermSrc.Scoped_cons hanswer TermSrc.Scoped_nil)))
          (fun _ _ _ hanswer => hanswer)
          (fun _ hcursor => hcursor))
        fun _ hlast => selectOptionWith_scoped hlast
          (failCause_scoped (Cause.die_scoped (str_scoped ended)))
          fun _ hanswer => succeed_scoped hanswer

/-- **The wrapper with no loop keeps scope**, where the module's part does. -/
theorem waitAnswer_scoped {w : Waiter} (h : w.Scoped) : (waitAnswer w).Scoped :=
  uninterruptibleMaskWith_scoped fun _ hrestore =>
    bindWith_scoped (Deferred.make_scoped .unit .never) fun _ hid =>
      bindWith_scoped (Deferred.make_scoped w.hint .never) fun _ hhint =>
        h.attempt _ _ _ _ hid hhint (waitAt_scoped hrestore hhint (h.withdraw _ hid))
          fun _ hanswer => succeed_scoped hanswer

/-! ## A minted name in a row's scope

A wrapper binds a request's identity and its hint with `bindWith`. A module's step is the term of
one `Ref.modifyWith`, so it reads both names under one more binder: the minted name of the cell's
current value. The lemmas below give each reading, from two premises on the scope: the name is
bound there, and no later binder shadows it. -/

/-- A name keeps its level under later binders of other names. -/
theorem resolve_append_free {names : Names} {x : String} {i : Nat}
    (bound : Names.resolve names x = some i) :
    ∀ more : Names, (∀ y ∈ more, y ≠ x) → Names.resolve (names ++ more) x = some i := by
  intro more
  induction more generalizing names with
  | nil =>
    intro _
    rw [List.append_nil]
    exact bound
  | cons y more ih =>
    intro free
    have split : names ++ y :: more = (names ++ [y]) ++ more := by
      rw [List.append_assoc]
      rfl
    rw [split]
    exact ih ((Names.resolve_append_ne (free y List.mem_cons_self) names).trans bound)
      fun z member => free z (List.mem_cons_of_mem y member)

/-- **A name that no later binder shadows resolves to its own level.** -/
theorem resolve_unshadowed (before : Names) (x : String) (later : Names)
    (free : ∀ y ∈ later, y ≠ x) :
    Names.resolve (before ++ x :: later) x = some before.length := by
  have split : before ++ x :: later = (before ++ [x]) ++ later := by
    rw [List.append_assoc]
    rfl
  rw [split]
  exact resolve_append_free (resolve_last before x) later free

/-- **Two minted names whose stems begin with two bytes are two names**, at any two scopes. A
minted name is the reserved prefix, the stem and the depth's digits, so the two names differ at
their third byte. It relates no two stems that begin alike: `mint_depth_inj` has one stem at two
depths. -/
theorem mint_ne_of_head {stem other : String} {b c : UInt8}
    (head : stem.toByteArray.data.toList.head? = some b)
    (otherHead : other.toByteArray.data.toList.head? = some c) (ne : b ≠ c) (env outer : Env) :
    env.mint stem ≠ outer.mint other := by
  obtain ⟨rest, stemBytes⟩ := List.head?_eq_some_iff.mp head
  obtain ⟨tail, otherBytes⟩ := List.head?_eq_some_iff.mp otherHead
  intro same
  unfold Env.mint reservedPrefix at same
  have bytes := congrArg (fun s : String => s.toByteArray.data.toList) same
  simp only [String.toByteArray_append, ByteArray.data_append, Array.toList_append] at bytes
  have prefixBytes : ("_%" : String).toByteArray.data.toList = [95, 37] := by decide
  rw [prefixBytes, stemBytes, otherBytes] at bytes
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at bytes
  exact ne bytes.2.2.1

/-- The name of a row's current value is no name that `bindWith` mints, at any two scopes. So a
row's own binder shadows no identity and no hint. -/
theorem mint_current_ne_answer (env outer : Env) : env.mint "current" ≠ outer.mint "answer" :=
  mint_ne_of_head (b := 99) (c := 97) (by decide) (by decide) (by decide) env outer

/-- **A later minted binder shadows no name that `bindWith` minted before it**, where the later
binder's stem is `answer` itself or begins with another byte. A later `answer` is minted at a
deeper scope, so it ends in other digits (`mint_depth_inj`). Any other stem of the surface
begins with another byte: `cursor`, `exit`, `payload`, `restore` and `current`. This discharges
the premise that no later binder shadows a request's identity or its hint, at a wrapper's own
binders. -/
theorem later_mint_ne_answer {outer env : Env} {stem : String} {b : UInt8}
    (deeper : outer.names.length < env.names.length)
    (head : stem.toByteArray.data.toList.head? = some b)
    (apart : stem = "answer" ∨ b ≠ 97) : env.mint stem ≠ outer.mint "answer" := by
  rcases apart with rfl | other
  · intro same
    exact absurd (mint_depth_inj same) (Nat.ne_of_gt deeper)
  · exact mint_ne_of_head (c := 97) head (by decide) other env outer

/-- A scope with one more minted name is one level deeper: one more value, or one more type. -/
theorem push_minted_length {α : Type} {env : Env} {xs : List α}
    (depth : xs.length = env.names.length) (stem : String) (x : α) :
    (xs ++ [x]).length = (env.push [env.mint stem]).names.length := by
  simp only [Env.push_length, List.length_append, List.length_cons, List.length_nil, depth]

/-- **A name that a builder mints and binds reads the value that it binds**, the last of its
scope: the cell's current value under a row's binder, and a bound answer under `bindWith`'s. -/
theorem reads_minted_last {env : Env} {captured : List Val}
    (depth : captured.length = env.names.length) (path : List Nat) (stem : String) (v : Val) :
    Reads (minted (env.mint stem)) (env.push [env.mint stem]) path (captured ++ [v]) v := by
  refine ⟨.var env.names.length, minted_tree (resolve_last env.names _) path, ?_⟩
  show (captured ++ [v])[env.names.length]? = some v
  rw [← depth, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

/-- The typed twin: the name has the type that its binder gives it, the last of its scope. -/
theorem types_minted_last {Op : Type} {sig : Signature Op} {env : Env} {tys : List Ty}
    (depth : tys.length = env.names.length) (path : List Nat) (stem : String) (T : Ty) :
    TypesEach sig (minted (env.mint stem)) (env.push [env.mint stem]) path (tys ++ [T]) T := by
  refine types_minted (resolve_last env.names _) ?_
  rw [← depth, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

/-- A name that `bindWith` mints, bound in a row's scope with no later binder that shadows it,
resolves to its own level under the row's own binder too. -/
theorem resolve_answer_in_row {outer env : Env} {before later : Names}
    (scope : env.names = before ++ outer.mint "answer" :: later)
    (unshadowed : ∀ name ∈ later, name ≠ outer.mint "answer") :
    (env.push [env.mint "current"]).names.resolve (outer.mint "answer") = some before.length := by
  have pushed : (env.push [env.mint "current"]).names =
      before ++ outer.mint "answer" :: (later ++ [env.mint "current"]) := by
    show env.names ++ [env.mint "current"] = _
    rw [scope, List.append_assoc]
    rfl
  rw [pushed]
  refine resolve_unshadowed before _ _ fun name member => ?_
  rcases List.mem_append.mp member with earlier | last
  · exact unshadowed name earlier
  · rw [List.mem_singleton.mp last]
    exact mint_current_ne_answer env outer

/-- **A name that `bindWith` mints is a caller's term of a row's step**, where the row's scope
binds it and no later binder shadows it. It reads the value at its level under the row's own
binder, and under the two binders that a fold of the step mints. -/
theorem captured_answer_in_row {outer env : Env} {path : List Nat} {captured : List Val}
    {before later : Names} {v cell : Val}
    (scope : env.names = before ++ outer.mint "answer" :: later)
    (unshadowed : ∀ name ∈ later, name ≠ outer.mint "answer")
    (held : captured[before.length]? = some v) :
    Captured (minted (outer.mint "answer")) (env.push [env.mint "current"]) path
      (captured ++ [cell]) v := by
  refine captured_answer (resolve_answer_in_row scope unshadowed) ?_
  obtain ⟨inside, -⟩ := List.getElem?_eq_some_iff.mp held
  rw [List.getElem?_append_left inside]
  exact held

/-- **The typed twin**: the name has the type at its level under the row's own binder, and under
a fold's two binders. -/
theorem capturedTy_answer_in_row {Op : Type} {sig : Signature Op} {outer env : Env}
    {path : List Nat} {tys : List Ty} {before later : Names} {T C : Ty}
    (scope : env.names = before ++ outer.mint "answer" :: later)
    (unshadowed : ∀ name ∈ later, name ≠ outer.mint "answer")
    (held : tys[before.length]? = some T) :
    CapturedTy sig (minted (outer.mint "answer")) (env.push [env.mint "current"]) path
      (tys ++ [C]) T := by
  refine capturedTy_answer (resolve_answer_in_row scope unshadowed) ?_
  obtain ⟨inside, -⟩ := List.getElem?_eq_some_iff.mp held
  rw [List.getElem?_append_left inside]
  exact held

end Effect4.Modules
