import Effect4.Modules.Waiting
import Effect4.Laws.Program.Authoring.Mask
import Effect4.Laws.Program.Authoring.Loops
import Effect4.Laws.Program.Authoring.Records
import Effect4.Laws.Program.Authoring.Tuples
import Effect4.Laws.Modules.Checking
import Effect4.Laws.Program.Typing.Sound
import Effect4.Laws.Codegen.Mask
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
- **The row's own name under a fold, and a loop's cursor in a row.** A step may hold the cell's
  own source in a fold's body, and a helper's loop may hand its cursor to a step. The row's own
  name is a caller's term under the step's folds (`captured_current`, `capturedTy_current`). A
  loop's cursor is a caller's term of a row's step (`captured_cursor_in_row`,
  `capturedTy_cursor_in_row`): the row's own binder has another name (`mint_current_ne_cursor`).

- **Typing at every scope.** The last part of the file holds the judgment of a program that
  answers a type (`Answers`), a term that keeps its type under the surface's binders (`Kept`),
  what each builder and each row of a cell answers, and the typing of the shared pieces. Its
  own header states its placement and its reach.

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

/-- **The loop at a caller's restore keeps scope**, where the module's part does and the caller's
restore function keeps it: the identity, the loop's two names, the hint and the result are
minted. -/
theorem waitRetryAt_scoped {restore : Src NativeOp → Src NativeOp} (result : Ty)
    (ended : String) {w : Waiter}
    (hrestore : ∀ e : Src NativeOp, e.Scoped → (restore e).Scoped) (h : w.Scoped) :
    (waitRetryAt restore result ended w).Scoped :=
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

/-- **The wrapper keeps scope**, where the module's part does: the mask's saved state is minted,
and the loop keeps scope at the mask's own restore. -/
theorem waitRetry_scoped (result : Ty) (ended : String) {w : Waiter} (h : w.Scoped) :
    (waitRetry result ended w).Scoped :=
  uninterruptibleMaskWith_scoped fun _ hrestore => waitRetryAt_scoped result ended hrestore h

/-- **The wrapper with no loop keeps scope**, where the module's part does. -/
theorem waitAnswer_scoped {w : Waiter} (h : w.Scoped) : (waitAnswer w).Scoped :=
  uninterruptibleMaskWith_scoped fun _ hrestore =>
    bindWith_scoped (Deferred.make_scoped .unit .never) fun _ hid =>
      bindWith_scoped (Deferred.make_scoped w.hint .never) fun _ hhint =>
        h.attempt _ _ _ _ hid hhint (waitAt_scoped hrestore hhint (h.withdraw _ hid))
          fun _ hanswer => succeed_scoped hanswer

/-- **The protected body keeps scope**, where its three parts do: the acquisition for every
restore function that keeps scope, and the release and the body for every scoped acquired value.
The mask's saved state, the acquired value and the body's exit are minted. -/
theorem protectedBy_scoped {acquire : (Src NativeOp → Src NativeOp) → Src NativeOp}
    {release body : TermSrc → Src NativeOp}
    (hacquire : ∀ restore : Src NativeOp → Src NativeOp,
      (∀ e : Src NativeOp, e.Scoped → (restore e).Scoped) → (acquire restore).Scoped)
    (hrelease : ∀ got : TermSrc, got.Scoped → (release got).Scoped)
    (hbody : ∀ got : TermSrc, got.Scoped → (body got).Scoped) :
    (protectedBy acquire release body).Scoped :=
  uninterruptibleMaskWith_scoped fun _ hrestore =>
    bindWith_scoped (hacquire _ hrestore) fun _ hgot =>
      onExitWith_scoped (hrestore _ (hbody _ hgot)) fun _ _ => hrelease _ hgot

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

/-! ## A minted name of any stem in a row's scope, the row's own name, and a loop's cursor

A step may hold the cell's own source in a fold's body: Semaphore's visit reads the free count
there. A helper's loop may hand its cursor to a step: the walk of a release hands each visit its
cursor. The lemmas below give each reading. The first three state the rule of a row's scope for
a minted name of any stem, with the three facts on names as premises. -/

/-- A name of a row's scope resolves to its own level under the row's own binder too, where no
later binder shadows it and the row's own binder has another name. -/
theorem resolve_minted_in_row {name : String} {env : Env} {before later : Names}
    (scope : env.names = before ++ name :: later)
    (unshadowed : ∀ other ∈ later, other ≠ name) (notCurrent : env.mint "current" ≠ name) :
    (env.push [env.mint "current"]).names.resolve name = some before.length := by
  have pushed : (env.push [env.mint "current"]).names =
      before ++ name :: (later ++ [env.mint "current"]) := by
    show env.names ++ [env.mint "current"] = _
    rw [scope, List.append_assoc]
    rfl
  rw [pushed]
  refine resolve_unshadowed before _ _ fun other member => ?_
  rcases List.mem_append.mp member with earlier | last
  · exact unshadowed other earlier
  · rw [List.mem_singleton.mp last]
    exact notCurrent

/-- **A minted name of a row's scope is a caller's term of the row's step**, where no later
binder shadows it, and neither the row's own binder nor a fold's two binders have its name. It
reads the value at its level under the row's own binder, and under a fold's two binders. -/
theorem captured_minted_in_row {name : String} {env : Env} {path : List Nat}
    {captured : List Val} {before later : Names} {v cell : Val}
    (scope : env.names = before ++ name :: later)
    (unshadowed : ∀ other ∈ later, other ≠ name) (notCurrent : env.mint "current" ≠ name)
    (notAcc : (env.push [env.mint "current"]).mint "acc" ≠ name)
    (notItem : (env.push [env.mint "current"]).mint "item" ≠ name)
    (held : captured[before.length]? = some v) :
    Captured (minted name) (env.push [env.mint "current"]) path (captured ++ [cell]) v := by
  refine captured_minted (resolve_minted_in_row scope unshadowed notCurrent) ?_ notAcc notItem
  obtain ⟨inside, -⟩ := List.getElem?_eq_some_iff.mp held
  rw [List.getElem?_append_left inside]
  exact held

/-- **The typed twin**: the name has the type at its level under the row's own binder, and under
a fold's two binders. -/
theorem capturedTy_minted_in_row {Op : Type} {sig : Signature Op} {name : String} {env : Env}
    {path : List Nat} {tys : List Ty} {before later : Names} {T C : Ty}
    (scope : env.names = before ++ name :: later)
    (unshadowed : ∀ other ∈ later, other ≠ name) (notCurrent : env.mint "current" ≠ name)
    (notAcc : (env.push [env.mint "current"]).mint "acc" ≠ name)
    (notItem : (env.push [env.mint "current"]).mint "item" ≠ name)
    (held : tys[before.length]? = some T) :
    CapturedTy sig (minted name) (env.push [env.mint "current"]) path (tys ++ [C]) T := by
  refine capturedTy_minted (resolve_minted_in_row scope unshadowed notCurrent) ?_ notAcc notItem
  obtain ⟨inside, -⟩ := List.getElem?_eq_some_iff.mp held
  rw [List.getElem?_append_left inside]
  exact held

/-- The name of a row's current value is no name that a loop mints for its cursor, at any two
scopes. The two stems agree in three bytes and differ at the fourth, so `mint_ne_of_head` does
not tell them apart. -/
theorem mint_current_ne_cursor (env outer : Env) : env.mint "current" ≠ outer.mint "cursor" := by
  intro same
  unfold Env.mint reservedPrefix at same
  have bytes := congrArg (fun s : String => s.toByteArray.data.toList) same
  simp only [String.toByteArray_append, ByteArray.data_append, Array.toList_append] at bytes
  have h1 : ("_%" : String).toByteArray.data.toList = [95, 37] := by decide
  have h2 : ("current" : String).toByteArray.data.toList = [99, 117, 114, 114, 101, 110, 116] := by
    decide
  have h3 : ("cursor" : String).toByteArray.data.toList = [99, 117, 114, 115, 111, 114] := by
    decide
  rw [h1, h2, h3] at bytes
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at bytes
  exact absurd bytes.2.2.2.2.2.1 (by decide)

/-- **A loop's cursor is a caller's term of a row's step**, where the row's scope binds the
cursor's name and no later binder shadows it. `outer` is the scope of the loop, and `env` the
scope of the row. Its first consumer is the walk of Semaphore's release, whose visit reads the
walk's cursor under the visit's fold. -/
theorem captured_cursor_in_row {outer env : Env} {path : List Nat} {captured : List Val}
    {before later : Names} {v cell : Val}
    (scope : env.names = before ++ outer.mint "cursor" :: later)
    (unshadowed : ∀ name ∈ later, name ≠ outer.mint "cursor")
    (held : captured[before.length]? = some v) :
    Captured (minted (outer.mint "cursor")) (env.push [env.mint "current"]) path
      (captured ++ [cell]) v :=
  captured_minted_in_row scope unshadowed (mint_current_ne_cursor env outer)
    (mint_ne_of_head (b := 97) (c := 99) (by decide) (by decide) (by decide) _ outer)
    (mint_ne_of_head (b := 105) (c := 99) (by decide) (by decide) (by decide) _ outer) held

/-- **The typed twin** of `captured_cursor_in_row`. -/
theorem capturedTy_cursor_in_row {Op : Type} {sig : Signature Op} {outer env : Env}
    {path : List Nat} {tys : List Ty} {before later : Names} {T C : Ty}
    (scope : env.names = before ++ outer.mint "cursor" :: later)
    (unshadowed : ∀ name ∈ later, name ≠ outer.mint "cursor")
    (held : tys[before.length]? = some T) :
    CapturedTy sig (minted (outer.mint "cursor")) (env.push [env.mint "current"]) path
      (tys ++ [C]) T :=
  capturedTy_minted_in_row scope unshadowed (mint_current_ne_cursor env outer)
    (mint_ne_of_head (b := 97) (c := 99) (by decide) (by decide) (by decide) _ outer)
    (mint_ne_of_head (b := 105) (c := 99) (by decide) (by decide) (by decide) _ outer) held

/-- **The name of a row's current value is a caller's term under the step's folds**: a fold's
two names begin with other bytes. Its first consumer is Semaphore's visit, whose fold reads the
cell's own source in its body. -/
theorem captured_current {env : Env} {captured : List Val}
    (depth : captured.length = env.names.length) (path : List Nat) (cell : Val) :
    Captured (minted (env.mint "current")) (env.push [env.mint "current"]) path
      (captured ++ [cell]) cell :=
  captured_minted (i := env.names.length) (resolve_last env.names _)
    (by
      show (captured ++ [cell])[env.names.length]? = some cell
      rw [← depth, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      rfl)
    (mint_ne_of_head (b := 97) (c := 99) (by decide) (by decide) (by decide) _ env)
    (mint_ne_of_head (b := 105) (c := 99) (by decide) (by decide) (by decide) _ env)

/-- **The typed twin** of `captured_current`. -/
theorem capturedTy_current {Op : Type} {sig : Signature Op} {env : Env} {tys : List Ty}
    (depth : tys.length = env.names.length) (path : List Nat) (C : Ty) :
    CapturedTy sig (minted (env.mint "current")) (env.push [env.mint "current"]) path
      (tys ++ [C]) C :=
  capturedTy_minted (i := env.names.length) (resolve_last env.names _)
    (by
      show (tys ++ [C])[env.names.length]? = some C
      rw [← depth, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      rfl)
    (mint_ne_of_head (b := 97) (c := 99) (by decide) (by decide) (by decide) _ env)
    (mint_ne_of_head (b := 105) (c := 99) (by decide) (by decide) (by decide) _ env)

/-! # Typing at every scope (decisions row 257)

A module's operation is typed at every scope, for every caller's term of the stated type. The
statements below are the means. They name no module.

- **A typed scope** (`TypedScope`) is the names in scope with the type of each. The surface's
  binders reach deeper scopes from it (`TypedScope.Reaches`): one minted name, or two that one
  builder mints at one scope.
- **A kept term** (`Kept`) types at a scope and at every scope that the surface's binders reach
  from it. A variable that an author wrote is kept (`kept_var`): every minted name is reserved.
  A name that `bindWith` mints is kept (`kept_answer`), and so is the name of a mask's saved
  state (`kept_restore`): no later binder of the surface has either name. A string literal is
  not kept: it has two types, by the literal flag (`Types`,
  `src/Effect4/Laws/Modules/Checking.lean`).
- **A program answers a type** (`Answers`): it elaborates at every path, and the checker types
  its tree with that answer, no failure and no requirement. One rule gives what each builder
  answers, from what its parts answer. A builder that binds a name hands its continuation the
  name's reader with its typing, so no statement mentions a minted name.
- **The rows.** `Ref.make`, `Ref.get` and `Ref.modifyWith` are typed at a cell of any canonical,
  formed type (`answers_refMake`, `answers_refGet`, `answers_refModifyWith`). The step of a
  `Ref.modifyWith` has the pair of its reply's type and the cell's type, which a module's step
  theorem gives. The three rows of a hint are typed at a hint's type (`HintTy`), and the kernel
  decides them at the two hints of the Queue.
- **The shared pieces** are typed: the posted helpers (`postAll_answers`), the cleanup on
  interruption (`onInterrupt_answers`) and the wait at a mask's restore site (`waitAt_answers`).
- **The wrapper's forms are typed over a module's part** (decisions row 275, point 3). A
  module's attempt is a function of its two exits, and `Waiter.Typed` says that it answers the
  join of what they answer. `waitRetryAt_answers` and `waitRetry_answers` follow, at every result
  type in normal form. Semaphore's `take` is their first consumer
  (`src/Effect4/Laws/Modules/Semaphore/Ops.lean`). The Queue's `take` and `offer` are typed by
  their own proofs, which follow the same tree.
- **A program at any effect type** (`Has`). A protected body is a caller's program: it may fail,
  and it may require a service. The rules of the builders around it state the columns as the
  checker joins them (`has_bindWith`, `has_onExitWith`, `has_restore`, `has_maskWith`,
  `has_ifElse`). `protectedBy_has` keeps the body's answer, its failure type in normal form and
  its requirement.

Placement. Concept `store-typing`, requirement R4: helpers of a module's typing statements, the
Queue's first (`src/Effect4/Laws/Modules/Queue/Ops.lean`), and Semaphore's operations second
(`src/Effect4/Laws/Modules/Semaphore/Ops.lean`). Reach: the checker's judgment `effTy` at every typed scope; the rows at the native
signature of any row table. The mask's rule is `MaskFormProfile.typed`
(`src/Effect4/Laws/Codegen/Mask.lean`). They establish no run, no behaviour and nothing of a
target. -/

section Typing

open Conform.Effect4.Typing
open Effect4.Machine.Env (Requirement)

/-! ## Typed scopes -/

/-- The roles of the names that the surface mints: the stems of `Env.mint`. -/
inductive Stem
  | answer | cursor | payload | exit | current | restore | acc | item

/-- A role's stem, as a builder writes it. -/
def Stem.text : Stem → String
  | .answer => "answer"
  | .cursor => "cursor"
  | .payload => "payload"
  | .exit => "exit"
  | .current => "current"
  | .restore => "restore"
  | .acc => "acc"
  | .item => "item"

/-- **A typed scope**: the names in scope, and the type of each. -/
structure TypedScope where
  env : Env
  types : List Ty
  depth : types.length = env.names.length

namespace TypedScope

/-- The scope under one minted binder. -/
def push (s : TypedScope) (stem : Stem) (X : Ty) : TypedScope :=
  ⟨s.env.push [s.env.mint stem.text], s.types ++ [X], by
    simp only [Env.push_length, List.length_append, List.length_cons, List.length_nil, s.depth]⟩

/-- The scope under two binders that one builder mints at one scope: a loop's cursor and its
body's answer, and a fold's two names. -/
def push2 (s : TypedScope) (first second : Stem) (X Y : Ty) : TypedScope :=
  ⟨s.env.push [s.env.mint first.text, s.env.mint second.text], s.types ++ [X, Y], by
    simp only [Env.push_length, List.length_append, List.length_cons, List.length_nil, s.depth]⟩

/-- The scopes that the surface's binders reach from a scope. -/
inductive Reaches (s : TypedScope) : TypedScope → Prop
  | here : Reaches s s
  | push {t : TypedScope} (stem : Stem) (X : Ty) : Reaches s t → Reaches s (t.push stem X)
  | push2 {t : TypedScope} (first second : Stem) (X Y : Ty) :
      Reaches s t → Reaches s (t.push2 first second X Y)

theorem Reaches.of_push {s t : TypedScope} {stem : Stem} {X : Ty}
    (h : (s.push stem X).Reaches t) : s.Reaches t := by
  induction h with
  | here => exact .push stem X .here
  | push stem' X' _ ih => exact .push stem' X' ih
  | push2 first second X' Y' _ ih => exact .push2 first second X' Y' ih

theorem Reaches.of_push2 {s t : TypedScope} {first second : Stem} {X Y : Ty}
    (h : (s.push2 first second X Y).Reaches t) : s.Reaches t := by
  induction h with
  | here => exact .push2 first second X Y .here
  | push stem' X' _ ih => exact .push stem' X' ih
  | push2 first' second' X' Y' _ ih => exact .push2 first' second' X' Y' ih

/-- What the surface's binders reach from a reached scope, they reach from the first scope. -/
theorem Reaches.trans {s t u : TypedScope} (first : s.Reaches t) (rest : t.Reaches u) :
    s.Reaches u := by
  induction rest with
  | here => exact first
  | push stem X _ ih => exact .push stem X ih
  | push2 a b X Y _ ih => exact .push2 a b X Y ih

end TypedScope

variable {sig : Signature NativeOp}

/-- A source term types at a typed scope, at every path and under each literal flag. -/
def Typed (sig : Signature NativeOp) (src : TermSrc) (s : TypedScope) (T : Ty) : Prop :=
  ∀ path, TypesEach sig src s.env path s.types T

/-- **A term that keeps its type under the surface's binders**: it types at the scope, and at
every scope that the surface's binders reach from it. -/
def Kept (sig : Signature NativeOp) (src : TermSrc) (s : TypedScope) (T : Ty) : Prop :=
  ∀ t, s.Reaches t → Typed sig src t T

theorem Kept.here {src : TermSrc} {s : TypedScope} {T : Ty} (h : Kept sig src s T) :
    Typed sig src s T := h s .here

theorem Kept.push {src : TermSrc} {s : TypedScope} {T : Ty} (h : Kept sig src s T)
    {stem : Stem} {X : Ty} : Kept sig src (s.push stem X) T :=
  fun t reach => h t reach.of_push

theorem Kept.push2 {src : TermSrc} {s : TypedScope} {T : Ty} (h : Kept sig src s T)
    {first second : Stem} {X Y : Ty} : Kept sig src (s.push2 first second X Y) T :=
  fun t reach => h t reach.of_push2

/-- A kept term is kept at every scope that the surface's binders reach. -/
theorem Kept.reach {src : TermSrc} {s t : TypedScope} {T : Ty} (h : Kept sig src s T)
    (reach : s.Reaches t) : Kept sig src t T :=
  fun u further => h u (reach.trans further)

/-- A kept term is a caller's term under a step's folds. -/
theorem Kept.captured {src : TermSrc} {s : TypedScope} {T : Ty} (h : Kept sig src s T)
    (path : List Nat) : CapturedTy sig src s.env path s.types T :=
  ⟨h.here path, fun acc item =>
    h (s.push2 .acc .item acc item) (.push2 .acc .item acc item .here) path⟩

/-- A name keeps its level and its type along the surface's binders, where no later binder has
its name. -/
theorem resolves_along {name : String} {s : TypedScope} {i : Nat} {T : Ty}
    (bound : s.env.names.resolve name = some i) (held : s.types[i]? = some T)
    (apart : ∀ (e : Env) (stem : Stem), s.env.names.length ≤ e.names.length →
      e.mint stem.text ≠ name)
    {t : TypedScope} (reach : s.Reaches t) :
    t.env.names.resolve name = some i ∧ t.types[i]? = some T ∧
      s.env.names.length ≤ t.env.names.length := by
  induction reach with
  | here => exact ⟨bound, held, Nat.le_refl _⟩
  | @push t stem X _ ih =>
    obtain ⟨b, h, le⟩ := ih
    obtain ⟨inside, -⟩ := List.getElem?_eq_some_iff.mp h
    refine ⟨?_, ?_, ?_⟩
    · exact resolve_append_free b [t.env.mint stem.text] fun y member => by
        rw [List.mem_singleton.mp member]
        exact apart t.env stem le
    · show (t.types ++ [X])[i]? = some T
      rw [List.getElem?_append_left inside]
      exact h
    · show _ ≤ (t.env.push [t.env.mint stem.text]).names.length
      rw [Env.push_length]
      exact Nat.le_trans le (Nat.le_add_right _ _)
  | @push2 t first second X Y _ ih =>
    obtain ⟨b, h, le⟩ := ih
    obtain ⟨inside, -⟩ := List.getElem?_eq_some_iff.mp h
    refine ⟨?_, ?_, ?_⟩
    · exact resolve_append_free b [t.env.mint first.text, t.env.mint second.text]
        fun y member => by
          rcases List.mem_cons.mp member with rfl | rest
          · exact apart t.env first le
          · rw [List.mem_singleton.mp rest]
            exact apart t.env second le
    · show (t.types ++ [X, Y])[i]? = some T
      rw [List.getElem?_append_left inside]
      exact h
    · show _ ≤ (t.env.push [t.env.mint first.text, t.env.mint second.text]).names.length
      rw [Env.push_length]
      exact Nat.le_trans le (Nat.le_add_right _ _)

/-- **A minted name keeps its type under the surface's binders**, where no later binder of the
surface has its name. -/
theorem kept_minted {name : String} {s : TypedScope} {i : Nat} {T : Ty}
    (bound : s.env.names.resolve name = some i) (held : s.types[i]? = some T)
    (apart : ∀ (e : Env) (stem : Stem), s.env.names.length ≤ e.names.length →
      e.mint stem.text ≠ name) :
    Kept sig (minted name) s T := fun _ reach _ =>
  types_minted (resolves_along bound held apart reach).1 (resolves_along bound held apart reach).2.1

/-- **A variable that an author wrote keeps its type under the surface's binders**: every name
that the surface mints is reserved, and an author's name is not. -/
theorem kept_var {x : String} {s : TypedScope} {i : Nat} {T : Ty}
    (written : Name.reserved x = false) (bound : s.env.names.resolve x = some i)
    (held : s.types[i]? = some T) : Kept sig (var x) s T := fun _ reach _ =>
  have along := resolves_along bound held
    (fun e stem _ => (written_ne_mint written e stem.text).symm) reach
  types_var written along.1 along.2.1

/-! ## The names that a builder binds -/

/-- A later minted binder has no name that `bindWith` minted at a shallower scope. -/
theorem apart_answer (outer e : Env) (later : Stem)
    (deeper : outer.names.length < e.names.length) :
    e.mint later.text ≠ outer.mint "answer" := by
  cases later with
  | answer => exact later_mint_ne_answer (b := 97) deeper (by decide) (Or.inl rfl)
  | cursor => exact later_mint_ne_answer (b := 99) deeper (by decide) (Or.inr (by decide))
  | payload => exact later_mint_ne_answer (b := 112) deeper (by decide) (Or.inr (by decide))
  | exit => exact later_mint_ne_answer (b := 101) deeper (by decide) (Or.inr (by decide))
  | current => exact later_mint_ne_answer (b := 99) deeper (by decide) (Or.inr (by decide))
  | restore => exact later_mint_ne_answer (b := 114) deeper (by decide) (Or.inr (by decide))
  | acc => exact mint_acc_ne_answer e outer
  | item => exact mint_item_ne_answer e outer

/-- A later minted binder has no name that a mask minted for its saved state at a shallower
scope. -/
theorem apart_restore (outer e : Env) (later : Stem)
    (deeper : outer.names.length < e.names.length) :
    e.mint later.text ≠ outer.mint "restore" := by
  cases later with
  | restore => exact fun same => absurd (mint_depth_inj same) (Nat.ne_of_gt deeper)
  | answer => exact mint_ne_of_head (b := 97) (c := 114) (by decide) (by decide) (by decide) e outer
  | cursor => exact mint_ne_of_head (b := 99) (c := 114) (by decide) (by decide) (by decide) e outer
  | payload =>
    exact mint_ne_of_head (b := 112) (c := 114) (by decide) (by decide) (by decide) e outer
  | exit => exact mint_ne_of_head (b := 101) (c := 114) (by decide) (by decide) (by decide) e outer
  | current =>
    exact mint_ne_of_head (b := 99) (c := 114) (by decide) (by decide) (by decide) e outer
  | acc => exact mint_ne_of_head (b := 97) (c := 114) (by decide) (by decide) (by decide) e outer
  | item => exact mint_ne_of_head (b := 105) (c := 114) (by decide) (by decide) (by decide) e outer

/-- The last name of a scope has the last type. -/
theorem held_last (s : TypedScope) (X : Ty) :
    (s.types ++ [X])[s.env.names.length]? = some X := by
  rw [← s.depth, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

theorem deeper_push (s : TypedScope) (stem : Stem) (X : Ty) {e : Env}
    (le : (s.push stem X).env.names.length ≤ e.names.length) :
    s.env.names.length < e.names.length := by
  have pushed : (s.push stem X).env.names.length = s.env.names.length + 1 := by
    show (s.env.push [s.env.mint stem.text]).names.length = _
    rw [Env.push_length]
    rfl
  omega

/-- **The name that `bindWith` mints keeps its type under the surface's binders.** -/
theorem kept_answer (s : TypedScope) (X : Ty) :
    Kept sig (minted (s.env.mint "answer")) (s.push .answer X) X :=
  kept_minted (i := s.env.names.length) (resolve_last s.env.names _) (held_last s X)
    fun e stem le => apart_answer s.env e stem (deeper_push s .answer X le)

/-- **The name that a mask mints for its saved state keeps its type under the surface's
binders.** -/
theorem kept_restore (s : TypedScope) (X : Ty) :
    Kept sig (minted (s.env.mint "restore")) (s.push .restore X) X :=
  kept_minted (i := s.env.names.length) (resolve_last s.env.names _) (held_last s X)
    fun e stem le => apart_restore s.env e stem (deeper_push s .restore X le)

/-- A later minted binder has no name that a loop minted for its cursor at a shallower scope.
The row's own binder is told apart at the stems' fourth byte (`mint_current_ne_cursor`). -/
theorem apart_cursor (outer e : Env) (later : Stem)
    (deeper : outer.names.length < e.names.length) :
    e.mint later.text ≠ outer.mint "cursor" := by
  cases later with
  | cursor => exact fun same => absurd (mint_depth_inj same) (Nat.ne_of_gt deeper)
  | current => exact mint_current_ne_cursor e outer
  | answer => exact mint_ne_of_head (b := 97) (c := 99) (by decide) (by decide) (by decide) e outer
  | payload =>
    exact mint_ne_of_head (b := 112) (c := 99) (by decide) (by decide) (by decide) e outer
  | exit => exact mint_ne_of_head (b := 101) (c := 99) (by decide) (by decide) (by decide) e outer
  | restore =>
    exact mint_ne_of_head (b := 114) (c := 99) (by decide) (by decide) (by decide) e outer
  | acc => exact mint_ne_of_head (b := 97) (c := 99) (by decide) (by decide) (by decide) e outer
  | item => exact mint_ne_of_head (b := 105) (c := 99) (by decide) (by decide) (by decide) e outer

/-- **The name that a loop mints for its cursor keeps its type under the surface's binders.** So
a loop's body may hand its cursor to a row's step, which reads it under its own binder. -/
theorem kept_cursor (s : TypedScope) (X : Ty) :
    Kept sig (minted (s.env.mint "cursor")) (s.push .cursor X) X :=
  kept_minted (i := s.env.names.length) (resolve_last s.env.names _) (held_last s X)
    fun e stem le => apart_cursor s.env e stem (deeper_push s .cursor X le)

/-- A later minted binder has no name that a selection minted for its payload at a shallower
scope: every other stem of the surface begins with another byte. -/
theorem apart_payload (outer e : Env) (later : Stem)
    (deeper : outer.names.length < e.names.length) :
    e.mint later.text ≠ outer.mint "payload" := by
  cases later with
  | payload => exact fun same => absurd (mint_depth_inj same) (Nat.ne_of_gt deeper)
  | answer =>
    exact mint_ne_of_head (b := 97) (c := 112) (by decide) (by decide) (by decide) e outer
  | cursor =>
    exact mint_ne_of_head (b := 99) (c := 112) (by decide) (by decide) (by decide) e outer
  | exit =>
    exact mint_ne_of_head (b := 101) (c := 112) (by decide) (by decide) (by decide) e outer
  | current =>
    exact mint_ne_of_head (b := 99) (c := 112) (by decide) (by decide) (by decide) e outer
  | restore =>
    exact mint_ne_of_head (b := 114) (c := 112) (by decide) (by decide) (by decide) e outer
  | acc => exact mint_ne_of_head (b := 97) (c := 112) (by decide) (by decide) (by decide) e outer
  | item =>
    exact mint_ne_of_head (b := 105) (c := 112) (by decide) (by decide) (by decide) e outer

/-- **The name that a selection mints for its payload keeps its type under the surface's
binders.** So the second arm may read the payload under more binders: the walk of Semaphore's
release reads a selected waiter's stamp after it resolves that waiter's hint. -/
theorem kept_payload (s : TypedScope) (X : Ty) :
    Kept sig (minted (s.env.mint "payload")) (s.push .payload X) X :=
  kept_minted (i := s.env.names.length) (resolve_last s.env.names _) (held_last s X)
    fun e stem le => apart_payload s.env e stem (deeper_push s .payload X le)

/-- The name that a builder binds has its type at the builder's scope. -/
theorem typed_bound (s : TypedScope) (stem : Stem) (X : Ty) :
    Typed sig (minted (s.env.mint stem.text)) (s.push stem X) X :=
  fun path => types_minted_last s.depth path stem.text X

/-- The first of two names that a builder binds at one scope has the first type, where the
second name is another name. -/
theorem typed_first (s : TypedScope) (first second : Stem) (X Y : Ty)
    (apart : s.env.mint second.text ≠ s.env.mint first.text) :
    Typed sig (minted (s.env.mint first.text)) (s.push2 first second X Y) X := fun _ =>
  types_minted
    (resolve_unshadowed s.env.names _ [s.env.mint second.text] fun y member => by
      rw [List.mem_singleton.mp member]
      exact apart)
    (by
      show (s.types ++ [X, Y])[s.env.names.length]? = some X
      rw [← s.depth, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      rfl)

/-- The second of two names that a builder binds at one scope has the second type. -/
theorem typed_second (s : TypedScope) (first second : Stem) (X Y : Ty) :
    Typed sig (minted (s.env.mint second.text)) (s.push2 first second X Y) Y := fun _ =>
  types_minted (i := s.env.names.length + 1)
    (by
      show Names.resolve (s.env.names ++ [s.env.mint first.text, s.env.mint second.text]) _ = _
      have split : s.env.names ++ [s.env.mint first.text, s.env.mint second.text] =
          (s.env.names ++ [s.env.mint first.text]) ++ [s.env.mint second.text] := by
        rw [List.append_assoc]
        rfl
      rw [split, resolve_last, List.length_append]
      rfl)
    (by
      show (s.types ++ [X, Y])[s.env.names.length + 1]? = some Y
      rw [← s.depth, List.getElem?_append_right (Nat.le_succ _)]
      have one : s.types.length + 1 - s.types.length = 1 := by omega
      rw [one]
      rfl)

/-! ## Programs: the judgment, and what each builder answers -/

/-- **A source program answers a type at a typed scope**: it elaborates under the scope's
names at every path, and the checker types its tree at the scope's types with that answer, no
failure and no requirement. -/
def Answers (sig : Signature NativeOp) (src : Src NativeOp) (s : TypedScope) (T : Ty) : Prop :=
  ∀ path, ∃ p, src s.env path = .ok p ∧ effTy sig s.types p = some (EffTy.pure T)

/-- An answer at a type that is the same type. -/
theorem Answers.to {src : Src NativeOp} {s : TypedScope} {T U : Ty} (h : Answers sig src s T)
    (same : T = U) : Answers sig src s U := same ▸ h

/-- Two columns with no failure and no requirement join to the same. -/
theorem pure_columns (T : Ty) :
    (⟨T, Ty.never.join Ty.never, Requirement.empty.union Requirement.empty⟩ : EffTy) =
      EffTy.pure T := rfl

theorem answers_succeed {value : TermSrc} {s : TypedScope} {T : Ty}
    (h : Typed sig value s T) : Answers sig (succeed value) s T := by
  intro path
  obtain ⟨t, tree, typed⟩ := h path false
  refine ⟨.succeed t, ?_, effTy_complete sig _ _ _ (.succeed typed)⟩
  show (value s.env path >>= fun x => Except.ok (Eff.succeed x)) = _
  rw [tree]
  rfl

/-- **`bindWith`**: the continuation reads the first program's answer through a kept term. -/
theorem answers_bindWith {first : Src NativeOp} {rest : TermSrc → Src NativeOp}
    {s : TypedScope} {X Y : Ty} (hfirst : Answers sig first s X)
    (hrest : ∀ x : TermSrc, Kept sig x (s.push .answer X) X →
      Answers sig (rest x) (s.push .answer X) Y) :
    Answers sig (bindWith first rest) s Y := by
  intro path
  obtain ⟨a, treeA, typedA⟩ := hfirst (path ++ [0])
  obtain ⟨b, treeB, typedB⟩ := hrest _ (kept_answer s X) (path ++ [1])
  have treeB' : rest (minted (s.env.mint "answer")) (s.env.push [s.env.mint "answer"])
      (path ++ [1]) = .ok b := treeB
  refine ⟨.bind a b, ?_, ?_⟩
  · show (first s.env (path ++ [0]) >>= fun x0 =>
      rest (minted (s.env.mint "answer")) (s.env.push [s.env.mint "answer"]) (path ++ [1]) >>=
        fun x1 => Except.ok (Eff.bind x0 x1)) = _
    rw [treeA, treeB']
    rfl
  · exact (effTy_complete sig _ _ _
      (.bind (effTy_sound sig a _ _ typedA) (effTy_sound sig b _ _ typedB))).trans
        (congrArg some (pure_columns Y))

/-- **`andThen`**: the second program stands under the binder of the first's discarded answer. -/
theorem answers_andThen {first rest : Src NativeOp} {s : TypedScope} {X Y : Ty}
    (hfirst : Answers sig first s X) (hrest : Answers sig rest (s.push .answer X) Y) :
    Answers sig (andThen first rest) s Y := by
  intro path
  obtain ⟨a, treeA, typedA⟩ := hfirst (path ++ [0])
  obtain ⟨b, treeB, typedB⟩ := hrest (path ++ [1])
  have treeB' : rest (s.env.push [s.env.mint "answer"]) (path ++ [1]) = .ok b := treeB
  refine ⟨.bind a b, ?_, ?_⟩
  · show (first s.env (path ++ [0]) >>= fun x0 =>
      rest (s.env.push [s.env.mint "answer"]) (path ++ [1]) >>=
        fun x1 => Except.ok (Eff.bind x0 x1)) = _
    rw [treeA, treeB']
    rfl
  · exact (effTy_complete sig _ _ _
      (.bind (effTy_sound sig a _ _ typedA) (effTy_sound sig b _ _ typedB))).trans
        (congrArg some (pure_columns Y))

/-- **`ifElse`**: the two arms' answers join. -/
theorem answers_ifElse {test : TermSrc} {thenB elseB : Src NativeOp} {s : TypedScope}
    {X Y : Ty} (htest : Typed sig test s .bool) (hthen : Answers sig thenB s X)
    (helse : Answers sig elseB s Y) :
    Answers sig (ifElse test thenB elseB) s (Ty.join X Y) := by
  intro path
  obtain ⟨c, treeC, typedC⟩ := htest path false
  obtain ⟨a, treeA, typedA⟩ := hthen (path ++ [0])
  obtain ⟨b, treeB, typedB⟩ := helse (path ++ [1])
  refine ⟨.select c .bool a b, ?_, ?_⟩
  · show (test s.env path >>= fun x0 => thenB s.env (path ++ [0]) >>= fun x2 =>
      elseB s.env (path ++ [1]) >>= fun x3 => Except.ok (Eff.select x0 .bool x2 x3)) = _
    rw [treeC, treeA, treeB]
    rfl
  · have left : HasTy sig (s.types ++ []) a (EffTy.pure X) := by
      rw [List.append_nil]
      exact effTy_sound sig a _ _ typedA
    have right : HasTy sig (s.types ++ []) b (EffTy.pure Y) := by
      rw [List.append_nil]
      exact effTy_sound sig b _ _ typedB
    exact (effTy_complete sig _ _ _
      (.select (d := .bool) (e0 := []) (e1 := []) typedC rfl left right rfl)).trans
        (congrArg some (pure_columns _))

/-- **`selectOptionWith`, with a kept payload.** The second arm reads the payload through a kept
term: it may read it under more binders. The two arms' answers join. -/
theorem answers_selectOptionWith_kept {scrutinee : TermSrc} {arm0 : Src NativeOp}
    {arm1 : TermSrc → Src NativeOp} {s : TypedScope} {P X Y : Ty}
    (canonical : P.normalize = P) (hscrutinee : Typed sig scrutinee s (.option P))
    (h0 : Answers sig arm0 s X)
    (h1 : ∀ x : TermSrc, Kept sig x (s.push .payload P) P →
      Answers sig (arm1 x) (s.push .payload P) Y) :
    Answers sig (selectOptionWith scrutinee arm0 arm1) s (Ty.join X Y) := by
  intro path
  obtain ⟨c, treeC, typedC⟩ := hscrutinee path false
  obtain ⟨a, treeA, typedA⟩ := h0 (path ++ [0])
  obtain ⟨b, treeB, typedB⟩ := h1 _ (kept_payload s P) (path ++ [1])
  have treeB' : arm1 (minted (s.env.mint "payload")) (s.env.push [s.env.mint "payload"])
      (path ++ [1]) = .ok b := treeB
  refine ⟨.select c .option a b, ?_, ?_⟩
  · show (scrutinee s.env path >>= fun x0 => arm0 s.env (path ++ [0]) >>= fun x2 =>
      arm1 (minted (s.env.mint "payload")) (s.env.push [s.env.mint "payload"]) (path ++ [1]) >>=
        fun x3 => Except.ok (Eff.select x0 .option x2 x3)) = _
    rw [treeC, treeA, treeB']
    rfl
  · have arms : Decision.arms .option (.option P) = some ([], [P]) := by
      show (match (Ty.option P).normalize with
        | .option a => some (([] : List Ty), [a])
        | _ => none) = _
      rw [Ty.normalize_option_canonical canonical]
    have left : HasTy sig (s.types ++ []) a (EffTy.pure X) := by
      rw [List.append_nil]
      exact effTy_sound sig a _ _ typedA
    exact (effTy_complete sig _ _ _
      (.select (d := .option) typedC arms left (effTy_sound sig b _ _ typedB) rfl)).trans
        (congrArg some (pure_columns _))

/-- **`selectOptionWith`**: the second arm reads the payload at its type, and the two arms'
answers join. -/
theorem answers_selectOptionWith {scrutinee : TermSrc} {arm0 : Src NativeOp}
    {arm1 : TermSrc → Src NativeOp} {s : TypedScope} {P X Y : Ty}
    (canonical : P.normalize = P) (hscrutinee : Typed sig scrutinee s (.option P))
    (h0 : Answers sig arm0 s X)
    (h1 : ∀ x : TermSrc, Typed sig x (s.push .payload P) P →
      Answers sig (arm1 x) (s.push .payload P) Y) :
    Answers sig (selectOptionWith scrutinee arm0 arm1) s (Ty.join X Y) :=
  answers_selectOptionWith_kept canonical hscrutinee h0 fun x hx => h1 x hx.here

/-- **`onExitWith`**: the finalizer reads the body's exit, and the program answers as its
body. -/
theorem answers_onExitWith {body : Src NativeOp} {finalizer : TermSrc → Src NativeOp}
    {s : TypedScope} {X F : Ty} (hbody : Answers sig body s X)
    (hfinal : ∀ x : TermSrc, Typed sig x (s.push .exit (.exitOf X .never)) (.exitOf X .never) →
      Answers sig (finalizer x) (s.push .exit (.exitOf X .never)) F) :
    Answers sig (onExitWith body finalizer) s X := by
  intro path
  obtain ⟨a, treeA, typedA⟩ := hbody (path ++ [0])
  obtain ⟨b, treeB, typedB⟩ := hfinal _ (typed_bound s .exit _) (path ++ [1])
  have treeB' : finalizer (minted (s.env.mint "exit")) (s.env.push [s.env.mint "exit"])
      (path ++ [1]) = .ok b := treeB
  refine ⟨.onExit a b, ?_, ?_⟩
  · show (body s.env (path ++ [0]) >>= fun x0 =>
      finalizer (minted (s.env.mint "exit")) (s.env.push [s.env.mint "exit"]) (path ++ [1]) >>=
        fun x1 => Except.ok (Eff.onExit x0 x1)) = _
    rw [treeA, treeB']
    rfl
  · exact (effTy_complete sig _ _ _
      (.onExit (effTy_sound sig a _ _ typedA) (effTy_sound sig b _ _ typedB))).trans
        (congrArg some (pure_columns X))

theorem answers_uninterruptible {body : Src NativeOp} {s : TypedScope} {X : Ty}
    (hbody : Answers sig body s X) : Answers sig (uninterruptible body) s X := by
  intro path
  obtain ⟨a, treeA, typedA⟩ := hbody (path ++ [0])
  refine ⟨.uninterruptible a, ?_,
    effTy_complete sig _ _ _ (.uninterruptible (effTy_sound sig a _ _ typedA))⟩
  show (body s.env (path ++ [0]) >>= fun x0 => Except.ok (Eff.uninterruptible x0)) = _
  rw [treeA]
  rfl

/-- A restore site answers as its body, where its saved term has the saved state's type. -/
theorem answers_restore {saved : TermSrc} {body : Src NativeOp} {s : TypedScope} {X : Ty}
    (hsaved : Typed sig saved s Ty.maskRestore) (hbody : Answers sig body s X) :
    Answers sig (Authoring.restore saved body) s X := by
  intro path
  obtain ⟨c, treeC, typedC⟩ := hsaved path false
  obtain ⟨a, treeA, typedA⟩ := hbody (path ++ [0])
  refine ⟨.restore c a, ?_,
    effTy_complete sig _ _ _ (.restore typedC (effTy_sound sig a _ _ typedA))⟩
  show (saved s.env path >>= fun x0 => body s.env (path ++ [0]) >>= fun x1 =>
    Except.ok (Eff.restore x0 x1)) = _
  rw [treeC, treeA]
  rfl

/-- **`uninterruptibleMaskWith`**: the body's `restore` answers as its argument, at every scope
that the surface's binders reach from the mask's. The program answers as its body
(`MaskFormProfile.typed`, `src/Effect4/Laws/Codegen/Mask.lean`). -/
theorem answers_maskWith {body : (Src NativeOp → Src NativeOp) → Src NativeOp}
    {s : TypedScope} {X : Ty}
    (hbody : ∀ restore : Src NativeOp → Src NativeOp,
      (∀ (t : TypedScope) (inner : Src NativeOp) (Y : Ty),
        (s.push .restore Ty.maskRestore).Reaches t → Answers sig inner t Y →
          Answers sig (restore inner) t Y) →
      Answers sig (body restore) (s.push .restore Ty.maskRestore) X) :
    Answers sig (uninterruptibleMaskWith body) s X := by
  intro path
  obtain ⟨a, treeA, typedA⟩ := hbody (Authoring.restore (minted (s.env.mint "restore")))
    (fun t inner Y reach hinner => answers_restore (kept_restore s Ty.maskRestore t reach) hinner)
    (path ++ [1] ++ [0])
  have treeA' : body (Authoring.restore (minted (s.env.mint "restore")))
      (s.env.push [s.env.mint "restore"]) (path ++ [1] ++ [0]) = .ok a := treeA
  refine ⟨Effect4.Program.maskForm a, ?_, ?_⟩
  · show (Except.ok (Eff.withFiber ActionTerm.getInterruptible) >>= fun x0 =>
      (body (Authoring.restore (minted (s.env.mint "restore")))
        (s.env.push [s.env.mint "restore"]) (path ++ [1] ++ [0]) >>= fun y =>
          Except.ok (Eff.uninterruptible y)) >>= fun x1 => Except.ok (Eff.bind x0 x1)) = _
    rw [treeA']
    rfl
  · exact (Effect4.Program.mask_printed_form_profile.typed sig s.types a _ typedA).trans
      (congrArg some (pure_columns X))

/-- **`withFiber (Action.fork …)`**: a fork answers its child's handle. -/
theorem answers_fork {program : Src NativeOp} {options : Supervision.ForkOptions}
    {s : TypedScope} {X : Ty} (h : Answers sig program s X) :
    Answers sig (withFiber (Action.fork program options)) s (.fiberOf X .never) := by
  intro path
  obtain ⟨a, treeA, typedA⟩ := h (path ++ [0] ++ [0])
  refine ⟨.withFiber (.fork a options), ?_,
    effTy_complete sig _ _ _ (.withFiber (.fork options (effTy_sound sig a _ _ typedA)))⟩
  show ((program s.env (path ++ [0] ++ [0]) >>= fun x0 =>
    Except.ok (ActionTerm.fork x0 options)) >>= fun y => Except.ok (Eff.withFiber y)) = _
  rw [treeA]
  rfl

/-- A defect of a text answers nothing, fails with nothing and requires nothing. -/
theorem answers_die (text : String) (s : TypedScope) :
    Answers sig (failCause (Authoring.Cause.die (str text))) s .never := by
  intro path
  exact ⟨.failCause (.die (.lit (.str text))), rfl,
    effTy_complete sig _ _ _ (.failCause (ty := .never) rfl)⟩

/-- **`iterateWith`, with a kept cursor in the body.** The test, the step and the result read
the cursor at its type, and the step reads the body's answer. The body reads the cursor through
a kept term: it may hand the cursor to a row's step, which reads it under more binders. The
initial value and the step are below the cursor's type in the checker's order. The loop answers
its result. -/
theorem answers_iterateWith_kept {initial : TermSrc} {spec : LoopSpec NativeOp} {s : TypedScope}
    {C0 C B C1 D : Ty} (cursor : spec.cursorTy.getD C0 = C) (hinitial : Typed sig initial s C0)
    (htest : ∀ c : TermSrc, Typed sig c (s.push .cursor C) C →
      Typed sig (spec.while_ c) (s.push .cursor C) .bool)
    (hbody : ∀ c : TermSrc, Kept sig c (s.push .cursor C) C →
      Answers sig (spec.body c) (s.push .cursor C) B)
    (hstep : ∀ c a : TermSrc, Typed sig c (s.push2 .cursor .answer C B) C →
      Typed sig a (s.push2 .cursor .answer C B) B →
        Typed sig (spec.step c a) (s.push2 .cursor .answer C B) C1)
    (hresult : ∀ c : TermSrc, Typed sig c (s.push .cursor C) C →
      Typed sig (spec.result c) (s.push .cursor C) D)
    (start : Ty.subN C0 C = true) (next : Ty.subN C1 C = true) :
    Answers sig (iterateWith initial spec) s D := by
  intro path
  subst cursor
  have apart : s.env.mint "answer" ≠ s.env.mint "cursor" :=
    mint_ne_of_head (b := 97) (c := 99) (by decide) (by decide) (by decide) s.env s.env
  obtain ⟨i, treeI, typedI⟩ := hinitial path false
  obtain ⟨t, treeT, typedT⟩ := htest _ (typed_bound s .cursor _) path false
  obtain ⟨b, treeB, typedB⟩ := hbody _ (kept_cursor s _) (path ++ [0])
  obtain ⟨st, treeS, typedS⟩ := hstep _ _ (typed_first s .cursor .answer _ _ apart)
    (typed_second s .cursor .answer _ _) path false
  obtain ⟨r, treeR, typedR⟩ := hresult _ (typed_bound s .cursor _) path false
  have treeT' : spec.while_ (minted (s.env.mint "cursor")) (s.env.push [s.env.mint "cursor"])
      path = .ok t := treeT
  have treeB' : spec.body (minted (s.env.mint "cursor")) (s.env.push [s.env.mint "cursor"])
      (path ++ [0]) = .ok b := treeB
  have treeS' : spec.step (minted (s.env.mint "cursor")) (minted (s.env.mint "answer"))
      (s.env.push [s.env.mint "cursor", s.env.mint "answer"]) path = .ok st := treeS
  have treeR' : spec.result (minted (s.env.mint "cursor")) (s.env.push [s.env.mint "cursor"])
      path = .ok r := treeR
  refine ⟨.iterate spec.cursorTy i t st r b, ?_,
    effTy_complete sig _ _ _
      (.iterate typedI typedT (effTy_sound sig b _ _ typedB) typedS typedR start next)⟩
  show (initial s.env path >>= fun x1 =>
    spec.while_ (minted (s.env.mint "cursor")) (s.env.push [s.env.mint "cursor"]) path >>=
      fun x2 => spec.step (minted (s.env.mint "cursor")) (minted (s.env.mint "answer"))
        (s.env.push [s.env.mint "cursor", s.env.mint "answer"]) path >>= fun x3 =>
          spec.result (minted (s.env.mint "cursor")) (s.env.push [s.env.mint "cursor"]) path >>=
            fun x4 => spec.body (minted (s.env.mint "cursor"))
              (s.env.push [s.env.mint "cursor"]) (path ++ [0]) >>= fun x5 =>
                Except.ok (Eff.iterate spec.cursorTy x1 x2 x3 x4 x5)) = _
  rw [treeI, treeT', treeS', treeR', treeB']
  rfl

/-- **`iterateWith`**: the test, the body, the step and the result read the cursor at its type,
and the step reads the body's answer. The initial value and the step are below the cursor's
type in the checker's order. The loop answers its result. -/
theorem answers_iterateWith {initial : TermSrc} {spec : LoopSpec NativeOp} {s : TypedScope}
    {C0 C B C1 D : Ty} (cursor : spec.cursorTy.getD C0 = C) (hinitial : Typed sig initial s C0)
    (htest : ∀ c : TermSrc, Typed sig c (s.push .cursor C) C →
      Typed sig (spec.while_ c) (s.push .cursor C) .bool)
    (hbody : ∀ c : TermSrc, Typed sig c (s.push .cursor C) C →
      Answers sig (spec.body c) (s.push .cursor C) B)
    (hstep : ∀ c a : TermSrc, Typed sig c (s.push2 .cursor .answer C B) C →
      Typed sig a (s.push2 .cursor .answer C B) B →
        Typed sig (spec.step c a) (s.push2 .cursor .answer C B) C1)
    (hresult : ∀ c : TermSrc, Typed sig c (s.push .cursor C) C →
      Typed sig (spec.result c) (s.push .cursor C) D)
    (start : Ty.subN C0 C = true) (next : Ty.subN C1 C = true) :
    Answers sig (iterateWith initial spec) s D :=
  answers_iterateWith_kept cursor hinitial htest (fun c hc => hbody c hc.here) hstep hresult
    start next

/-! ## Programs at any effect type

`Answers` is the judgment of a program with no failure and no requirement: every piece of a
module's own operation is one. A protected body is a caller's program, and it may fail or
require a service. `Has` is the same judgment at any effect type, and the rules below are the
rules of the builders that stand around such a body: a sequence, a hook on the exit, a restore
site, the mask and a selection. Each states the columns as the checker joins them. -/

/-- **A source program has an effect type at a typed scope**: it elaborates under the scope's
names at every path, and the checker types its tree at the scope's types with that effect type.
`Answers` is `Has` at an answer with no failure and no requirement. -/
def Has (sig : Signature NativeOp) (src : Src NativeOp) (s : TypedScope) (t : EffTy) : Prop :=
  ∀ path, ∃ p, src s.env path = .ok p ∧ effTy sig s.types p = some t

/-- A program that answers a type has that answer's effect type. -/
theorem Answers.has {src : Src NativeOp} {s : TypedScope} {T : Ty} (h : Answers sig src s T) :
    Has sig src s (EffTy.pure T) := h

/-- An effect type with no failure and no requirement is an answer. -/
theorem Has.answers {src : Src NativeOp} {s : TypedScope} {T : Ty}
    (h : Has sig src s (EffTy.pure T)) : Answers sig src s T := h

/-- An effect type that is the same effect type. -/
theorem Has.to {src : Src NativeOp} {s : TypedScope} {t u : EffTy} (h : Has sig src s t)
    (same : t = u) : Has sig src s u := same ▸ h

/-- **`bindWith`, at any effect types**: the errors join and the requirements union. -/
theorem has_bindWith {first : Src NativeOp} {rest : TermSrc → Src NativeOp} {s : TypedScope}
    {f r : EffTy} (hfirst : Has sig first s f)
    (hrest : ∀ x : TermSrc, Kept sig x (s.push .answer f.answer) f.answer →
      Has sig (rest x) (s.push .answer f.answer) r) :
    Has sig (bindWith first rest) s
      ⟨r.answer, f.error.join r.error, f.requires.union r.requires⟩ := by
  intro path
  obtain ⟨a, treeA, typedA⟩ := hfirst (path ++ [0])
  obtain ⟨b, treeB, typedB⟩ := hrest _ (kept_answer s f.answer) (path ++ [1])
  have treeB' : rest (minted (s.env.mint "answer")) (s.env.push [s.env.mint "answer"])
      (path ++ [1]) = .ok b := treeB
  refine ⟨.bind a b, ?_, effTy_complete sig _ _ _
    (.bind (effTy_sound sig a _ _ typedA) (effTy_sound sig b _ _ typedB))⟩
  show (first s.env (path ++ [0]) >>= fun x0 =>
    rest (minted (s.env.mint "answer")) (s.env.push [s.env.mint "answer"]) (path ++ [1]) >>=
      fun x1 => Except.ok (Eff.bind x0 x1)) = _
  rw [treeA, treeB']
  rfl

/-- **`onExitWith`, at any effect types**: the finalizer reads the body's exit, at the body's
answer and failure types. The node keeps the body's answer, and the finalizer's failure and
requirement join the body's. -/
theorem has_onExitWith {body : Src NativeOp} {finalizer : TermSrc → Src NativeOp}
    {s : TypedScope} {b f : EffTy} (hbody : Has sig body s b)
    (hfinal : ∀ x : TermSrc,
      Typed sig x (s.push .exit (.exitOf b.answer b.error)) (.exitOf b.answer b.error) →
        Has sig (finalizer x) (s.push .exit (.exitOf b.answer b.error)) f) :
    Has sig (onExitWith body finalizer) s
      ⟨b.answer, b.error.join f.error, b.requires.union f.requires⟩ := by
  intro path
  obtain ⟨a, treeA, typedA⟩ := hbody (path ++ [0])
  obtain ⟨c, treeC, typedC⟩ := hfinal _ (typed_bound s .exit _) (path ++ [1])
  have treeC' : finalizer (minted (s.env.mint "exit")) (s.env.push [s.env.mint "exit"])
      (path ++ [1]) = .ok c := treeC
  refine ⟨.onExit a c, ?_, effTy_complete sig _ _ _
    (.onExit (effTy_sound sig a _ _ typedA) (effTy_sound sig c _ _ typedC))⟩
  show (body s.env (path ++ [0]) >>= fun x0 =>
    finalizer (minted (s.env.mint "exit")) (s.env.push [s.env.mint "exit"]) (path ++ [1]) >>=
      fun x1 => Except.ok (Eff.onExit x0 x1)) = _
  rw [treeA, treeC']
  rfl

/-- A restore site has its body's effect type, where its saved term has the saved state's
type. -/
theorem has_restore {saved : TermSrc} {body : Src NativeOp} {s : TypedScope} {t : EffTy}
    (hsaved : Typed sig saved s Ty.maskRestore) (hbody : Has sig body s t) :
    Has sig (Authoring.restore saved body) s t := by
  intro path
  obtain ⟨c, treeC, typedC⟩ := hsaved path false
  obtain ⟨a, treeA, typedA⟩ := hbody (path ++ [0])
  refine ⟨.restore c a, ?_,
    effTy_complete sig _ _ _ (.restore typedC (effTy_sound sig a _ _ typedA))⟩
  show (saved s.env path >>= fun x0 => body s.env (path ++ [0]) >>= fun x1 =>
    Except.ok (Eff.restore x0 x1)) = _
  rw [treeC, treeA]
  rfl

/-- **`uninterruptibleMaskWith`, at any effect type**: the body's `restore` keeps the effect
type of its argument, at every scope that the surface's binders reach from the mask's. The mask
has its body's answer, and the getter's two empty columns join the body's
(`MaskFormProfile.typed`, `src/Effect4/Laws/Codegen/Mask.lean`). -/
theorem has_maskWith {body : (Src NativeOp → Src NativeOp) → Src NativeOp} {s : TypedScope}
    {b : EffTy}
    (hbody : ∀ restore : Src NativeOp → Src NativeOp,
      (∀ (t : TypedScope) (inner : Src NativeOp) (y : EffTy),
        (s.push .restore Ty.maskRestore).Reaches t → Has sig inner t y →
          Has sig (restore inner) t y) →
      Has sig (body restore) (s.push .restore Ty.maskRestore) b) :
    Has sig (uninterruptibleMaskWith body) s
      ⟨b.answer, Ty.never.join b.error, Requirement.empty.union b.requires⟩ := by
  intro path
  obtain ⟨a, treeA, typedA⟩ := hbody (Authoring.restore (minted (s.env.mint "restore")))
    (fun t inner y reach hinner => has_restore (kept_restore s Ty.maskRestore t reach) hinner)
    (path ++ [1] ++ [0])
  have treeA' : body (Authoring.restore (minted (s.env.mint "restore")))
      (s.env.push [s.env.mint "restore"]) (path ++ [1] ++ [0]) = .ok a := treeA
  refine ⟨Effect4.Program.maskForm a, ?_,
    Effect4.Program.mask_printed_form_profile.typed sig s.types a _ typedA⟩
  show (Except.ok (Eff.withFiber ActionTerm.getInterruptible) >>= fun x0 =>
    (body (Authoring.restore (minted (s.env.mint "restore")))
      (s.env.push [s.env.mint "restore"]) (path ++ [1] ++ [0]) >>= fun y =>
        Except.ok (Eff.uninterruptible y)) >>= fun x1 => Except.ok (Eff.bind x0 x1)) = _
  rw [treeA']
  rfl

/-- **`ifElse`, at any effect types**: the two arms' answers join, their errors join and their
requirements union. -/
theorem has_ifElse {test : TermSrc} {thenB elseB : Src NativeOp} {s : TypedScope}
    {t0 t1 : EffTy} (htest : Typed sig test s .bool) (hthen : Has sig thenB s t0)
    (helse : Has sig elseB s t1) :
    Has sig (ifElse test thenB elseB) s
      ⟨Ty.join t0.answer t1.answer, t0.error.join t1.error, t0.requires.union t1.requires⟩ := by
  intro path
  obtain ⟨c, treeC, typedC⟩ := htest path false
  obtain ⟨a, treeA, typedA⟩ := hthen (path ++ [0])
  obtain ⟨b, treeB, typedB⟩ := helse (path ++ [1])
  refine ⟨.select c .bool a b, ?_, ?_⟩
  · show (test s.env path >>= fun x0 => thenB s.env (path ++ [0]) >>= fun x2 =>
      elseB s.env (path ++ [1]) >>= fun x3 => Except.ok (Eff.select x0 .bool x2 x3)) = _
    rw [treeC, treeA, treeB]
    rfl
  · have left : HasTy sig (s.types ++ []) a t0 := by
      rw [List.append_nil]
      exact effTy_sound sig a _ _ typedA
    have right : HasTy sig (s.types ++ []) b t1 := by
      rw [List.append_nil]
      exact effTy_sound sig b _ _ typedB
    exact effTy_complete sig _ _ _
      (.select (d := .bool) (e0 := []) (e1 := []) typedC rfl left right rfl)

/-! ## Rows -/

/-- **A row's use answers the row's answer**, where the operation is in the signature's domain,
the request has its type, and the row check answers with no failure and no requirement. -/
theorem answers_perform {op : NativeOp} {request : TermSrc} {s : TypedScope} {R T : Ty}
    (dom : sig.dom op = true)
    (hrequest : ∀ path, Types sig request s.env path s.types false R)
    (row : rowTy (sig.rowOf op) R (sig.termUse s.types op) = some (EffTy.pure T)) :
    Answers sig (perform op request) s T := by
  intro path
  obtain ⟨r, tree, typed⟩ := hrequest path
  refine ⟨.perform op r, ?_, effTy_complete sig _ _ _ (.perform dom typed row)⟩
  show (request s.env path >>= fun x1 => Except.ok (Eff.perform op x1)) = _
  rw [tree]
  rfl

/-- The row check in its introduction form: the request matches the row's template, the binder
term binds, and every instantiated column is formed. -/
theorem rowTy_intro {row : Effect4.Program.Row} {request : Ty} {use : Option TermUse} {σ bindings : Ty.Subst}
    (matched : Ty.matchTemplate [] row.request.normalize request.normalize = some σ)
    (bound : bindTerm σ use = .ok bindings)
    (formed : Formation.Formed (Formation.instantiatedSites row bindings)) :
    rowTy row request use =
      some ⟨(row.answer.instantiate bindings).normalize,
        (row.error.instantiate bindings).normalize, Requirement.ofList row.requires⟩ := by
  rw [rowTy_eq_some_iff]
  simp only [checkRow, matched, bound, (Formation.check_eq_none_iff _).mpr formed]

/-- Every raw occurrence of a type is formed, outside a template
(`Formation.HeadFormed`). -/
def NodesFormed (T : Ty) : Prop := ∀ t ∈ Formation.nodes T, Formation.HeadFormed false t

theorem formed_sites {T : Ty} (formed : NodesFormed T) (path : List String) :
    Formation.Formed (Formation.sites false path T) := by
  intro site member
  obtain ⟨⟨t, i⟩, inside, rfl⟩ := List.mem_map.mp member
  exact formed t (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp inside))

theorem formed_append {a b : List Formation.Site} (ha : Formation.Formed a)
    (hb : Formation.Formed b) : Formation.Formed (a ++ b) := fun site member =>
  (List.mem_append.mp member).elim (ha site) (hb site)

theorem nodesFormed_never : NodesFormed .never := fun t member => by
  rw [List.mem_singleton.mp member]
  exact trivial

theorem nodesFormed_refOf {C : Ty} (formed : NodesFormed C) : NodesFormed (.refOf C) :=
  fun t member => by
    rcases List.mem_cons.mp member with rfl | inside
    · exact trivial
    · exact formed t inside

/-! ## The rows of a cell and of a promise, at the native signature -/

section NativeRows

variable {table : RowTable}

/-- The normal form of a cell's handle type, at a canonical element type. -/
theorem normalize_refOf_canonical {C : Ty} (normal : C.normalize = C) :
    (Ty.refOf C).normalize = .refOf C := by
  show Ty.refOf (Ty.normalize C) = _
  rw [normal]

/-- **`Ref.make`** at a canonical, formed type answers the cell's handle. -/
theorem answers_refMake {value : TermSrc} {s : TypedScope} {C : Ty}
    (normal : C.normalize = C) (formed : NodesFormed C)
    (hvalue : ∀ path, Types (nativeSignature table) value s.env path s.types false C) :
    Answers (nativeSignature table) (Ref.make value) s (.refOf C) := by
  refine answers_perform rfl hvalue ?_
  have matched : Ty.matchTemplate []
      ((nativeSignature table).rowOf .refMake).request.normalize C.normalize = some [(0, C)] := by
    rw [normal]
    exact Ty.matchTemplate_var_first C false
  have sites : Formation.Formed
      (Formation.instantiatedSites ((nativeSignature table).rowOf .refMake) [(0, C)]) :=
    formed_append (formed_append (formed_sites formed _)
      (formed_sites (nodesFormed_refOf formed) _)) (formed_sites nodesFormed_never _)
  refine (rowTy_intro matched rfl sites).trans ?_
  show some (⟨(Ty.refOf C).normalize, Ty.never, Requirement.empty⟩ : EffTy) = _
  rw [normalize_refOf_canonical normal]
  rfl

/-- **`Ref.get`** of a cell at a canonical, formed type answers the cell's value. -/
theorem answers_refGet {cell : TermSrc} {s : TypedScope} {C : Ty}
    (normal : C.normalize = C) (formed : NodesFormed C)
    (hcell : Typed (nativeSignature table) cell s (.refOf C)) :
    Answers (nativeSignature table) (Ref.get cell) s C := by
  refine answers_perform rfl (fun path => hcell path false) ?_
  have matched : Ty.matchTemplate []
      ((nativeSignature table).rowOf .refGet).request.normalize (Ty.refOf C).normalize =
        some [(0, C)] := by
    rw [normalize_refOf_canonical normal]
    refine Ty.matchTemplate_exact ?_ rfl
    show Ty.infer [] (.var 0) C false = [(0, C)]
    exact Ty.infer_var_fresh C false rfl
  have sites : Formation.Formed
      (Formation.instantiatedSites ((nativeSignature table).rowOf .refGet) [(0, C)]) :=
    formed_append (formed_append (formed_sites (nodesFormed_refOf formed) _)
      (formed_sites formed _)) (formed_sites nodesFormed_never _)
  refine (rowTy_intro matched rfl sites).trans ?_
  show some (⟨C.normalize, Ty.never, Requirement.empty⟩ : EffTy) = _
  rw [normal]
  rfl

/-- A binder term binds in its introduction form: it types at the row's parameter, and its type
matches the row's result template. -/
theorem bindTerm_intro {σ σ' : Ty.Subst} {use : TermUse} {r : Ty}
    (typed : use.typeAt ((use.param.normalize.instantiate σ).normalize) = some r)
    (matched : Ty.matchTemplate σ use.result.normalize r = some σ') :
    bindTerm σ (some use) = .ok σ' := by
  simp only [bindTerm, typed, matched]

/-- **`Ref.modifyWith`, with the cell's current value as a caller's term under a fold.** The row
of a cell at a canonical, formed type answers the step's reply. The step's term has the pair of
the reply's type and the cell's type, under the minted name of the cell's current value
(decisions row 257, point 1). The step reads that name through a term that keeps its type under
a fold's two binders: a step may hold the cell's own source in a fold's body. -/
theorem answers_refModifyWith_captured {cell : TermSrc} {f : TermSrc → TermSrc}
    {s : TypedScope} {C B : Ty} (normalC : C.normalize = C) (formedC : NodesFormed C)
    (normalB : B.normalize = B) (formedB : NodesFormed B)
    (hcell : Typed (nativeSignature table) cell s (.refOf C))
    (hstep : ∀ current : TermSrc,
      (∀ path, CapturedTy (nativeSignature table) current (s.push .current C).env path
        (s.push .current C).types C) →
      Typed (nativeSignature table) (f current) (s.push .current C) (.prod B C)) :
    Answers (nativeSignature table) (Ref.modifyWith cell f) s B := by
  intro path
  obtain ⟨r, treeR, typedR⟩ := hcell path false
  obtain ⟨t, treeT, typedT⟩ :=
    hstep _ (fun path => capturedTy_current s.depth path C) path false
  have treeT' : f (minted (s.env.mint "current")) (s.env.push [s.env.mint "current"]) path =
      .ok t := treeT
  have typedT' : termTy (nativeSignature table) (s.types ++ [C]) t = some (.prod B C) := typedT
  have matched : Ty.matchTemplate []
      ((nativeSignature table).rowOf (.refModifyWith t)).request.normalize
      (Ty.refOf C).normalize = some [(0, C)] := by
    rw [normalize_refOf_canonical normalC]
    refine Ty.matchTemplate_exact ?_ rfl
    show Ty.infer [] (.var 0) C false = [(0, C)]
    exact Ty.infer_var_fresh C false rfl
  have inferred : Ty.infer [(0, C)] (.prod (.var 1) (.var 0)) (.prod B C) false =
      [(0, C), (1, B)] := by
    show Ty.infer (Ty.infer [(0, C)] (.var 1) B false) (.var 0) C false = _
    rw [Ty.infer_var_fresh B false rfl]
    show Ty.infer [(0, C), (1, B)] (.var 0) C false = _
    rw [Ty.infer_var_bound C false (bound := C) rfl]
    rfl
  have bound : bindTerm [(0, C)]
      ((nativeSignature table).termUse s.types (.refModifyWith t)) = .ok [(0, C), (1, B)] := by
    refine bindTerm_intro (use := ⟨.var 0, .prod (.var 1) (.var 0),
      fun A => termTy (nativeSignature table) (s.types ++ [A]) t⟩) (r := .prod B C) ?_ ?_
    · show termTy (nativeSignature table) (s.types ++ [C.normalize]) t = _
      rw [normalC]
      exact typedT'
    · have resultNormal : (Ty.prod (.var 1) (.var 0)).normalize = .prod (.var 1) (.var 0) := by
        decide +kernel
      show Ty.matchTemplate [(0, C)] (Ty.prod (.var 1) (.var 0)).normalize (.prod B C) = _
      rw [resultNormal]
      exact Ty.matchTemplate_exact inferred rfl
  have sites : Formation.Formed (Formation.instantiatedSites
      ((nativeSignature table).rowOf (.refModifyWith t)) [(0, C), (1, B)]) :=
    formed_append (formed_append (formed_sites (nodesFormed_refOf formedC) _)
      (formed_sites formedB _)) (formed_sites nodesFormed_never _)
  refine ⟨.perform (.refModifyWith t) r, ?_,
    effTy_complete _ _ _ _ (.perform rfl typedR ((rowTy_intro matched bound sites).trans ?_))⟩
  · show (f (minted (s.env.mint "current")) (s.env.push [s.env.mint "current"]) path >>=
      fun x0 => cell s.env path >>= fun x1 =>
        Except.ok (Eff.perform (NativeOp.refModifyWith x0) x1)) = _
    rw [treeT', treeR]
    rfl
  · show some (⟨B.normalize, Ty.never, Requirement.empty⟩ : EffTy) = _
    rw [normalB]
    rfl

/-- **`Ref.modifyWith`** of a cell at a canonical, formed type answers the step's reply. The
step's term has the pair of the reply's type and the cell's type, under the minted name of the
cell's current value (decisions row 257, point 1). -/
theorem answers_refModifyWith {cell : TermSrc} {f : TermSrc → TermSrc} {s : TypedScope}
    {C B : Ty} (normalC : C.normalize = C) (formedC : NodesFormed C)
    (normalB : B.normalize = B) (formedB : NodesFormed B)
    (hcell : Typed (nativeSignature table) cell s (.refOf C))
    (hstep : ∀ current : TermSrc, Typed (nativeSignature table) current (s.push .current C) C →
      Typed (nativeSignature table) (f current) (s.push .current C) (.prod B C)) :
    Answers (nativeSignature table) (Ref.modifyWith cell f) s B :=
  answers_refModifyWith_captured normalC formedC normalB formedB hcell fun current captured =>
    hstep current fun path => (captured path).atScope

/-- **A hint's type**: the three `Deferred` rows of a wait type at it, with no failure. The
rows are the making of the hint, its await and its completion. -/
structure HintTy (table : RowTable) (H : Ty) : Prop where
  made : ∀ types : TyEnv,
    rowTy ((nativeSignature table).rowOf (.deferredMakeOf H .never)) .unit
      ((nativeSignature table).termUse types (.deferredMakeOf H .never)) =
        some (EffTy.pure (.deferredOf H .never))
  awaited : ∀ types : TyEnv,
    rowTy ((nativeSignature table).rowOf .deferredAwait) (.deferredOf H .never)
      ((nativeSignature table).termUse types .deferredAwait) = some (EffTy.pure H)
  succeeded : ∀ types : TyEnv,
    rowTy ((nativeSignature table).rowOf .deferredSucceed) (.prod (.deferredOf H .never) H)
      ((nativeSignature table).termUse types .deferredSucceed) = some (EffTy.pure .bool)

/-- A hint that carries nothing: a taker's. The completion's row is closed at it, and the
kernel decides its check. -/
theorem hintTy_unit : HintTy table .unit :=
  ⟨fun _ => (by decide +kernel : rowTy (NativeOp.deferredMakeOf .unit .never).row.normalizeTypes
      .unit none = some (EffTy.pure (.deferredOf .unit .never))),
    fun _ => (by decide +kernel : rowTy NativeOp.deferredAwait.row.normalizeTypes
      (.deferredOf .unit .never) none = some (EffTy.pure .unit)),
    fun _ => (by decide +kernel : rowTy NativeOp.deferredSucceed.row.normalizeTypes
      (.prod (.deferredOf .unit .never) .unit) none = some (EffTy.pure .bool))⟩

/-- A hint that carries an offer's decided answer. -/
theorem hintTy_bool : HintTy table .bool :=
  ⟨fun _ => (by decide +kernel : rowTy (NativeOp.deferredMakeOf .bool .never).row.normalizeTypes
      .unit none = some (EffTy.pure (.deferredOf .bool .never))),
    fun _ => (by decide +kernel : rowTy NativeOp.deferredAwait.row.normalizeTypes
      (.deferredOf .bool .never) none = some (EffTy.pure .bool)),
    fun _ => (by decide +kernel : rowTy NativeOp.deferredSucceed.row.normalizeTypes
      (.prod (.deferredOf .bool .never) .bool) none = some (EffTy.pure .bool))⟩

theorem answers_deferredMake {H : Ty} (hint : HintTy table H) (s : TypedScope) :
    Answers (nativeSignature table) (Deferred.make H .never) s (.deferredOf H .never) :=
  answers_perform rfl (fun _ => types_unit false) (hint.made s.types)

theorem answers_deferredAwait {H : Ty} (hint : HintTy table H) {promise : TermSrc}
    {s : TypedScope} (hpromise : Typed (nativeSignature table) promise s (.deferredOf H .never)) :
    Answers (nativeSignature table) (Deferred.await promise) s H :=
  answers_perform rfl (fun path => hpromise path false) (hint.awaited s.types)

theorem answers_deferredSucceed {H : Ty} (hint : HintTy table H) {promise value : TermSrc}
    {s : TypedScope} (hpromise : Typed (nativeSignature table) promise s (.deferredOf H .never))
    (hvalue : Typed (nativeSignature table) value s H) :
    Answers (nativeSignature table) (Deferred.succeed promise value) s .bool :=
  answers_perform rfl (fun path => types_pair rfl (hpromise path) (hvalue path) false)
    (hint.succeeded s.types)

end NativeRows

/-- The nodes of a type that the formation check accepts are formed. -/
theorem nodesFormed_of_check {T : Ty}
    (checked : Formation.check (Formation.sites false [] T) = none) : NodesFormed T := by
  intro t member
  have formed := (Formation.check_eq_none_iff _).mp checked
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp member
  have inside : ((Formation.nodes T)[i], i) ∈ (Formation.nodes T).zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hi)
  exact formed _ (List.mem_map_of_mem inside)

theorem nodesFormed_list {T : Ty} (formed : NodesFormed T) : NodesFormed (.list T) :=
  fun t member => by
    rcases List.mem_cons.mp member with rfl | inside
    · exact trivial
    · exact formed t inside

theorem nodesFormed_option {T : Ty} (formed : NodesFormed T) : NodesFormed (.option T) :=
  fun t member => by
    rcases List.mem_cons.mp member with rfl | inside
    · exact trivial
    · exact formed t inside

/-- `isSome` reads an option of any type. -/
theorem nativeAtomTy_isSome (X : Ty) : nativeAtomTy "isSome" [.option X] = some .bool := by
  show NativeAtom.monoApply [.option .unknown] .bool [.option X] = some .bool
  unfold NativeAtom.monoApply
  refine if_pos ⟨rfl, ?_⟩
  show (Ty.sub (.option X) (.option .unknown) && true) = true
  rw [Ty.sub_option, Ty.sub_unknown]
  rfl

/-! ## Kept terms: literals and a positional read -/

theorem kept_bool (b : Bool) (s : TypedScope) : Kept sig (bool b) s .bool :=
  fun _ _ _ => types_bool b

theorem kept_unit (s : TypedScope) : Kept sig unit s .unit := fun _ _ _ => types_unit

/-- A positional read of a kept term is kept. -/
theorem Kept.tupleAt {target : TermSrc} {index : Nat} {s : TypedScope} {R T : Ty}
    (h : Kept sig target s R) (item : Tuple.typeAt R index = some T) :
    Kept sig (tupleAt target index) s T :=
  fun t reach path _ => types_tupleAt (h t reach path false) item

/-- The join of two canonical types below a canonical type is below it, in the checker's
order. -/
theorem subN_join_of_canonical {a b c : Ty} (ha : a.normalize = a) (hb : b.normalize = b)
    (hc : c.normalize = c) (hac : Ty.sub a c = true) (hbc : Ty.sub b c = true) :
    Ty.subN (Ty.join a b) c = true := by
  unfold Ty.subN
  rw [Ty.normalize_join, hc]
  exact Ty.join_least ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ hac hbc

/-- **The join of a canonical type with a canonical type below it is the first.** The join is
above the first and below it, and the order is antisymmetric on canonical types. Its consumer is
an operation whose two arms answer one type and a type below it: an option of an answer beside
the empty option. -/
theorem join_absorb {a b : Ty} (ha : a.normalize = a) (hb : b.normalize = b)
    (below : Ty.sub b a = true) : Ty.join a b = a :=
  congrArg CTy.toRaw
    (Ty.sub_antisymm_canonical (CTy.join ⟨a, ha⟩ ⟨b, hb⟩) ⟨a, ha⟩
      (Ty.join_least ⟨a, ha⟩ ⟨b, hb⟩ ⟨a, ha⟩ (Ty.sub_refl a) below)
      (Ty.sub_join_left ⟨a, ha⟩ ⟨b, hb⟩))

/-- The two empty columns of a pure program leave a failure type in normal form as it is. -/
theorem join_never_normal (E : Ty) : Ty.never.join E.normalize = E.normalize :=
  (Ty.join_never _).trans (Ty.normalize_idem E)

/-! ## The shared pieces of a module that waits -/

section Pieces

variable {table : RowTable}

/-- **The posted helpers of a list answer a number**: the count of the loop. Each request holds
a hint at the answer's type, and each helper completes one hint. The requests and the answer
are kept terms: the loop reads them under its own binders. -/
theorem postAll_answers {requests answer : TermSrc} {s : TypedScope} {E H : Ty}
    (hint : HintTy table H) (canonical : E.normalize = E)
    (hintField : Record.fieldType false E "hint" = some (.deferredOf H .never))
    (hrequests : Kept (nativeSignature table) requests s (.list E))
    (hanswer : Kept (nativeSignature table) answer s H) :
    Answers (nativeSignature table) (postAll requests answer) s .nat := by
  have joined : Ty.join .unit .unit = .unit := by decide +kernel
  have succTy : nativeAtomTy "succ" [.nat] = some .nat := NativeAtom.monoApply_self [.nat] .nat
  refine answers_iterateWith (C0 := .nat) (C := .nat) (B := .unit) (C1 := .nat) (D := .nat) rfl
    (fun _ => types_nat 0) ?_ ?_ ?_ (fun _ hc => hc) (Ty.subN_refl _) (Ty.subN_refl _)
  · intro c hc path
    exact types_lt rfl (hc path) (types_len rfl (hrequests.push.here path))
  · intro c hc
    have body := answers_selectOptionWith (sig := nativeSignature table)
      (scrutinee := app "get" [requests, c]) (arm0 := succeed unit) (X := .unit) (Y := .unit)
      (arm1 := fun request => andThen
        (withFiber (Action.fork (Deferred.succeed (field request "hint") answer) posted))
        (succeed unit))
      canonical
      (fun path _ => types_app (.cons (hrequests.push.here path _) (.cons (hc path _) .nil))
        (nativeAtomTy_get E))
      (answers_succeed fun _ => types_unit)
      (fun request hrequest => answers_andThen
        (answers_fork (answers_deferredSucceed hint
          (fun path _ => types_field (hrequest path false) hintField)
          hanswer.push.push.here))
        (answers_succeed fun _ => types_unit))
    rw [joined] at body
    exact body
  · intro c a hc _ path _
    exact types_app (.cons (hc path _) .nil) succTy

/-- **The cleanup on interruption answers as its body.** The cleanup's own answer is
discarded. -/
theorem onInterrupt_answers {body cleanup : Src NativeOp} {s : TypedScope} {X F : Ty}
    (test : nativeAtomTy "causeIsInterrupt" [.exitOf X .never] = some .bool)
    (hbody : Answers (nativeSignature table) body s X)
    (hcleanup : Answers (nativeSignature table) cleanup (s.push .exit (.exitOf X .never)) F) :
    Answers (nativeSignature table) (onInterrupt body cleanup) s X :=
  answers_onExitWith hbody fun _ hexit =>
    answers_ifElse (fun path _ => types_app (.cons (hexit path _) .nil) test) hcleanup
      (answers_succeed fun _ => types_unit)

/-- **The wait at a mask's restore site answers the hint's value.** -/
theorem waitAt_answers {restore : Src NativeOp → Src NativeOp} {hint : TermSrc}
    {withdraw : Src NativeOp} {s : TypedScope} {H F : Ty} (hintTy : HintTy table H)
    (test : nativeAtomTy "causeIsInterrupt" [.exitOf H .never] = some .bool)
    (hrestore : ∀ (inner : Src NativeOp) (Y : Ty),
      Answers (nativeSignature table) inner s Y → Answers (nativeSignature table) (restore inner) s Y)
    (hhint : Typed (nativeSignature table) hint s (.deferredOf H .never))
    (hwithdraw : Answers (nativeSignature table) withdraw (s.push .exit (.exitOf H .never)) F) :
    Answers (nativeSignature table) (waitAt restore hint withdraw) s H :=
  onInterrupt_answers test (hrestore _ _ (answers_deferredAwait hintTy hhint)) hwithdraw

/-! ### The wrapper's forms, typed over a module's part (decisions row 275, point 3)

A module's part of the wrapper is a `Waiter`, whose attempt is a function of its two exits. Its
typing says what the attempt answers from what the two exits answer: their join. The Queue's
`take` chooses by an option, and Semaphore's by a Boolean: both answer that join. -/

/-- **A module's part of the wrapper, typed at a result type** `R`, at every scope that the
surface's binders reach from `s`. `F` is what the withdrawal answers.

- The hint's three rows type, and so does the test of an interrupted wait's exit.
- The attempt answers the join of what its two exits answer. It reads the identity and the hint
  through kept terms. Its `wait` answers one type at every scope that the attempt reaches, and
  its `done` answers one type for every answer of the result type.
- The withdrawal answers one type, for every kept identity. -/
structure Waiter.Typed (table : RowTable) (w : Waiter) (s : TypedScope) (R F : Ty) : Prop where
  hint : HintTy table w.hint
  interrupted : nativeAtomTy "causeIsInterrupt" [.exitOf w.hint .never] = some .bool
  attempt : ∀ (t : TypedScope) (id hint : TermSrc) (wait : Src NativeOp)
    (done : TermSrc → Src NativeOp) (W D : Ty), s.Reaches t →
    Kept (nativeSignature table) id t idTy →
    Kept (nativeSignature table) hint t (.deferredOf w.hint .never) →
    (∀ u : TypedScope, t.Reaches u → Answers (nativeSignature table) wait u W) →
    (∀ (u : TypedScope) (answer : TermSrc), t.Reaches u →
      Effect4.Modules.Typed (nativeSignature table) answer u R →
        Answers (nativeSignature table) (done answer) u D) →
    Answers (nativeSignature table) (w.attempt id hint wait done) t (Ty.join W D)
  withdraw : ∀ (t : TypedScope) (id : TermSrc), s.Reaches t →
    Kept (nativeSignature table) id t idTy →
      Answers (nativeSignature table) (w.withdraw id) t F

/-- **The loop at a caller's restore answers the result**, where the module's part is typed and
the caller's restore keeps what its argument answers, at every scope that the surface's binders
reach. The result type is its own normal form. -/
theorem waitRetryAt_answers {restore : Src NativeOp → Src NativeOp} {result : Ty}
    {ended : String} {w : Waiter} {s : TypedScope} {F : Ty}
    (canonical : result.normalize = result)
    (hrestore : ∀ (t : TypedScope) (inner : Src NativeOp) (Y : Ty), s.Reaches t →
      Answers (nativeSignature table) inner t Y →
        Answers (nativeSignature table) (restore inner) t Y)
    (hw : w.Typed table s result F) :
    Answers (nativeSignature table) (waitRetryAt restore result ended w) s result := by
  have optionNormal : (Ty.option result).normalize = .option result :=
    Ty.normalize_option_canonical canonical
  have noneBelow : Ty.sub (.option .never) (.option result) = true := by
    rw [Ty.sub_option]
    exact Ty.OrderProof.sub_never result
  have final : Ty.join .never result = result := (Ty.join_never result).trans canonical
  have whole : Answers (nativeSignature table) (waitRetryAt restore result ended w) s
      (Ty.join .never result) := by
    unfold waitRetryAt
    refine answers_bindWith (answers_deferredMake hintTy_unit _) fun id hid => ?_
    refine answers_bindWith (X := .option result) ?_ fun _ hlast =>
      answers_selectOptionWith canonical (fun path => hlast.here path) (answers_die _ _)
        fun _ hanswer => answers_succeed hanswer
    refine answers_iterateWith (C0 := .option .never) (C := .option result)
      (B := Ty.join (.option .never) (.option result))
      (C1 := Ty.join (.option .never) (.option result)) (D := .option result) rfl
      (fun _ => types_noneT rfl) ?_ ?_ (fun _ _ _ ha => ha) (fun _ hc => hc) ?_
      (subN_join_of_canonical rfl optionNormal optionNormal noneBelow (Ty.sub_refl _))
    · intro c hc path
      exact types_notT rfl fun _ =>
        types_app (.cons (hc path _) .nil) (nativeAtomTy_isSome result)
    · intro _ _
      dsimp only
      refine answers_bindWith (answers_deferredMake hw.hint _) fun hint hhint => ?_
      refine hw.attempt _ id hint _ _ (.option .never) (.option result)
        (.push _ _ (.push _ _ (.push _ _ .here))) hid.push.push hhint ?_ ?_
      · intro u reach
        refine answers_andThen
          (waitAt_answers (F := F) hw.hint hw.interrupted
            (fun inner Y h => hrestore u inner Y
              (TypedScope.Reaches.trans (.push _ _ (.push _ _ (.push _ _ .here))) reach) h)
            (hhint u reach) ?_)
          (answers_succeed fun _ => types_noneT rfl)
        exact hw.withdraw _ id
          (TypedScope.Reaches.trans (.push _ _ (.push _ _ (.push _ _ .here)))
            (.push _ _ reach))
          ((hid.push.push).reach (.push _ _ reach))
      · intro u answer _ hanswer
        exact answers_succeed fun path => types_some rfl (hanswer path)
    · show Ty.sub (Ty.option .never).normalize (Ty.option result).normalize = true
      rw [optionNormal]
      exact noneBelow
  rw [final] at whole
  exact whole

/-- **The wrapper answers the result**, where the module's part is typed under the mask's saved
state. -/
theorem waitRetry_answers {result : Ty} {ended : String} {w : Waiter} {s : TypedScope} {F : Ty}
    (canonical : result.normalize = result)
    (hw : w.Typed table (s.push .restore Ty.maskRestore) result F) :
    Answers (nativeSignature table) (waitRetry result ended w) s result := by
  unfold waitRetry
  exact answers_maskWith fun _ hrestore => waitRetryAt_answers canonical hrestore hw

/-- **The protected body has its body's effect type**, with the failure type in normal form.
The acquisition answers a type with no failure, for every restore function that keeps what its
argument answers. The body has one effect type for every kept reader of the acquired value: it
may fail, and it may require a service. The release answers a type with no failure, under the
body's exit. -/
theorem protectedBy_has {acquire : (Src NativeOp → Src NativeOp) → Src NativeOp}
    {release body : TermSrc → Src NativeOp} {s : TypedScope} {G F : Ty} {b : EffTy}
    (hacquire : ∀ restore : Src NativeOp → Src NativeOp,
      (∀ (t : TypedScope) (inner : Src NativeOp) (Y : Ty),
        (s.push .restore Ty.maskRestore).Reaches t →
          Answers (nativeSignature table) inner t Y →
            Answers (nativeSignature table) (restore inner) t Y) →
      Answers (nativeSignature table) (acquire restore) (s.push .restore Ty.maskRestore) G)
    (hbody : ∀ got : TermSrc,
      Kept (nativeSignature table) got ((s.push .restore Ty.maskRestore).push .answer G) G →
        Has (nativeSignature table) (body got)
          ((s.push .restore Ty.maskRestore).push .answer G) b)
    (hrelease : ∀ got : TermSrc,
      Kept (nativeSignature table) got ((s.push .restore Ty.maskRestore).push .answer G) G →
        Answers (nativeSignature table) (release got)
          (((s.push .restore Ty.maskRestore).push .answer G).push .exit
            (.exitOf b.answer b.error)) F) :
    Has (nativeSignature table) (protectedBy acquire release body) s
      ⟨b.answer, b.error.normalize, b.requires⟩ := by
  unfold protectedBy
  refine (has_maskWith fun restore hrestore =>
    has_bindWith (f := EffTy.pure G)
      (hacquire restore fun t inner Y reach h => hrestore t inner _ reach h)
      fun got hgot =>
        has_onExitWith (f := EffTy.pure F)
          (hrestore _ _ _ (.push _ _ .here) (hbody got hgot)) fun _ _ => hrelease got hgot).to ?_
  show (⟨b.answer, Ty.never.join (Ty.never.join (b.error.join .never)),
    Requirement.empty.union (Requirement.empty.union (b.requires.union Requirement.empty))⟩ :
      EffTy) = _
  rw [Ty.join_never_right, join_never_normal, join_never_normal]
  simp only [Requirement.empty, Requirement.union, Row.union_empty_left, Row.union_empty_right]

end Pieces

end Typing

end Effect4.Modules
