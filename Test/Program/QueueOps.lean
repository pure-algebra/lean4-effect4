import Test.Program.QueueScenarios
import Test.Program.QueueSteps
import Effect4.Laws.Modules.Queue.Ops
import ProofGraph.Plan

/-!
# The Queue's operations: the finite controls of the library module (rows 233, 242 and 255)

The module is `src/Effect4/Modules/Queue/Ops.lean`, over the shared waiting wrapper
(`src/Effect4/Modules/Waiting.lean`). The eight scenarios and the masked caller are
`Test/Program/QueueScenarios.lean` and `Test/Program/QueueMask.lean`. This battery holds the
controls of the operations that those do not run, and of the module's laws.

1. **The construction refuses a capacity of zero** where an author writes the queue.
2. **`Queue.poll`** on the machine: an empty queue, a buffered message, a waiting taker
   (decisions row 242) and a pending offer that the poll's step accepts.
3. **Scope.** A client's program over the operations keeps the authoring scope judgment, by
   `authoring_scoped`: each operation's law is found by its name.
4. **The attempt laws at the wrapper's own binders.** Each law's second form takes two premises
   for each minted name: the row's scope binds it, and no later binder shadows it
   (`src/Effect4/Laws/Modules/Queue/Ops.lean`). The wrapper's own binders meet both, at every
   caller's scope: proved here, with each scope written out. And each statement's term is the
   term of the operation's own row: tested, on the trees that the operations elaborate to.
5. **Hygiene.** The fixtures wrote the names `id`, `hint`, `r`, `e` and `s` around a caller's
   variable. For each name, a caller's variable of that name keeps its reading in the library's
   operation, and the fixture's written form is the red control.
6. **Typing at every scope.** Each operation's typing statement, read at a caller's variables,
   and the checker's own answer on each operation's tree: at 27 message types and three scopes.
   The red controls are a message of another type, a handle of another type and a cell of
   another message type.
7. **The example of `README.md`**, with its checked answer.

Placement. Each run is a finite control of the proposed claim `queue-expansion-agrees` (concept
`translation-simulation`, requirement R10), on the side of the operations' use in a program.
Every guard is one run on one schedule. None proves delivery, a cancellation law or liveness,
and none is a host run. The theorems of section 4 are helpers of the same claim: they discharge
the scope premises of the attempt laws, and they state nothing of a run. Section 6 is the finite
control of the typing statements (concept `store-typing`, requirement R4): each guard is the
checker's answer on one tree, and it states no run.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Test.Program.QueueOps

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Test.Program.QueueScenarios (mk verdict exitOf exitAt typesOf bytesOf)
open Effect4.Modules

/-! ## 1. The construction: a positive capacity -/

-- A positive capacity is written as a literal, and the proof is found by `decide`.
#guard verdict (Queue.bounded .nat 1) = "built"
#guard typesOf (Queue.bounded .nat 3) = some (.refOf (Queue.cellTy .nat), .never)

/--
error: could not synthesize default value for parameter '_positive' using tactics
---
error: Tactic `decide` proved that the proposition
  0 < 0
is false
-/
#guard_msgs in
example : Src NativeOp := Queue.bounded .nat 0

/-! ## 2. `Queue.poll` on the machine -/

/-- An empty queue: the poll answers nothing. -/
def pollEmpty : Src NativeOp := eff do
  let q ← Queue.bounded .nat 2
  let x ← Queue.poll .nat q
  return x

/-- One buffered message and no taker: the first poll takes it, and the second finds nothing. -/
def pollOne : Src NativeOp := eff do
  let q ← Queue.bounded .nat 2
  let _ ← Queue.offer .nat q (nat 4)
  let x ← Queue.poll .nat q
  let y ← Queue.poll .nat q
  return tuple [x, y]

/-- **A poll passes no waiting taker** (decisions row 242). A taker waits. An offer buffers the
message 1 and posts the taker's wake. Before the helper runs, the root polls: the taker is still
enrolled, so the poll takes nothing, and the buffer still holds one message. The taker then
takes it. The answer: the poll, the size after it, the taker's message, and a last poll. -/
def pollBehindTaker : Src NativeOp := eff do
  let q ← Queue.bounded .nat 2
  let f ← fork (Queue.take .nat q)
  let _ ← Queue.offer .nat q (nat 1)
  let x ← Queue.poll .nat q
  let n ← Queue.size .nat q
  let y ← join f
  let z ← Queue.poll .nat q
  return tuple [x, n, y, z]

/-- **A poll that frees room accepts a pending offer**, and the offer's answer is posted.
Capacity one: a first offer is accepted, and a second waits. The poll takes the first message
and accepts the second offer. The offerer's answer is `true`, the buffer then holds one message,
and a last poll takes it. -/
def pollAccepts : Src NativeOp := eff do
  let q ← Queue.bounded .nat 1
  let a ← Queue.offer .nat q (nat 1)
  let f ← fork (Queue.offer .nat q (nat 2))
  let x ← Queue.poll .nat q
  let b ← join f
  let n ← Queue.size .nat q
  let y ← Queue.poll .nat q
  return tuple [a, x, b, n, y]

#guard [pollEmpty, pollOne, pollBehindTaker, pollAccepts].map verdict =
  List.replicate 4 "built"
-- A poll answers an option of a message, and it cannot fail.
#guard typesOf pollEmpty = some (.option .nat, .never)

#guard exitOf pollEmpty = some (.success .none)
#guard exitOf pollOne = some (.success (.list [.some (.nat 4), .none]))
-- The poll behind a waiting taker takes nothing, and the message stays for the taker.
#guard exitOf pollBehindTaker = some (.success (.list [.none, .nat 1, .nat 1, .none]))
#guard exitOf pollAccepts =
  some (.success (.list [.bool true, .some (.nat 1), .bool true, .nat 1, .some (.nat 2)]))
-- The ordinary run gives each answer at the truth lane's fuel.
#guard [pollEmpty, pollOne, pollBehindTaker, pollAccepts].all fun src =>
  (exitAt 1000 src).isSome && exitAt 1000 src == exitOf src

-- The model answers the same at the two states of `pollBehindTaker` and `pollOne`: with a
-- waiting taker the poll takes nothing, and with none it takes the message.
#guard (Queue.Model.poll
  { capacity := some 2, messages := [1], takers := [⟨7, 1, 1⟩] }).2.1 = none
#guard (Queue.Model.poll { capacity := some 2, messages := [1] }).2.1 = some 1
-- Red control of the pins: the same poll with no taker waiting takes the message.
#guard exitOf pollBehindTaker != some (.success (.list [.some (.nat 1), .nat 0, .nat 1, .none]))

/-! ## 3. Scope: a client's program over the operations -/

open Test.Program.QueueScenarios (r4 r4With library) in
/-- R4 keeps the scope judgment: `authoring_scoped` finds each operation's law by its name. -/
theorem r4_scoped : (r4 : Src NativeOp).Scoped := by
  unfold r4 r4With library
  authoring_scoped

/-- A program that polls and reads the size keeps the scope judgment. -/
theorem pollAccepts_scoped : (pollAccepts : Src NativeOp).Scoped := by
  unfold pollAccepts
  authoring_scoped

/-- So the tree that R4 elaborates to is closed (`elaborate_scoped`). -/
example (e : Eff NativeOp) (h : elaborate Test.Program.QueueScenarios.r4 = .ok e) :
    Eff.scopedAt 0 e = true :=
  elaborate_scoped r4_scoped h

/-! ## 4. The attempt laws at the wrapper's own binders

The second form of each attempt law takes two premises for each minted name: the row's scope
binds the name, and no later binder of the scope shadows it. Below, each scope of the wrapper is
written out as a function of the caller's scope, binder by binder. Each theorem proves the two
premises there, at every caller's scope. Then each law applies with no premise on a name. -/

section OwnBinders

open Effect4.Program.Typed
open Effect4.Queue.Model (FirstProfile Requested MessageTy cellVal)

/-- Under the mask: the saved state's name. -/
def masked (caller : Env) : Env := caller.push [caller.mint "restore"]

/-- Under the request's identity. Its name is `(masked caller).mint "answer"`. -/
def named (caller : Env) : Env := (masked caller).push [(masked caller).mint "answer"]

/-- `take`: under the loop's cursor. -/
def looped (caller : Env) : Env := (named caller).push [(named caller).mint "cursor"]

/-- `take`: the scope of the attempt's row, under the round's hint. The hint's name is
`(looped caller).mint "answer"`. -/
def takeRow (caller : Env) : Env := (looped caller).push [(looped caller).mint "answer"]

/-- `take`: under the step's reply. -/
def takeReplied (caller : Env) : Env := (takeRow caller).push [(takeRow caller).mint "answer"]

/-- `take`: under the discarded answer of the first post. -/
def takePosted (caller : Env) : Env :=
  (takeReplied caller).push [(takeReplied caller).mint "answer"]

/-- `take`: under the discarded answer of the second post. The wait stands here. -/
def takeWaiting (caller : Env) : Env :=
  (takePosted caller).push [(takePosted caller).mint "answer"]

/-- `take`: the scope of the withdrawal's row, under the wait's exit. -/
def takeWithdrawRow (caller : Env) : Env :=
  (takeWaiting caller).push [(takeWaiting caller).mint "exit"]

/-- `offer`: the scope of the attempt's row, under the hint. The hint's name is
`(named caller).mint "answer"`. -/
def offerRow (caller : Env) : Env := (named caller).push [(named caller).mint "answer"]

/-- `offer`: under the step's reply. -/
def offerReplied (caller : Env) : Env :=
  (offerRow caller).push [(offerRow caller).mint "answer"]

/-- `offer`: under the discarded answer of the post. The wait stands here. -/
def offerWaiting (caller : Env) : Env :=
  (offerReplied caller).push [(offerReplied caller).mint "answer"]

/-- `offer`: the scope of the withdrawal's row, under the wait's exit. -/
def offerWithdrawRow (caller : Env) : Env :=
  (offerWaiting caller).push [(offerWaiting caller).mint "exit"]

/-- **`take`'s attempt: the row's scope binds the identity, and no later binder shadows it.**
The later binders are the loop's cursor and the round's hint. -/
theorem takeRow_identity (caller : Env) :
    (takeRow caller).names = (masked caller).names ++ (masked caller).mint "answer" ::
        [(named caller).mint "cursor", (looped caller).mint "answer"] ∧
      ∀ name ∈ [(named caller).mint "cursor", (looped caller).mint "answer"],
        name ≠ (masked caller).mint "answer" := by
  refine ⟨by simp only [takeRow, looped, named, Env.push, List.append_assoc, List.cons_append,
    List.nil_append], fun name member => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact later_mint_ne_answer (b := 99)
      (by simp only [named, Env.push_length, List.length_cons, List.length_nil]; omega)
      (by decide) (Or.inr (by decide))
  · exact later_mint_ne_answer (b := 97)
      (by simp only [looped, named, Env.push_length, List.length_cons, List.length_nil]; omega)
      (by decide) (Or.inl rfl)

/-- **`take`'s attempt: the row's scope binds the hint last**, so no later binder exists. -/
theorem takeRow_hint (caller : Env) :
    (takeRow caller).names = (looped caller).names ++ (looped caller).mint "answer" :: [] ∧
      ∀ name ∈ ([] : Names), name ≠ (looped caller).mint "answer" :=
  ⟨rfl, fun _ member => absurd member List.not_mem_nil⟩

/-- **`take`'s withdrawal: the row's scope binds the identity, and no later binder shadows
it.** The later binders are the cursor, the hint, the reply, two discarded answers and the
wait's exit. -/
theorem takeWithdrawRow_identity (caller : Env) :
    (takeWithdrawRow caller).names = (masked caller).names ++ (masked caller).mint "answer" ::
        [(named caller).mint "cursor", (looped caller).mint "answer",
          (takeRow caller).mint "answer", (takeReplied caller).mint "answer",
          (takePosted caller).mint "answer", (takeWaiting caller).mint "exit"] ∧
      ∀ name ∈ [(named caller).mint "cursor", (looped caller).mint "answer",
          (takeRow caller).mint "answer", (takeReplied caller).mint "answer",
          (takePosted caller).mint "answer", (takeWaiting caller).mint "exit"],
        name ≠ (masked caller).mint "answer" := by
  refine ⟨by simp only [takeWithdrawRow, takeWaiting, takePosted, takeReplied, takeRow, looped,
    named, Env.push, List.append_assoc, List.cons_append, List.nil_append],
    fun name member => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact later_mint_ne_answer (b := 99)
      (by simp only [named, Env.push_length, List.length_cons, List.length_nil]; omega)
      (by decide) (Or.inr (by decide))
  · exact later_mint_ne_answer (b := 97)
      (by simp only [looped, named, Env.push_length, List.length_cons, List.length_nil]; omega)
      (by decide) (Or.inl rfl)
  · exact later_mint_ne_answer (b := 97)
      (by simp only [takeRow, looped, named, Env.push_length, List.length_cons,
        List.length_nil]; omega)
      (by decide) (Or.inl rfl)
  · exact later_mint_ne_answer (b := 97)
      (by simp only [takeReplied, takeRow, looped, named, Env.push_length, List.length_cons,
        List.length_nil]; omega)
      (by decide) (Or.inl rfl)
  · exact later_mint_ne_answer (b := 97)
      (by simp only [takePosted, takeReplied, takeRow, looped, named, Env.push_length,
        List.length_cons, List.length_nil]; omega)
      (by decide) (Or.inl rfl)
  · exact later_mint_ne_answer (b := 101)
      (by simp only [takeWaiting, takePosted, takeReplied, takeRow, looped, named,
        Env.push_length, List.length_cons, List.length_nil]; omega)
      (by decide) (Or.inr (by decide))

/-- **`offer`'s attempt: the row's scope binds the identity, and the hint does not shadow
it.** -/
theorem offerRow_identity (caller : Env) :
    (offerRow caller).names = (masked caller).names ++ (masked caller).mint "answer" ::
        [(named caller).mint "answer"] ∧
      ∀ name ∈ [(named caller).mint "answer"], name ≠ (masked caller).mint "answer" := by
  refine ⟨by simp only [offerRow, named, Env.push, List.append_assoc, List.cons_append,
    List.nil_append], fun name member => ?_⟩
  rw [List.mem_singleton.mp member]
  exact later_mint_ne_answer (b := 97)
    (by simp only [named, Env.push_length, List.length_cons, List.length_nil]; omega)
    (by decide) (Or.inl rfl)

/-- **`offer`'s attempt: the row's scope binds the hint last.** -/
theorem offerRow_hint (caller : Env) :
    (offerRow caller).names = (named caller).names ++ (named caller).mint "answer" :: [] ∧
      ∀ name ∈ ([] : Names), name ≠ (named caller).mint "answer" :=
  ⟨rfl, fun _ member => absurd member List.not_mem_nil⟩

/-- **`offer`'s withdrawal: the row's scope binds the identity, and no later binder shadows
it.** The later binders are the hint, the reply, one discarded answer and the wait's exit. -/
theorem offerWithdrawRow_identity (caller : Env) :
    (offerWithdrawRow caller).names = (masked caller).names ++ (masked caller).mint "answer" ::
        [(named caller).mint "answer", (offerRow caller).mint "answer",
          (offerReplied caller).mint "answer", (offerWaiting caller).mint "exit"] ∧
      ∀ name ∈ [(named caller).mint "answer", (offerRow caller).mint "answer",
          (offerReplied caller).mint "answer", (offerWaiting caller).mint "exit"],
        name ≠ (masked caller).mint "answer" := by
  refine ⟨by simp only [offerWithdrawRow, offerWaiting, offerReplied, offerRow, named, Env.push,
    List.append_assoc, List.cons_append, List.nil_append], fun name member => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact later_mint_ne_answer (b := 97)
      (by simp only [named, Env.push_length, List.length_cons, List.length_nil]; omega)
      (by decide) (Or.inl rfl)
  · exact later_mint_ne_answer (b := 97)
      (by simp only [offerRow, named, Env.push_length, List.length_cons, List.length_nil]; omega)
      (by decide) (Or.inl rfl)
  · exact later_mint_ne_answer (b := 97)
      (by simp only [offerReplied, offerRow, named, Env.push_length, List.length_cons,
        List.length_nil]; omega)
      (by decide) (Or.inl rfl)
  · exact later_mint_ne_answer (b := 101)
      (by simp only [offerWaiting, offerReplied, offerRow, named, Env.push_length,
        List.length_cons, List.length_nil]; omega)
      (by decide) (Or.inr (by decide))

-- Red control of the premise: where a later binder has the identity's own name, the name
-- resolves to the later level, and a step would read that binder's value there.
#guard Names.resolve
  ((masked {}).names ++ [(masked {}).mint "answer", "x", (masked {}).mint "answer"])
  ((masked {}).mint "answer") == some 3
-- With no such binder it resolves to its own level, one above the mask's saved state.
#guard Names.resolve ((masked {}).names ++ [(masked {}).mint "answer", "x"])
  ((masked {}).mint "answer") == some 1

/-! Each law at the wrapper's own binders. The premises that stay are the caller's context: the
typed environment, the request's two handles at their levels, the cell's value and its
membership. No premise on a name stays. Each example's conclusion is its law's. -/

/-- `take`'s attempt at its own binders. -/
example (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy) (A : Ty)
    (message : MessageTy A) (tb : Table) (msg : Nat → Val) (s : Queue.Model.State) (id : Nat)
    (hint : DeferredKey) (profile : FirstProfile s) (requested : Requested s (.take id 1 1))
    (injective : tb.Injective) (caller : Env) (path : List Nat) (tys : List Ty)
    (w : Typed.World) (captured : List Val)
    (depth : captured.length = (takeRow caller).names.length)
    (tyDepth : tys.length = (takeRow caller).names.length) (typedEnv : EnvTyped w tys captured)
    (idHeld : captured[(masked caller).names.length]? = some (Val.promise (tb.handle id)))
    (idTyped : tys[(masked caller).names.length]? = some idTy)
    (hintHeld : captured[(looped caller).names.length]? = some (Val.promise hint))
    (hintTyped : tys[(looped caller).names.length]? = some idTy)
    (stores : Stores) (q : RefKey) (held : refPeek stores.refs q = some (cellVal tb msg s))
    (member : Fits w (cellVal tb msg s) (Queue.cellTy A)) :=
  Queue.take_attempt_minted sig atoms A message tb msg s id hint profile requested injective
    (path := path) depth tyDepth typedEnv (takeRow_identity caller).1 (takeRow_identity caller).2
    idHeld idTyped (takeRow_hint caller).1 (takeRow_hint caller).2 hintHeld hintTyped held member

/-- `take`'s withdrawal at its own binders. -/
example (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy) (A : Ty)
    (message : MessageTy A) (tb : Table) (msg : Nat → Val) (s : Queue.Model.State) (id : Nat)
    (profile : FirstProfile s) (injective : tb.Injective) (caller : Env) (path : List Nat)
    (tys : List Ty) (w : Typed.World) (captured : List Val)
    (depth : captured.length = (takeWithdrawRow caller).names.length)
    (tyDepth : tys.length = (takeWithdrawRow caller).names.length)
    (typedEnv : EnvTyped w tys captured)
    (idHeld : captured[(masked caller).names.length]? = some (Val.promise (tb.handle id)))
    (idTyped : tys[(masked caller).names.length]? = some idTy)
    (stores : Stores) (q : RefKey) (held : refPeek stores.refs q = some (cellVal tb msg s))
    (member : Fits w (cellVal tb msg s) (Queue.cellTy A)) :=
  Queue.take_withdrawal_minted sig atoms A message tb msg s id profile injective (path := path)
    depth tyDepth typedEnv (takeWithdrawRow_identity caller).1
    (takeWithdrawRow_identity caller).2 idHeld idTyped held member

/-- `offer`'s attempt at its own binders. The message is a variable that the caller reads
through `var`: it keeps its level under the row's own binder (`var_push_minted`). -/
example (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy) (A : Ty)
    (message : MessageTy A) (tb : Table) (msg : Nat → Val) (s : Queue.Model.State) (id a : Nat)
    (hint : DeferredKey) (profile : FirstProfile s) (requested : Requested s (.offer id a))
    (fresh : ∀ o ∈ s.offers, o.id ≠ id) (caller : Env) (path : List Nat) (tys : List Ty)
    (w : Typed.World) (captured : List Val) (x : String) (level : Nat)
    (written : Name.reserved x = false)
    (bound : (offerRow caller).names.resolve x = some level)
    (depth : captured.length = (offerRow caller).names.length)
    (tyDepth : tys.length = (offerRow caller).names.length) (typedEnv : EnvTyped w tys captured)
    (idHeld : captured[(masked caller).names.length]? = some (Val.promise (tb.handle id)))
    (idTyped : tys[(masked caller).names.length]? = some idTy)
    (hintHeld : captured[(named caller).names.length]? = some (Val.promise hint))
    (hintTyped : tys[(named caller).names.length]? = some Queue.answerTy)
    (messageHeld : captured[level]? = some (msg a)) (messageTyped : tys[level]? = some A)
    (stores : Stores) (q : RefKey) (held : refPeek stores.refs q = some (cellVal tb msg s))
    (member : Fits w (cellVal tb msg s) (Queue.cellTy A)) :=
  have pushed : ((offerRow caller).push [(offerRow caller).mint "current"]).names.resolve x =
      some level :=
    (Names.resolve_append_ne (fun same => written_ne_mint written _ "current" same.symm)
      (offerRow caller).names).trans bound
  have inside : level < captured.length := (List.getElem?_eq_some_iff.mp messageHeld).1
  have insideTy : level < tys.length := (List.getElem?_eq_some_iff.mp messageTyped).1
  Queue.offer_attempt_minted sig atoms A message tb msg s id a hint profile requested fresh
    (path := path) (messageSrc := var x) depth tyDepth typedEnv (offerRow_identity caller).1
    (offerRow_identity caller).2 idHeld idTyped (offerRow_hint caller).1 (offerRow_hint caller).2
    hintHeld hintTyped
    ⟨.var level, var_tree written pushed path,
      (List.getElem?_append_left inside).trans messageHeld⟩
    (types_var written pushed ((List.getElem?_append_left insideTy).trans messageTyped))
    held member

/-- `offer`'s withdrawal at its own binders. -/
example (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy) (A : Ty)
    (message : MessageTy A) (tb : Table) (msg : Nat → Val) (s : Queue.Model.State) (id : Nat)
    (profile : FirstProfile s) (injective : tb.Injective) (caller : Env) (path : List Nat)
    (tys : List Ty) (w : Typed.World) (captured : List Val)
    (depth : captured.length = (offerWithdrawRow caller).names.length)
    (tyDepth : tys.length = (offerWithdrawRow caller).names.length)
    (typedEnv : EnvTyped w tys captured)
    (idHeld : captured[(masked caller).names.length]? = some (Val.promise (tb.handle id)))
    (idTyped : tys[(masked caller).names.length]? = some idTy)
    (stores : Stores) (q : RefKey) (held : refPeek stores.refs q = some (cellVal tb msg s))
    (member : Fits w (cellVal tb msg s) (Queue.cellTy A)) :=
  Queue.offer_withdrawal_minted sig atoms A message tb msg s id profile injective (path := path)
    depth tyDepth typedEnv (offerWithdrawRow_identity caller).1
    (offerWithdrawRow_identity caller).2 idHeld idTyped held member

end OwnBinders

/-! ### Each statement's term is the term of the operation's own row

The scopes above are written by hand, binder by binder. The guards below bind them to the
operations: at each caller's scope, the term that the operation's tree holds in its row is the
tree of the statement's term at the scope that the statement names. A scope with one binder
too many or too few gives another tree, so the guard fails. -/

/-- The tree of an operation at a caller's scope of names. -/
def treeAt (names : List String) (src : Src NativeOp) : Option (Eff NativeOp) :=
  (src { names := names } []).toOption

/-- The masked body of `take` or `offer`: under the getter's `bind` and the mask. -/
def maskedBody : Eff NativeOp → Option (Eff NativeOp)
  | .bind (.withFiber .getInterruptible) (.uninterruptible body) => some body
  | _ => none

/-- The term of a row that opens a sequence: `bind (Ref.modify …) …`. -/
def rowTerm : Eff NativeOp → Option Term
  | .bind (.perform (.refModifyWith f) _) _ => some f
  | _ => none

/-- The withdrawal inside a wait: the first arm of the exit's test. -/
def withdrawalOf : Eff NativeOp → Option (Eff NativeOp)
  | .onExit _ (.select _ _ cleanup _) => some cleanup
  | _ => none

/-- `take`'s attempt: the round's body, after the hint's allocation. -/
def takeAttemptOf (tree : Eff NativeOp) : Option (Eff NativeOp) :=
  match maskedBody tree with
  | some (.bind _ (.bind (.iterate _ _ _ _ _ (.bind _ attempt)) _)) => some attempt
  | _ => none

/-- `take`'s wait: the first arm of the attempt's choice, before its discarded answer. -/
def takeWaitOf : Eff NativeOp → Option (Eff NativeOp)
  | .bind _ (.bind _ (.bind _ (.select _ _ (.bind wait _) _))) => some wait
  | _ => none

/-- `offer`'s attempt: after the two allocations. -/
def offerAttemptOf (tree : Eff NativeOp) : Option (Eff NativeOp) :=
  match maskedBody tree with
  | some (.bind _ (.bind _ attempt)) => some attempt
  | _ => none

/-- `offer`'s wait: the first arm of the attempt's choice. -/
def offerWaitOf : Eff NativeOp → Option (Eff NativeOp)
  | .bind _ (.bind _ (.select _ _ wait _)) => some wait
  | _ => none

/-- A statement's term at a row's scope, under the row's own binder. -/
def termUnder (row : Env) (step : TermSrc → TermSrc) : Option Term :=
  (step (minted (row.mint "current")) (row.push [row.mint "current"]) []).toOption

/-- The callers' scopes of the binding: a handle alone, a handle between two names, and a scope
that already holds two minted names. -/
def callers : List (List String) :=
  [["q", "m"], ["x", "q", "m", "y"], ["q", "_%answer3", "m", "_%current5"]]

-- `take`'s attempt: the row's term is the take step at `takeRow`, with the identity and the
-- hint under the names that the two `bindWith`s mint.
#guard callers.all fun names =>
  let caller : Env := { names := names }
  ((treeAt names (Queue.take .nat (var "q"))).bind takeAttemptOf).bind rowTerm ==
    termUnder (takeRow caller)
      (Queue.takeStep .nat (minted ((masked caller).mint "answer"))
        (minted ((looped caller).mint "answer"))) &&
  (termUnder (takeRow caller) (Queue.takeStep .nat (minted ((masked caller).mint "answer"))
    (minted ((looped caller).mint "answer")))).isSome
-- `take`'s withdrawal: the row's term is the withdrawal at `takeWithdrawRow`.
#guard callers.all fun names =>
  let caller : Env := { names := names }
  ((((treeAt names (Queue.take .nat (var "q"))).bind takeAttemptOf).bind takeWaitOf).bind
      withdrawalOf).bind rowTerm ==
    termUnder (takeWithdrawRow caller)
      (Queue.withdrawTake .nat (minted ((masked caller).mint "answer"))) &&
  (termUnder (takeWithdrawRow caller)
    (Queue.withdrawTake .nat (minted ((masked caller).mint "answer")))).isSome
-- `offer`'s attempt: the row's term is the offer step at `offerRow`, with the caller's message.
#guard callers.all fun names =>
  let caller : Env := { names := names }
  ((treeAt names (Queue.offer .nat (var "q") (var "m"))).bind offerAttemptOf).bind rowTerm ==
    termUnder (offerRow caller)
      (Queue.offerStep .nat (minted ((masked caller).mint "answer"))
        (minted ((named caller).mint "answer")) (var "m")) &&
  (termUnder (offerRow caller) (Queue.offerStep .nat (minted ((masked caller).mint "answer"))
    (minted ((named caller).mint "answer")) (var "m"))).isSome
-- `offer`'s withdrawal: the row's term is the withdrawal at `offerWithdrawRow`.
#guard callers.all fun names =>
  let caller : Env := { names := names }
  ((((treeAt names (Queue.offer .nat (var "q") (var "m"))).bind offerAttemptOf).bind
      offerWaitOf).bind withdrawalOf).bind rowTerm ==
    termUnder (offerWithdrawRow caller)
      (Queue.withdrawOffer .nat (minted ((masked caller).mint "answer"))) &&
  (termUnder (offerWithdrawRow caller)
    (Queue.withdrawOffer .nat (minted ((masked caller).mint "answer")))).isSome
-- `poll`: the row stands at the caller's own scope, under the mask alone.
#guard callers.all fun names =>
  let caller : Env := { names := names }
  (match treeAt names (Queue.poll .nat (var "q")) with
    | some (.uninterruptible body) => rowTerm body
    | _ => none) == termUnder caller (Queue.pollStep .nat) &&
  (termUnder caller (Queue.pollStep .nat)).isSome
-- `size`: the term after the read is the size step under the name that `bindWith` mints.
#guard callers.all fun names =>
  let caller : Env := { names := names }
  (match treeAt names (Queue.size .nat (var "q")) with
    | some (.bind (.perform .refGet _) (.succeed t)) => some t
    | _ => none) ==
    (Queue.sizeStep .nat (minted (caller.mint "answer")) (caller.push [caller.mint "answer"])
      []).toOption

-- Red control of the binding: at a scope with one binder fewer, the statement's term is
-- another tree. Here the take step is read at the scope before the hint's binder.
#guard callers.all fun names =>
  let caller : Env := { names := names }
  ((treeAt names (Queue.take .nat (var "q"))).bind takeAttemptOf).bind rowTerm !=
    termUnder (looped caller)
      (Queue.takeStep .nat (minted ((masked caller).mint "answer"))
        (minted ((looped caller).mint "answer")))
-- Red control of the two names: with the identity and the hint exchanged, another tree.
#guard callers.all fun names =>
  let caller : Env := { names := names }
  ((treeAt names (Queue.take .nat (var "q"))).bind takeAttemptOf).bind rowTerm !=
    termUnder (takeRow caller)
      (Queue.takeStep .nat (minted ((looped caller).mint "answer"))
        (minted ((masked caller).mint "answer")))

/-! ## 5. Hygiene: a caller's variable keeps its reading

**The promise.** A variable that a caller reads through `var` keeps its reading inside an
operation: every binder of the operation is minted, a minted name is reserved, and an author's
name is not (`var_push_minted`, `src/Effect4/Laws/Program/Author.lean`). It is no promise for an
arbitrary source term, which is a function of its scope: the last control below is one.

**The names.** The fixtures of the earlier slices wrote nine names
(`Written`, `Test/Program/QueueScenarios.lean`). Five stand around a caller's variable: `id` and
`hint` around the handle and the message, `r` and `e` around the handle in a withdrawal, and
`s` around the message in the offer's row. Four stand around none: `m`, `ok`, `woken`, `got`.

**The control of one name.** A client holds the handle, or a message, in a variable of that
name. Over the library's operations its tree is the tree of the same client under another name.
Over the written forms it is another tree: the variable reads the operation's own binder. -/

section Hygiene

open Test.Program.QueueScenarios (Ops library Written.ops Written.restoring)

/-- The fixture's written forms, under the mask that restores. -/
def written : Ops := Written.ops Written.restoring

/-- A client that holds the queue's handle in a variable of a given name, and takes. -/
def takeHolding (ops : Ops) (handle : String) : Src NativeOp :=
  bindName handle (Queue.bounded .nat 2) fun q => ops.take .nat q

/-- A client that holds the handle and a message in variables of given names, and offers. -/
def offerHolding (ops : Ops) (handle message : String) : Src NativeOp :=
  bindName handle (Queue.bounded .nat 2) fun q =>
    bindName message (succeed (nat 5)) fun m => ops.offer .nat q m

/-- A client's tree does not depend on its variable's name: it elaborates, and its tree is the
tree of the same client under a name that nobody writes. -/
def keeps (client : String → Src NativeOp) (name : String) : Bool :=
  (elaborate (client name)).toOption.isSome &&
    elaborate (client name) == elaborate (client "caller_")

/-- The nine names that the fixtures wrote. -/
def writtenNames : List String := ["id", "hint", "r", "e", "s", "m", "ok", "woken", "got"]

-- The library's operations: a caller's variable of each written name keeps its reading, as
-- the handle of a take, as the handle of an offer and as the message of an offer.
#guard writtenNames.all fun name =>
  keeps (takeHolding library) name && keeps (fun x => offerHolding library x "message_") name &&
    keeps (fun x => offerHolding library "handle_" x) name
-- Red controls, one for each name that stands around a caller's variable. Over the written
-- forms the handle under `id`, `hint`, `r` or `e` reads the operation's own binder.
#guard writtenNames.filter (fun name => !keeps (takeHolding written) name) =
  ["id", "hint", "r", "e"]
#guard writtenNames.filter (fun name => !keeps (fun x => offerHolding written x "message_") name) =
  ["id", "hint", "r", "e"]
-- The message under `id`, `hint` or `s` reads the offer's own binder.
#guard writtenNames.filter (fun name => !keeps (fun x => offerHolding written "handle_" x) name) =
  ["id", "hint", "s"]
-- So the five names of the capture are `id`, `hint`, `r`, `e` and `s`, and the other four
-- stand around no caller's variable.

-- The checker catches each of these captures: the captured value has another type.
#guard ["id", "hint", "r", "e"].all fun name =>
  verdict (takeHolding written name) = "typing: requestNotSubtype" &&
    verdict (takeHolding library name) = "built"
#guard ["id", "hint", "s"].all fun name =>
  verdict (offerHolding written "handle_" name) = "typing: binderTerm" &&
    verdict (offerHolding library "handle_" name) = "built"

/-! ### A capture that the checker does not catch

Where the caller's variable has the type of the binder that captures it, the written form is
scoped, it is typed and it runs: it offers the operation's own value in place of the caller's.
A client makes a `Deferred` of its own, offers it into a queue of such values, takes one, and
says whether the taken value is its own. -/

/-- The client: its own `Deferred` under a given name, in a queue of such values. -/
def ownDeferred (ops : Ops) (name : String) (value : Ty) : Src NativeOp :=
  bindName "queue_" (Queue.bounded (.deferredOf value .never) 2) fun q =>
    bindName name (Deferred.make value .never) fun mine => eff do
      let _ ← ops.offer (.deferredOf value .never) q mine
      let x ← ops.take (.deferredOf value .never) q
      return same x mine

-- The library's operations: the client gets its own value back, under each name. `id` meets
-- the request's identity, a `Deferred` of nothing, and `hint` the offer's hint, of a Boolean.
#guard [("id", Ty.unit), ("hint", Ty.bool), ("mine", Ty.unit), ("mine", Ty.bool)].all
  fun (name, value) => verdict (ownDeferred library name value) = "built" &&
    exitOf (ownDeferred library name value) == some (Exit.success (Val.bool true))
-- Red control: the written forms build and run, and under `id` and `hint` the taken value is
-- the operation's own binder, not the client's.
#guard [("id", Ty.unit), ("hint", Ty.bool)].all fun (name, value) =>
  verdict (ownDeferred written name value) = "built" &&
    exitOf (ownDeferred written name value) == some (Exit.success (Val.bool false))
-- Under a name that the forms do not write, they answer as the library does.
#guard [Ty.unit, Ty.bool].all fun value =>
  exitOf (ownDeferred written "mine" value) == some (Exit.success (Val.bool true))

/-! ### The promise's boundary: a source term that is no variable read through `var`

A minted reader is a function of its scope. Here a hand-made scope holds the name that the
wrapper mints for the request's identity at that depth. A caller's term that reads that name
through `minted` reads the identity inside the operation, and the handle outside it. No author
can write such a name through `var`, which refuses the reserved prefix. -/

-- The caller's scope is one name, at depth 1. The wrapper mints `_%restore1` and then the
-- identity's name at depth 2: the name that this scope already holds.
#guard (masked { names := ["_%answer2"] }).mint "answer" == "_%answer2"
-- At the caller's scope the term reads level 0. In the attempt's row it reads level 2, the
-- identity: the row's request is the identity's variable, and not the caller's.
#guard (minted "_%answer2" { names := ["_%answer2"] } []).toOption == some (Term.var 0)
#guard ((treeAt ["_%answer2"] (Queue.take .nat (minted "_%answer2"))).bind takeAttemptOf).map
    (fun attempt => match attempt with
      | .bind (.perform (.refModifyWith _) request) _ => request == Term.var 2
      | _ => false) == some true
-- A variable read through `var` cannot be that name: the scope reader refuses it.
#guard (var "_%answer2" { names := ["_%answer2"] } []).toOption.isNone
-- And an author's variable in the same place reads its own level, 0.
#guard ((treeAt ["q"] (Queue.take .nat (var "q"))).bind takeAttemptOf).map
    (fun attempt => match attempt with
      | .bind (.perform (.refModifyWith _) request) _ => request == Term.var 0
      | _ => false) == some true

end Hygiene

/-! ## 6. Typing at every scope

`take_types` and its four siblings type each operation at every typed scope, for every message
type with `MessageTy` (`src/Effect4/Laws/Modules/Queue/Ops.lean`). The examples read each at a
caller's variables: a variable that an author wrote is a kept term, at every scope that binds
it. The guards run the checker on each operation's tree, so each statement has a finite control
with the checker's own answer. -/

section Typing

open Effect4.Queue.Model
open Effect4.Machine.Env (Requirement)

-- `take` at a caller's variable `q`, at every typed scope that binds it to a queue's handle.
example (table : RowTable) (A : Ty) (message : MessageTy A) (s : TypedScope) (i : Nat)
    (bound : s.env.names.resolve "q" = some i)
    (held : s.types[i]? = some (.refOf (Queue.cellTy A))) :
    Answers (nativeSignature table) (Queue.take A (var "q")) s A :=
  Queue.take_types A message (kept_var rfl bound held)

-- `offer` at two variables: the handle and the message.
example (table : RowTable) (A : Ty) (message : MessageTy A) (s : TypedScope) (i j : Nat)
    (bound : s.env.names.resolve "q" = some i)
    (held : s.types[i]? = some (.refOf (Queue.cellTy A)))
    (boundM : s.env.names.resolve "m" = some j) (heldM : s.types[j]? = some A) :
    Answers (nativeSignature table) (Queue.offer A (var "q") (var "m")) s .bool :=
  Queue.offer_types A message (kept_var rfl bound held) (kept_var rfl boundM heldM)

-- `offer` of a number literal, at a queue of numbers.
example (table : RowTable) (s : TypedScope) (i : Nat)
    (bound : s.env.names.resolve "q" = some i)
    (held : s.types[i]? = some (.refOf (Queue.cellTy .nat))) (n : Nat) :
    Answers (nativeSignature table) (Queue.offer .nat (var "q") (nat n)) s .bool :=
  Queue.offer_types .nat (by decide) (kept_var rfl bound held) fun _ _ _ => types_nat n

-- `poll` and `size` read the handle at their own scope.
example (table : RowTable) (A : Ty) (message : MessageTy A) (s : TypedScope) (i : Nat)
    (bound : s.env.names.resolve "q" = some i)
    (held : s.types[i]? = some (.refOf (Queue.cellTy A))) :
    Answers (nativeSignature table) (Queue.poll A (var "q")) s (.option A) ∧
      Answers (nativeSignature table) (Queue.size A (var "q")) s .nat :=
  ⟨Queue.poll_types A message (kept_var rfl bound held).here,
    Queue.size_types A message (kept_var rfl bound held).here⟩

-- The construction, at every typed scope and every positive capacity.
example (table : RowTable) (A : Ty) (message : MessageTy A) (s : TypedScope) :
    Answers (nativeSignature table) (Queue.bounded A 3) s (.refOf (Queue.cellTy A)) :=
  Queue.bounded_types A message 3 (by decide) s

/-- The checker's answer on a source's tree, at a scope of names and their types. -/
def answerAt (names : List String) (types : List Ty) (src : Src NativeOp) : Option EffTy :=
  (src { names := names } []).toOption.bind (effTy nativeSignature types)

/-- Each operation at one message type and one scope of a handle and a message, with other
names around them: the checker answers the operation's type, with no failure and no
requirement. -/
def operationsTyped (names : List String) (others : Ty → List Ty) (A : Ty) : Bool :=
  decide (answerAt names (others A) (Queue.take A (var "q")) = some (EffTy.pure A)) &&
  decide (answerAt names (others A) (Queue.offer A (var "q") (var "m")) =
    some (EffTy.pure .bool)) &&
  decide (answerAt names (others A) (Queue.poll A (var "q")) = some (EffTy.pure (.option A))) &&
  decide (answerAt names (others A) (Queue.size A (var "q")) = some (EffTy.pure .nat)) &&
  decide (answerAt names (others A) (Queue.bounded A 2) =
    some (EffTy.pure (.refOf (Queue.cellTy A))))

-- At each of the 27 message types of `Test/Program/QueueSteps.lean`, at three scopes: the two
-- names alone, the two names between others, and a scope that holds names under the reserved
-- prefix.
#guard Test.Program.QueueSteps.messageTypes.length = 27
#guard Test.Program.QueueSteps.messageTypes.all
  (operationsTyped ["q", "m"] fun A => [.refOf (Queue.cellTy A), A])
#guard Test.Program.QueueSteps.messageTypes.all
  (operationsTyped ["x", "q", "m", "y"] fun A => [.nat, .refOf (Queue.cellTy A), A, .bool])
#guard Test.Program.QueueSteps.messageTypes.all
  (operationsTyped ["q", "_%answer1", "m", "_%restore3", "_%current4"] fun A =>
    [.refOf (Queue.cellTy A), .nat, A, .bool, .unit])
-- Red control: a message of another type has no answer.
#guard answerAt ["q", "m"] [.refOf (Queue.cellTy .nat), .bool]
  (Queue.offer .nat (var "q") (var "m")) = none
-- Red control: a handle that is no cell's handle has no answer, at each reading operation.
#guard [Queue.take .nat (var "q"), Queue.poll .nat (var "q"), Queue.size .nat (var "q"),
    Queue.offer .nat (var "q") (nat 1)].all fun operation =>
  decide (answerAt ["q"] [.nat] operation = none)
-- Red control: a cell of another message type has no answer at `take`: the step's type is no
-- pair of a reply and that cell's type.
#guard answerAt ["q"] [.refOf (Queue.cellTy .bool)] (Queue.take .nat (var "q")) = none
-- A number literal and a Boolean literal are messages of the statements.
#guard answerAt ["q"] [.refOf (Queue.cellTy .nat)] (Queue.offer .nat (var "q") (nat 7)) =
  some (EffTy.pure .bool)
#guard answerAt ["q"] [.refOf (Queue.cellTy .bool)] (Queue.offer .bool (var "q") (bool true)) =
  some (EffTy.pure .bool)
-- The limit of the statements: a string literal is no kept term, so no statement covers it.
-- The checker types this one tree: tested, on one tree, and not proved.
#guard answerAt ["q"] [.refOf (Queue.cellTy .string)]
  (Queue.offer .string (var "q") (str "a")) = some (EffTy.pure .bool)

end Typing

/-! ## The example of `README.md`

The section "A bounded queue" of `README.md` shows this program. It is the scenario R2 with
another name for the worker, so its tree is R2's: the program `pQueueWake` of the truth lane
(`harness/truth/Truth.lean`). -/

/-- The README's example, as the README writes it. -/
def handoff : Src NativeOp := eff do
  let q ← Queue.bounded .nat 2
  let worker ← fork (Queue.take .nat q)
  let _ ← Queue.offer .nat q (nat 7)
  let x ← join worker
  return x

-- `Effect4.Api.author` checks it at the answer type `nat`, with no failure and no requirement,
-- and its run answers `7`.
#guard match Effect4.Api.author handoff with
  | .ok typed => decide (typed.ty = EffTy.pure .nat) && typed.runSync == .success (Val.nat 7)
  | .error _ => false
-- Its tree is the scenario R2's.
#guard (elaborate handoff).toOption == (elaborate Test.Program.QueueScenarios.r2).toOption
-- Red control: with a message of another type, the checker refuses the program at a type.
#guard match Effect4.Api.author (eff do
    let q ← Queue.bounded .nat 2
    let a ← Queue.offer .nat q (bool true)
    return a) with
  | .error (.typing _) => true
  | _ => false

end Test.Program.QueueOps
