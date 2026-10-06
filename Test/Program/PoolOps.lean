import Test.Program.PoolPublic
import Test.Program.SemaphoreOps
import Effect4.Laws.Modules.Pool.Ops
import ProofGraph.Plan

/-!
# Pool's operations: the finite controls of the library module's laws (rows 267 to 269, 276, 279)

The module is `src/Effect4/Modules/Pool/Ops.lean`, over the shared wrapper
(`src/Effect4/Modules/Waiting.lean`). Its laws are `src/Effect4/Laws/Modules/Pool/Ops.lean`. The
cases on the machine are `Test/Program/PoolPublic.lean`. This battery holds the controls of the
laws.

1. **The construction refuses a size of zero** where an author writes the pool.
2. **Scope.** A client's program over `make` and `use` keeps the authoring scope judgment, by
   `authoring_scoped`: each program's law is found by its name.
3. **The attempt laws at the operations' own binders.** The second form of a law takes two
   premises for each minted name: the row's scope binds it, and no later binder shadows it
   (`src/Effect4/Laws/Modules/Pool/Ops.lean`). The operations' own binders meet both, at every
   caller's scope: proved here, over the wrapper's scopes that Semaphore's battery writes out
   (`Test/Program/SemaphoreOps.lean`). And each statement's term is the term of the operation's
   own row: tested, on the trees that the operations elaborate to.
4. **Hygiene.** A caller's variable keeps its reading in the handle, in the acquisition and in
   the body, at each stem that the surface mints. A written form with fixed names is the red
   control.
5. **Typing at every scope.** Each typing statement, read at a caller's variables, and the
   checker's own answer on each program's tree, at three scopes. A body that fails keeps its
   failure type, and `make` requires the scope's service. The red controls are a handle of
   another type, a resource of another type and a release that could fail.
6. **The example of `README.md`**, with its checked answer.
7. **The pinned outputs**: each law's axioms, and its standing in the plan.

Placement. The theorems of section 3 are helpers of the proposed claim `pool-expansion-agrees`
(concept `translation-simulation`, requirement R10): they discharge the scope premises of the
attempt laws, and they state nothing of a run. Section 5 is the finite control of the typing
statements (concept `store-typing`, requirement R4): each guard is the checker's answer on one
tree, and it states no run. Every guard is a finite check. None is a host run.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Test.Program.PoolOps

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Modules
open Test.Program.PoolScenarios (mk verdict exitOf)
open Test.Program.PoolPublic (library typesOf closedOf treeAt)
open Test.Program.SemaphoreOps (masked named looped takeRow takeReplied takeWithdrawRow hookRow
  takeRow_identity takeRow_hint takeWithdrawRow_identity maskedBody rowTerm loopAttempt
  withdrawalOf acquisitionOf hookOf termUnder answerAt)

/-! ## 1. The construction: a positive size -/

-- A positive size is written as a literal, and the proof is found by `decide`.
#guard verdict (scope (Pool.make .nat 1 (succeed (nat 7)))) = "built"
#guard typesOf (scope (Pool.make .nat 3 (succeed (nat 7)))) =
  some (.refOf (Pool.cellTy .nat), .never)

/--
error: could not synthesize default value for parameter '_positive' using tactics
---
error: Tactic `decide` proved that the proposition
  0 < 0
is false
-/
#guard_msgs in
example : Src NativeOp := Pool.make .nat 0 (succeed (nat 7))

/-! ## 2. Scope: a client's program over the operations -/

/-- A client of both operations. It makes a pool of two items inside a scope. A child borrows
one item and answers its resource plus one. The root borrows the other and answers its
resource. -/
def client : Src NativeOp :=
  scope (eff do
    let pool ← Pool.make .nat 2 (succeed (nat 7))
    let f ← fork (Pool.use .nat pool fun r => succeed (app "succ" [r]))
    let a ← Pool.use .nat pool fun r => succeed r
    let b ← join f
    return tuple [a, b])

#guard verdict client = "built" && closedOf client = some true
#guard typesOf client = some (.prod .nat .nat, .never)
-- The child holds the first item while the root asks: the root gets the second. Both resources
-- are 7.
#guard exitOf client = some (.success (.list [.nat 7, .nat 8]))

/-- The client keeps the scope judgment: `authoring_scoped` finds each program's law by its
name. -/
theorem client_scoped : (client : Src NativeOp).Scoped := by
  unfold client
  authoring_scoped

/-- So the tree that the client elaborates to is closed (`elaborate_scoped`). -/
example (e : Eff NativeOp) (h : elaborate client = .ok e) : Eff.scopedAt 0 e = true :=
  elaborate_scoped client_scoped h

/-! ## 3. The attempt laws at the operations' own binders

The second form of an attempt law takes two premises for each minted name: the row's scope binds
the name, and no later binder of the scope shadows it. The wrapper's scopes are written out in
`Test/Program/SemaphoreOps.lean`, binder by binder, as functions of the caller's scope:
`takeRow` is the scope of an attempt's row, and `takeWithdrawRow` the scope of a withdrawal's
row. Pool's lease holds the same loop at the same scope, under the mask's saved state. So those
scopes and their three theorems serve Pool as they are. This section adds the scopes that are
Pool's own: the hook's row, and the rows of the close. -/

section OwnBinders

open Effect4.Program.Typed
open Effect4.Pool.Model (cellVal itemVal)

/-- The scope of the return's row, in the hook: under the leased item's record and the body's
exit. The item's name is `(masked caller).mint "answer"`, the name of the request's identity in
the sibling scope of the loop. -/
def returnRow (caller : Env) : Env := hookRow caller

/-- The scope of the selection's row, in a return's helper: under the return step's reply. -/
def returned (caller : Env) : Env := (returnRow caller).push [(returnRow caller).mint "answer"]

/-- The close: under the first step's reply. The helper's selection row stands here. -/
def closeFirst (closer : Env) : Env := closer.push [closer.mint "answer"]

/-- The close: under the discarded answer of the wake's post. The closer's wrapper stands
here, so the closer's rows are the wrapper's rows at this scope as their caller's. -/
def closeBase (closer : Env) : Env := (closeFirst closer).push [(closeFirst closer).mint "answer"]

/-- **The return's row: the scope binds the leased item's record, and no later binder shadows
it.** The one later binder is the body's exit. -/
theorem returnRow_item (caller : Env) :
    (returnRow caller).names = (masked caller).names ++ (masked caller).mint "answer" ::
        [(named caller).mint "exit"] ∧
      ∀ name ∈ [(named caller).mint "exit"], name ≠ (masked caller).mint "answer" := by
  refine ⟨by simp only [returnRow, hookRow, named, Env.push, List.append_assoc, List.cons_append,
    List.nil_append], fun name member => ?_⟩
  rw [List.mem_singleton.mp member]
  exact later_mint_ne_answer (b := 101)
    (by simp only [named, Env.push_length, List.length_cons, List.length_nil]; omega)
    (by decide) (Or.inr (by decide))

-- Red control of the premise: where a later binder has the item's own name, the name resolves
-- to the later level, and the return would read that binder's value there.
#guard Names.resolve
  ((masked {}).names ++ [(masked {}).mint "answer", "x", (masked {}).mint "answer"])
  ((masked {}).mint "answer") == some 3
#guard Names.resolve ((masked {}).names ++ [(masked {}).mint "answer", "x"])
  ((masked {}).mint "answer") == some 1

/-! Each law at the operations' own binders. The premises that stay are the caller's context:
the typed environment, the request's two handles or the item's record at their levels, the
cell's value and its membership. No premise on a minted name stays. Each example's conclusion
is its law's. -/

/-- The lease's attempt at its own binders, in `use`. -/
example (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy) (A : Ty)
    (canonical : A.normalize = A) (tb : Table) (res : Nat → Val) (s : Pool.Model.State)
    (id : Nat) (hint : DeferredKey) (injective : tb.Injective) (caller : Env) (path : List Nat)
    (tys : List Ty) (w : Typed.World) (captured : List Val)
    (depth : captured.length = (takeRow caller).names.length)
    (tyDepth : tys.length = (takeRow caller).names.length) (typedEnv : EnvTyped w tys captured)
    (idHeld : captured[(masked caller).names.length]? = some (Val.promise (tb.handle id)))
    (idTyped : tys[(masked caller).names.length]? = some idTy)
    (hintHeld : captured[(looped caller).names.length]? = some (Val.promise hint))
    (hintTyped : tys[(looped caller).names.length]? = some idTy)
    (stores : Stores) (q : RefKey) (held : refPeek stores.refs q = some (cellVal tb res s))
    (member : Fits w (cellVal tb res s) (Pool.cellTy A)) :=
  Pool.lease_attempt_minted sig atoms canonical tb res s id hint injective (path := path) depth
    tyDepth typedEnv (takeRow_identity caller).1 (takeRow_identity caller).2 idHeld idTyped
    (takeRow_hint caller).1 (takeRow_hint caller).2 hintHeld hintTyped held member

/-- The lease's withdrawal at its own binders. -/
example (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy) (A : Ty)
    (canonical : A.normalize = A) (tb : Table) (res : Nat → Val) (s : Pool.Model.State)
    (id : Nat) (injective : tb.Injective) (caller : Env) (path : List Nat) (tys : List Ty)
    (w : Typed.World) (captured : List Val)
    (depth : captured.length = (takeWithdrawRow caller).names.length)
    (tyDepth : tys.length = (takeWithdrawRow caller).names.length)
    (typedEnv : EnvTyped w tys captured)
    (idHeld : captured[(masked caller).names.length]? = some (Val.promise (tb.handle id)))
    (idTyped : tys[(masked caller).names.length]? = some idTy)
    (stores : Stores) (q : RefKey) (held : refPeek stores.refs q = some (cellVal tb res s))
    (member : Fits w (cellVal tb res s) (Pool.cellTy A)) :=
  Pool.withdraw_attempt_minted sig atoms canonical tb res s id injective (path := path) depth
    tyDepth typedEnv (takeWithdrawRow_identity caller).1 (takeWithdrawRow_identity caller).2
    idHeld idTyped held member

/-- The return at the hook's own binder: the leased item's record stands at the level of the
mask's saved state plus one. -/
example (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy) (A : Ty)
    (canonical : A.normalize = A) (tb : Table) (res : Nat → Val) (s : Pool.Model.State)
    (it : Pool.Model.Item) (caller : Env) (path : List Nat) (tys : List Ty) (w : Typed.World)
    (captured : List Val) (depth : captured.length = (returnRow caller).names.length)
    (tyDepth : tys.length = (returnRow caller).names.length) (typedEnv : EnvTyped w tys captured)
    (itemHeld : captured[(masked caller).names.length]? = some (itemVal res it))
    (itemTyped : tys[(masked caller).names.length]? = some (Pool.itemTy A))
    (stores : Stores) (q : RefKey) (held : refPeek stores.refs q = some (cellVal tb res s))
    (member : Fits w (cellVal tb res s) (Pool.cellTy A)) :=
  Pool.return_attempt_minted sig atoms canonical tb res s it (path := path) depth tyDepth
    typedEnv (returnRow_item caller).1 (returnRow_item caller).2 itemHeld itemTyped held member

/-- The closer's attempt at the wrapper's own binders: the closer's wrapper stands at
`closeBase`, so its row is the wrapper's row at that scope as its caller's. -/
example (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy) (A : Ty)
    (canonical : A.normalize = A) (tb : Table) (res : Nat → Val) (s : Pool.Model.State)
    (id : Nat) (hint : DeferredKey) (injective : tb.Injective) (closer : Env) (path : List Nat)
    (tys : List Ty) (w : Typed.World) (captured : List Val)
    (depth : captured.length = (takeRow (closeBase closer)).names.length)
    (tyDepth : tys.length = (takeRow (closeBase closer)).names.length)
    (typedEnv : EnvTyped w tys captured)
    (idHeld : captured[(masked (closeBase closer)).names.length]? =
      some (Val.promise (tb.handle id)))
    (idTyped : tys[(masked (closeBase closer)).names.length]? = some idTy)
    (hintHeld : captured[(looped (closeBase closer)).names.length]? = some (Val.promise hint))
    (hintTyped : tys[(looped (closeBase closer)).names.length]? = some idTy)
    (stores : Stores) (q : RefKey) (held : refPeek stores.refs q = some (cellVal tb res s))
    (member : Fits w (cellVal tb res s) (Pool.cellTy A)) :=
  Pool.drain_attempt_minted sig atoms canonical tb res s id hint injective (path := path) depth
    tyDepth typedEnv (takeRow_identity (closeBase closer)).1
    (takeRow_identity (closeBase closer)).2 idHeld idTyped (takeRow_hint (closeBase closer)).1
    (takeRow_hint (closeBase closer)).2 hintHeld hintTyped held member

/-- The selection of a return's helper, at the helper's row: the count is the literal 1. -/
example (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy) (A : Ty)
    (canonical : A.normalize = A) (tb : Table) (res : Nat → Val) (s : Pool.Model.State)
    (row : Env) (path : List Nat) (tys : List Ty) (w : Typed.World) (captured : List Val)
    (depth : captured.length = row.names.length) (tyDepth : tys.length = row.names.length)
    (typedEnv : EnvTyped w tys captured) (stores : Stores) (q : RefKey)
    (held : refPeek stores.refs q = some (cellVal tb res s))
    (member : Fits w (cellVal tb res s) (Pool.cellTy A)) :=
  Pool.select_attempt sig atoms canonical tb res s 1 (path := path) (countSrc := nat 1) depth
    tyDepth typedEnv (reads_nat 1 _ path _) (types_nat 1) held member

end OwnBinders

/-! ### Each statement's term is the term of the operation's own row

The guards below bind the scopes to the operations: at each caller's scope, the term that the
operation's tree holds in its row is the tree of the statement's term at the scope that the
statement names. A scope with one binder too many or too few gives another tree, so the guard
fails. -/

/-- The lease's loop: the first node of the lease, before the branch on the refusal. -/
def leaseLoop : Eff NativeOp → Option (Eff NativeOp)
  | .bind loop (.select _ _ _ _) => some loop
  | _ => none

/-- The helper's body in a return or in the close: the fork in the first arm of the test of
the step's reply. -/
def postedOf : Eff NativeOp → Option (Eff NativeOp)
  | .bind _ (.select _ _ (.bind (.withFiber (.fork helper _)) _) _) => some helper
  | .bind _ (.bind (.select _ _ (.bind (.withFiber (.fork helper _)) _) _) _) => some helper
  | _ => none

/-- The closer's wrapper in the close: the node after the wake's post. -/
def drainOf : Eff NativeOp → Option (Eff NativeOp)
  | .bind _ (.bind _ wrapper) => some wrapper
  | _ => none

/-- The callers' scopes of the binding: a handle alone, between two names, and beside two names
under the reserved prefix. -/
def callers : List (List String) :=
  [["p"], ["x", "p", "y"], ["p", "_%answer3", "_%current5"]]

/-- The lease step of a statement, at a caller's scope: the identity and the hint under the
names that the two `bindWith`s mint. -/
def leaseTerm (caller : Env) : Option Term :=
  termUnder (takeRow caller)
    (Pool.leaseStep (minted ((masked caller).mint "answer"))
      (minted ((looped caller).mint "answer")))

/-- The withdrawal of a statement, at a caller's scope. -/
def withdrawTerm (caller : Env) : Option Term :=
  termUnder (takeWithdrawRow caller) (Pool.withdrawStep (minted ((masked caller).mint "answer")))

/-- The return step of a statement, at a caller's scope: the two stamps are two fields of the
leased item's record. -/
def returnTerm (caller : Env) : Option Term :=
  termUnder (returnRow caller)
    (Pool.returnStep (field (minted ((masked caller).mint "answer")) "stamp")
      (field (minted ((masked caller).mint "answer")) "lease"))

/-- The closer's step of a statement, at the close's scope. -/
def drainTerm (closer : Env) : Option Term :=
  termUnder (takeRow (closeBase closer))
    (Pool.drainStep (minted ((masked (closeBase closer)).mint "answer"))
      (minted ((looped (closeBase closer)).mint "answer")))

/-- The protected form of `use`, at a caller's scope: the masked body. -/
def useForm (names : List String) : Option (Eff NativeOp) :=
  (treeAt names (Pool.use .nat (var "p") fun r => succeed r)).bind maskedBody

-- `use`: the attempt's row is the lease step at `takeRow`, and the withdrawal's row is the
-- withdrawal at `takeWithdrawRow`.
#guard callers.all fun names =>
  let caller : Env := { names := names }
  let attempt := (((useForm names).bind acquisitionOf).bind leaseLoop).bind loopAttempt
  (leaseTerm caller).isSome && attempt.bind rowTerm == leaseTerm caller &&
    (withdrawTerm caller).isSome &&
    (attempt.bind withdrawalOf).bind rowTerm == withdrawTerm caller
-- `use`: the hook's row is the return step at `returnRow`, with the two fields of the item's
-- record. The helper's row is the selection step at `returned`, at the count 1.
#guard callers.all fun names =>
  let caller : Env := { names := names }
  let hook := (useForm names).bind hookOf
  (returnTerm caller).isSome && hook.bind rowTerm == returnTerm caller &&
    (termUnder (returned caller) (Pool.selectStep (nat 1))).isSome &&
    (hook.bind postedOf).bind rowTerm == termUnder (returned caller) (Pool.selectStep (nat 1))
-- The close: its first row is the close's first step at the close's own scope. The helper's
-- row is the selection at `closeFirst`, at the count of the first step's reply. The closer's
-- row is the closer's step at the wrapper's row over `closeBase`, and its withdrawal's row is
-- the withdrawal there.
#guard callers.all fun names =>
  let closer : Env := { names := names }
  let tree := treeAt names (Pool.close (var "p"))
  let attempt := ((tree.bind drainOf).bind maskedBody).bind loopAttempt
  (termUnder closer Pool.closeStep).isSome && tree.bind rowTerm == termUnder closer Pool.closeStep &&
    (tree.bind postedOf).bind rowTerm ==
      termUnder (closeFirst closer) (Pool.selectStep (tupleAt (minted (closer.mint "answer")) 1)) &&
    (drainTerm closer).isSome && attempt.bind rowTerm == drainTerm closer &&
    (attempt.bind withdrawalOf).bind rowTerm ==
      termUnder (takeWithdrawRow (closeBase closer))
        (Pool.withdrawStep (minted ((masked (closeBase closer)).mint "answer")))
-- Red control: the row's own scope is not the row's scope under one more binder, nor under
-- one binder fewer.
#guard callers.all fun names =>
  let caller : Env := { names := names }
  let attempt := (((useForm names).bind acquisitionOf).bind leaseLoop).bind loopAttempt
  attempt.bind rowTerm !=
      termUnder (takeReplied caller)
        (Pool.leaseStep (minted ((masked caller).mint "answer"))
          (minted ((looped caller).mint "answer"))) &&
    attempt.bind rowTerm !=
      termUnder (looped caller)
        (Pool.leaseStep (minted ((masked caller).mint "answer"))
          (minted ((looped caller).mint "answer")))
-- Red control of the two names: with the identity and the hint exchanged, another tree.
#guard callers.all fun names =>
  let caller : Env := { names := names }
  ((((useForm names).bind acquisitionOf).bind leaseLoop).bind loopAttempt).bind rowTerm !=
    termUnder (takeRow caller)
      (Pool.leaseStep (minted ((looped caller).mint "answer"))
        (minted ((masked caller).mint "answer")))
-- Red control of the return's two fields: with the two fields exchanged, another tree.
#guard callers.all fun names =>
  let caller : Env := { names := names }
  ((useForm names).bind hookOf).bind rowTerm !=
    termUnder (returnRow caller)
      (Pool.returnStep (field (minted ((masked caller).mint "answer")) "lease")
        (field (minted ((masked caller).mint "answer")) "stamp"))

/-- The request of the row that makes the cell, in a tree of `make` at the size 2: under the
two acquisitions' binders. -/
def madeRequest : Eff NativeOp → Option Term
  | .bind _ (.bind _ (.bind (.perform .refMake request) _)) => some request
  | _ => none

-- `make` at the size 2: the cell's row makes the initial value at the two resources' readers,
-- each the name that its `bindWith` mints. So the premise of `make_makes` reads the row of the
-- operation's own tree.
#guard callers.all fun names =>
  let caller : Env := { names := names }
  let first := caller.push [caller.mint "answer"]
  let second := first.push [first.mint "answer"]
  let tree := treeAt names (Pool.make .nat 2 (succeed (nat 7)))
  (tree.bind madeRequest).isSome &&
    tree.bind madeRequest ==
      (Pool.initial .nat [minted (caller.mint "answer"), minted (first.mint "answer")] second
        []).toOption

/-! ## 4. Hygiene: a caller's variable keeps its reading

**The promise.** A variable that a caller reads through `var` keeps its reading inside an
operation: every binder of the operation is minted, a minted name is reserved, and an author's
name is not (`var_push_minted`, `src/Effect4/Laws/Program/Author.lean`). The same holds inside
an acquisition and inside a body. It is no promise for an arbitrary source term, which is a
function of its scope.

**The names.** The surface mints eight stems: `answer`, `cursor`, `payload`, `exit`, `current`,
`restore`, `acc` and `item`. A caller may write each as a name of its own, and so it may write
the names that a written form would choose: `pool`, `id`, `hint`, `reply`, `got` and `s`.

**The control of one name.** A client holds the handle, or a value that its acquisition or its
body reads, in a variable of that name. Over the library's operations its tree is the tree of
the same client under another name. Over a written form with fixed names it is another tree: the
variable reads the form's own binder. -/

section Hygiene

/-- The names of the controls: the eight stems, and six names of a written form. -/
def names : List String :=
  ["answer", "cursor", "payload", "exit", "current", "restore", "acc", "item", "pool", "id",
    "hint", "reply", "got", "s"]

/-- A client that holds the handle in a variable of a given name, and borrows. -/
def useHolding (use : Ty → TermSrc → (TermSrc → Src NativeOp) → Src NativeOp) (handle : String) :
    Src NativeOp :=
  bindName handle (Ref.make (Pool.initial .nat [nat 1])) fun pool =>
    use .nat pool fun r => succeed r

/-- A client that holds a number in a variable of a given name, and reads it in a body. -/
def bodyHolding (use : Ty → TermSrc → (TermSrc → Src NativeOp) → Src NativeOp) (held : String) :
    Src NativeOp :=
  bindWith (Ref.make (Pool.initial .nat [nat 1])) fun pool =>
    bindName held (succeed (nat 5)) fun v => use .nat pool fun r => succeed (app "add" [r, v])

/-- A client that holds a number in a variable of a given name, and reads it in an
acquisition. -/
def acquireHolding (held : String) : Src NativeOp :=
  bindName held (succeed (nat 5)) fun v => Pool.make .nat 2 (succeed v)

/-- A client's tree does not depend on its variable's name: it elaborates, and its tree is the
tree of the same client under a name that nobody writes. -/
def keeps (client : String → Src NativeOp) (name : String) : Bool :=
  (elaborate (client name)).toOption.isSome &&
    elaborate (client name) == elaborate (client "nobodyWritesThis")

-- The library's operations keep each name, in the handle, in the body and in the acquisition.
#guard names.all (keeps (useHolding Pool.use))
#guard names.all (keeps (bodyHolding Pool.use))
#guard names.all (keeps acquireHolding)

/-- **Red control: a written form of `use` with fixed names.** It binds the pool's current
value as `s` in each row, the identity as `id`, the hint as `hint`, the reply as `reply`, the
leased item as `got` and the exit as `exit`. It is one round, with no wait. -/
def useWritten (_A : Ty) (pool : TermSrc) (body : TermSrc → Src NativeOp) : Src NativeOp :=
  uninterruptible
    (bind "id" (Deferred.make .unit .never)
      (bind "hint" (Deferred.make .unit .never)
        (bind "reply" (Ref.modify "s" (Pool.leaseStep (var "id") (var "hint") (var "s")) pool)
          (selectOption "got" (tupleAt (var "reply") 1) (succeed (nat 0))
            (onExit "exit" (interruptible (body (field (var "got") "resource")))
              (Ref.modify "s"
                (Pool.returnStep (field (var "got") "stamp") (field (var "got") "lease") (var "s"))
                pool))))))

-- The written form builds, and it answers as the library's on a pool with an idle item.
#guard verdict (useHolding useWritten "p") = "built" &&
  exitOf (useHolding useWritten "p") = exitOf (useHolding Pool.use "p")
-- A handle named `id`, `hint` or `reply` is read under the written form's binder of that name:
-- another tree. So is a handle named `got` or `exit`, at the return's row.
#guard ["id", "hint", "reply", "got", "exit"].all fun name =>
  !keeps (useHolding useWritten) name
-- A body's variable named `got` or `reply` reads the written form's binder.
#guard !keeps (bodyHolding useWritten) "got" && !keeps (bodyHolding useWritten) "reply"
-- The written form keeps the names that it does not write. A handle named `s` is kept too: a
-- row reads its handle outside the binder of the cell's current value.
#guard ["answer", "cursor", "payload", "pool", "s"].all (keeps (useHolding useWritten))

end Hygiene

/-! ## 5. Typing at every scope

`use_types`, `make_types` and `close_answers` type each program at every typed scope
(`src/Effect4/Laws/Modules/Pool/Ops.lean`). The examples read each at a caller's variables: a
variable that an author wrote is a kept term, at every scope that binds it. The guards run the
checker on each program's tree, so each statement has a finite control with the checker's own
answer. -/

section Typing

open Effect4.Machine.Env (Requirement)
open Conform.Effect4.Typing

-- `use` with a body that answers its resource: the form answers a resource, with no failure
-- and no requirement.
example (table : RowTable) (s : TypedScope) (i : Nat)
    (bound : s.env.names.resolve "p" = some i)
    (held : s.types[i]? = some (.refOf (Pool.cellTy .nat))) :
    Has (nativeSignature table) (Pool.use .nat (var "p") fun r => succeed r) s
      (EffTy.pure .nat) :=
  Pool.use_types (A := .nat) (b := EffTy.pure .nat) (by decide) (kept_var rfl bound held)
    fun _ _ _ hr => (answers_succeed hr.here).has

-- `use` with a body that fails with a number: the form keeps the failure type.
example (table : RowTable) (s : TypedScope) (i : Nat)
    (bound : s.env.names.resolve "p" = some i)
    (held : s.types[i]? = some (.refOf (Pool.cellTy .nat))) :
    Has (nativeSignature table) (Pool.use .nat (var "p") fun _ => fail (nat 3)) s
      ⟨.never, .nat, Requirement.empty⟩ :=
  Pool.use_types (A := .nat) (b := ⟨.never, .nat, Requirement.empty⟩) (by decide)
    (kept_var rfl bound held) fun _ _ _ _ _ =>
      ⟨.fail (.lit (.nat 3)), rfl, effTy_complete _ _ _ _ (.fail rfl rfl)⟩

-- The close at a variable: it answers nothing.
example (table : RowTable) (s : TypedScope) (i : Nat)
    (bound : s.env.names.resolve "p" = some i)
    (held : s.types[i]? = some (.refOf (Pool.cellTy .nat))) :
    Answers (nativeSignature table) (Pool.close (var "p")) s .unit :=
  Pool.close_answers (A := .nat) (by decide) (kept_var rfl bound held)

-- `make` with an acquisition that answers a number: it answers the handle, it has the
-- acquisition's failure type, and it requires the acquisition's services with the scope's.
example (table : RowTable) (s : TypedScope) :
    Has (nativeSignature table) (Pool.make .nat 2 (succeed (nat 7))) s
      ⟨.refOf (Pool.cellTy .nat), (EffTy.pure .nat).error.normalize,
        (EffTy.pure .nat).requires.union
          (Requirement.single (nativeSignature table).scopeKey)⟩ :=
  Pool.make_types (A := .nat) (a := EffTy.pure .nat) (by decide) 2 (by decide) rfl
    fun _ _ => (answers_succeed fun _ => types_nat 7).has

/-- A handle's type at numbers. -/
def poolTy : Ty := .refOf (Pool.cellTy .nat)

/-- What `make` at numbers has, where its acquisition cannot fail and requires nothing: the
handle, no failure, and the scope's service. -/
def madeTy : EffTy :=
  ⟨poolTy, .never, Requirement.single nativeSignature.scopeKey⟩

/-- Each program at one scope of a handle and a number, with other names around them: the
checker answers the program's type. -/
def programsTyped (names : List String) (types : List Ty) : Bool :=
  decide (answerAt names types (Pool.use .nat (var "p") fun r => succeed r) =
    some (EffTy.pure .nat)) &&
  decide (answerAt names types (Pool.use .nat (var "p") fun _ => succeed (var "n")) =
    some (EffTy.pure .nat)) &&
  decide (answerAt names types (Pool.close (var "p")) = some (EffTy.pure .unit)) &&
  decide (answerAt names types (Pool.make .nat 1 (succeed (var "n"))) = some madeTy) &&
  decide (answerAt names types (Pool.make .nat 3 (succeed (var "n"))) = some madeTy) &&
  decide (answerAt names types (scope (Pool.make .nat 2 (succeed (var "n")))) =
    some (EffTy.pure poolTy))

-- At three scopes: the two names alone, the two names between others, and a scope that holds
-- names under the reserved prefix.
#guard programsTyped ["p", "n"] [poolTy, .nat]
#guard programsTyped ["x", "p", "n", "y"] [.bool, poolTy, .nat, .string]
#guard programsTyped ["p", "_%answer1", "n", "_%restore3", "_%current4"]
  [poolTy, .bool, .nat, .bool, .unit]
-- A body that fails with a number: the checker answers the body's failure type.
#guard answerAt ["p"] [poolTy] (Pool.use .nat (var "p") fun _ => fail (nat 3)) =
  some ⟨.never, .nat, Requirement.empty⟩
-- An acquisition that fails with a number: `make` has that failure type, and it requires the
-- scope's service.
#guard answerAt [] [] (Pool.make .nat 2 (bindWith (fail (nat 3)) fun _ => succeed (nat 7))) =
  some ⟨poolTy, .nat, Requirement.single nativeSignature.scopeKey⟩
-- `make` requires the scope's service, and a scope around it requires nothing.
#guard (answerAt [] [] (Pool.make .nat 1 (succeed (nat 7)))).map (·.requires) =
  some (Requirement.single nativeSignature.scopeKey)
#guard (answerAt [] [] (scope (Pool.make .nat 1 (succeed (nat 7))))).map (·.requires) =
  some Requirement.empty
-- The answer at a closed pool: no answer, no failure type and no requirement.
#guard answerAt [] [] Pool.refused = some (EffTy.pure .never)
-- Red control: a handle that is no cell's handle has no answer.
#guard [Pool.use .nat (var "p") fun r => succeed r, Pool.close (var "p")].all fun program =>
  decide (answerAt ["p"] [.nat] program = none)
-- Red control: a pool at another resource type has no answer at the stated type.
#guard answerAt ["p"] [.refOf (Pool.cellTy .string)] (Pool.use .nat (var "p") fun r => succeed r) =
  none
-- Red control: an acquisition of another type than the stated one has no answer.
#guard answerAt [] [] (Pool.make .nat 1 (succeed (bool true))) = none
-- Red control: a release that could fail is refused. The close cannot fail, and a changed
-- close that fails has no answer in `make`'s registration.
#guard answerAt ["p"] [poolTy] (Pool.atClose (Pool.close (var "p"))) =
  some ⟨.unit, .never, Requirement.single nativeSignature.scopeKey⟩
#guard answerAt ["p"] [poolTy] (Pool.atClose (andThen (Pool.close (var "p")) (fail (nat 3)))) =
  none

end Typing

/-! ## 6. The example of `README.md`

The section "A pool" of `README.md` shows this program. The root borrows the one item, and
inside its body it forks a worker that asks for the item. The worker waits. The root's return
posts a helper, the root joins the worker, and the helper wakes the worker. -/

/-- The README's example, as the README writes it. -/
def handoff : Src NativeOp := scope (eff do
  let pool ← Pool.make .nat 1 (succeed (nat 7))
  let worker ← Pool.use .nat pool fun _ =>
    fork (Pool.use .nat pool fun resource => succeed resource)
  let x ← join worker
  return x)

-- `Effect4.Api.author` checks it at the answer type `nat`, with no failure and no requirement,
-- and its run answers `7`: the worker gets the resource that the root returned.
#guard match Effect4.Api.author handoff with
  | .ok typed => decide (typed.ty = EffTy.pure .nat) && typed.runSync == .success (Val.nat 7)
  | .error _ => false
-- The checked session's run gives the same answer, at the tape `[evaluate root, flush]`.
#guard exitOf handoff = some (.success (.nat 7))
-- The worker waits first. It is fiber 1, and the helper of the root's return is fiber 2. The
-- worker and then the root exit inside the helper's task, so the helper exits last.
#guard Test.Program.PoolScenarios.exitsOf handoff = some [1, 0, 2]
-- Red control: with a resource of another type, the checker refuses the program at a type.
#guard match Effect4.Api.author (scope (eff do
    let pool ← Pool.make .nat 1 (succeed (nat 7))
    Pool.use .bool pool fun resource => succeed resource)) with
  | .error (.typing _) => true
  | _ => false
-- The scope is part of the example: without it the checker admits the program at a type that
-- requires the scope, and the type is not the example's.
#guard match Effect4.Api.author (eff do
    let pool ← Pool.make .nat 1 (succeed (nat 7))
    Pool.use .nat pool fun resource => succeed resource) with
  | .ok typed => decide (typed.ty ≠ EffTy.pure .nat)
  | .error _ => false

/-! ## 7. The pinned outputs

Each law's axioms, and its standing as the plan derives it from its proof. No law rests on a
planned goal. The counts are of this battery's tree, which holds no step of a proof. -/

/-- info: 'Effect4.Pool.use_types' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Pool.use_types

/-- info: 'Effect4.Pool.make_types' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Pool.make_types

/-- info: 'Effect4.Pool.close_answers' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Pool.close_answers

/-- info: 'Effect4.Pool.lease_attempt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Pool.lease_attempt

/-- info: 'Effect4.Pool.withdraw_attempt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Pool.withdraw_attempt

/-- info: 'Effect4.Pool.return_attempt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Pool.return_attempt

/-- info: 'Effect4.Pool.select_attempt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Pool.select_attempt

/-- info: 'Effect4.Pool.close_attempt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Pool.close_attempt

/-- info: 'Effect4.Pool.drain_attempt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Pool.drain_attempt

/-- info: 'Effect4.Pool.make_makes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Pool.make_makes

/-- info: 'Effect4.Pool.lease_attempt_minted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Pool.lease_attempt_minted

/-- info: 'Effect4.Pool.withdraw_attempt_minted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Pool.withdraw_attempt_minted

/-- info: 'Effect4.Pool.return_attempt_minted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Pool.return_attempt_minted

/-- info: 'Effect4.Pool.drain_attempt_minted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Pool.drain_attempt_minted

-- The scope laws of the three programs.
/-- info: 'Effect4.Pool.use_scoped' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Pool.use_scoped

/-- info: 'Effect4.Pool.make_scoped' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Pool.make_scoped

/-- info: 'Effect4.Pool.close_scoped' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Pool.close_scoped

-- The shared rules that the slice adds.
/-- info: 'Effect4.Modules.has_andThen' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms has_andThen

/-- info: 'Effect4.Modules.has_acquireRelease' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms has_acquireRelease

/-- info: 'Effect4.Modules.answers_getId' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms answers_getId

/-- info: 'Effect4.Modules.answers_interrupt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms answers_interrupt

/-- info: 'Effect4.Modules.Kept.field' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Kept.field

/-- info: 'Effect4.Modules.captured_field' depends on axioms: [propext] -/
#guard_msgs in
#print axioms captured_field

/-- info: 'Effect4.Modules.reads_listOf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms reads_listOf

/-- info: 'Effect4.Modules.listOf_scoped' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms listOf_scoped

/--
info: Effect4.Pool.use_types: proved; nearest []; 0 lemmas, 0 definitions
Effect4.Pool.make_types: proved; nearest [Effect4.Pool.close_answers]; 0 lemmas, 0 definitions
Effect4.Pool.close_answers: proved; nearest []; 0 lemmas, 0 definitions
next goals: 0
-/
#guard_msgs in
#plan_status Pool.use_types Pool.make_types Pool.close_answers

/--
info: Effect4.Pool.lease_attempt: proved; nearest []; 0 lemmas, 0 definitions
Effect4.Pool.withdraw_attempt: proved; nearest []; 0 lemmas, 0 definitions
Effect4.Pool.return_attempt: proved; nearest []; 0 lemmas, 0 definitions
Effect4.Pool.select_attempt: proved; nearest []; 0 lemmas, 0 definitions
Effect4.Pool.close_attempt: proved; nearest []; 0 lemmas, 0 definitions
Effect4.Pool.drain_attempt: proved; nearest []; 0 lemmas, 0 definitions
Effect4.Pool.make_makes: proved; nearest []; 0 lemmas, 0 definitions
next goals: 0
-/
#guard_msgs in
#plan_status Pool.lease_attempt Pool.withdraw_attempt Pool.return_attempt Pool.select_attempt
  Pool.close_attempt Pool.drain_attempt Pool.make_makes

/--
info: Effect4.Pool.lease_attempt_minted: proved; nearest [Effect4.Pool.lease_attempt]; 0 lemmas, 0 definitions
Effect4.Pool.withdraw_attempt_minted: proved; nearest [Effect4.Pool.withdraw_attempt]; 0 lemmas, 0 definitions
Effect4.Pool.return_attempt_minted: proved; nearest [Effect4.Pool.return_attempt]; 0 lemmas, 0 definitions
Effect4.Pool.drain_attempt_minted: proved; nearest [Effect4.Pool.drain_attempt]; 0 lemmas, 0 definitions
Effect4.Pool.lease_attempt: proved; nearest []; 0 lemmas, 0 definitions
Effect4.Pool.withdraw_attempt: proved; nearest []; 0 lemmas, 0 definitions
Effect4.Pool.return_attempt: proved; nearest []; 0 lemmas, 0 definitions
Effect4.Pool.drain_attempt: proved; nearest []; 0 lemmas, 0 definitions
next goals: 0
-/
#guard_msgs in
#plan_status Pool.lease_attempt_minted Pool.withdraw_attempt_minted Pool.return_attempt_minted
  Pool.drain_attempt_minted Pool.lease_attempt Pool.withdraw_attempt Pool.return_attempt
  Pool.drain_attempt

end Test.Program.PoolOps
