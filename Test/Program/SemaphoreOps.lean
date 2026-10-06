import Test.Program.SemaphoreScenarios
import Effect4.Laws.Modules.Semaphore.Ops
import ProofGraph.Plan

/-!
# Semaphore's operations: the finite controls of the library module (rows 259 to 261 and 276)

The module is `src/Effect4/Modules/Semaphore/Ops.lean`, over the shared wrapper
(`src/Effect4/Modules/Waiting.lean`). The host probe's cases are
`Test/Program/SemaphoreScenarios.lean`. This battery holds the controls of the operations that
those do not run, and of the module's laws.

1. **The construction refuses a total of zero** where an author writes the semaphore.
2. **The forms that never wait** on the machine: `takeIfAvailable` and
   `withPermitsIfAvailable`, on both answers. Where the step does not take, the body does not
   run and nothing is released: each of the two faults is a red control.
3. **Scope.** A client's program over the six operations keeps the authoring scope judgment, by
   `authoring_scoped`: each operation's law is found by its name.
4. **The attempt laws at the operations' own binders.** The second form of a law takes two
   premises for each minted name: the row's scope binds it, and no later binder shadows it
   (`src/Effect4/Laws/Modules/Semaphore/Ops.lean`). The operations' own binders meet both, at
   every caller's scope: proved here, with each scope written out. And each statement's term is
   the term of the operation's own row: tested, on the trees that the operations elaborate to.
5. **Hygiene.** The fixtures wrote the names `id`, `hint`, `took`, `r`, `e` and `s` around a
   caller's variable. For each name, a caller's variable of that name keeps its reading in the
   library's operation, and the fixture's written form is the red control.
6. **Typing at every scope.** Each operation's typing statement, read at a caller's variables,
   and the checker's own answer on each operation's tree, at three scopes. A protected body
   that fails keeps its failure type. The red controls are a count of another type and a handle
   of another type.
7. **The pinned outputs**: each law's axioms, and its standing in the plan. The example of
   `README.md` stands before them, with its checked answer.

Placement. Each run is a finite control of the proposed claim `semaphore-expansion-agrees`
(concept `translation-simulation`, requirement R10), on the side of the operations' use in a
program. Every guard is one run on one schedule. None proves delivery, a cancellation law or
liveness, and none is a host run. The theorems of section 4 are helpers of the same claim: they
discharge the scope premises of the attempt laws, and they state nothing of a run. Section 6 is
the finite control of the typing statements (concept `store-typing`, requirement R4): each guard
is the checker's answer on one tree, and it states no run.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Test.Program.SemaphoreOps

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Test.Program.SemaphoreScenarios (Ops library mk verdict exitOf exitAt typesOf counts mark
  noNumbers count marks treeAt)
open Effect4.Modules

/-! ## 1. The construction: a positive total -/

-- A positive total is written as a literal, and the proof is found by `decide`.
#guard verdict (Semaphore.make 1) = "built"
#guard typesOf (Semaphore.make 3) = some (.refOf Semaphore.cellTy, .never)

/--
error: could not synthesize default value for parameter '_positive' using tactics
---
error: Tactic `decide` proved that the proposition
  0 < 0
is false
-/
#guard_msgs in
example : Src NativeOp := Semaphore.make 0

/-! ## 2. The forms that never wait, on the machine

A total of 2. A protected body runs with both permits, and it writes the taken count that it
reads. The root then takes 1. A second protected form asks for 2: one permit is free, so the
step does not take. Its body would write the mark 99. Two takes of 1 follow, each one step. -/

/-- The scenario, over a form of `withPermitsIfAvailable`. The answer: the first form's answer,
the counts after it, the second form's answer, the two takes' answers, the counts at the end,
and the marks. -/
def ifAvailableWith (form : TermSrc → TermSrc → Src NativeOp → Src NativeOp) : Src NativeOp :=
  eff do
    let q ← Semaphore.make 2
    let log ← Ref.make noNumbers
    let a ← form q (nat 2) (eff do
      let s ← Ref.get q
      let _ ← mark log (field s "taken")
      return nat 7)
    let between ← counts q
    let _ ← Semaphore.take q (nat 1)
    let b ← form q (nat 2) (eff do
      let _ ← mark log (nat 99)
      return nat 8)
    let c ← Semaphore.takeIfAvailable q (nat 1)
    let d ← Semaphore.takeIfAvailable q (nat 1)
    let after ← counts q
    let l ← Ref.get log
    return tuple [a, between, b, c, d, after, l]

/-- The scenario over the library's form. -/
def ifAvailable : Src NativeOp := ifAvailableWith Semaphore.withPermitsIfAvailable

#guard verdict ifAvailable = "built"
-- An option of the body's answer, a Boolean for each take, and no failure.
#guard (typesOf ifAvailable).map (·.2) = some .never
-- The first form takes 2: its body sees 2 taken and answers 7, and the release follows, so
-- nothing is taken after it. The second form does not take: it answers the empty option, its
-- body does not run (no mark 99), and nothing is released: the second take of 1 finds no
-- permit. Two permits are taken at the end.
#guard exitOf ifAvailable = some (.success (.list
  [.some (.nat 7), count 0 [] [], .none, .bool true, .bool false, count 2 [] [], marks [2]]))
-- The ordinary run gives the same answer at the truth lane's fuel.
#guard exitAt 1000 ifAvailable = exitOf ifAvailable

/-- **Fault: a release that does not select on what the step answered.** -/
def releasesAnyway (q count : TermSrc) (body : Src NativeOp) : Src NativeOp :=
  protectedBy (fun _ => Semaphore.takeIfAvailable q count)
    (fun _ => andThen (Semaphore.release q count) (succeed unit))
    (fun took =>
      ifElse took (bindWith body fun answer => succeed (app "some" [answer])) (succeed noneT))

/-- **Fault: a body that does not select on what the step answered.** -/
def runsAnyway (q count : TermSrc) (body : Src NativeOp) : Src NativeOp :=
  protectedBy (fun _ => Semaphore.takeIfAvailable q count)
    (fun took => ifElse took (andThen (Semaphore.release q count) (succeed unit)) (succeed unit))
    (fun _ => bindWith body fun answer => succeed (app "some" [answer]))

-- Each fault builds: the checker types it. So each fails the promised property, and not typing.
#guard [ifAvailableWith releasesAnyway, ifAvailableWith runsAnyway].map verdict =
  ["built", "built"]
-- The release that runs anyway gives back two permits that the form never took: the root's own
-- permit is released, and the second take of 1 takes.
#guard exitOf (ifAvailableWith releasesAnyway) = some (.success (.list
  [.some (.nat 7), count 0 [] [], .none, .bool true, .bool true, count 2 [] [], marks [2]]))
-- The body that runs anyway runs with no permit: it answers 8 and writes its mark.
#guard exitOf (ifAvailableWith runsAnyway) = some (.success (.list
  [.some (.nat 7), count 0 [] [], .some (.nat 8), .bool true, .bool false, count 2 [] [],
    marks [2, 99]]))

/-! ## 3. Scope: a client's program over the six operations -/

/-- A client of every operation. The root takes 1 of 2. A child asks for 2 in the protected
form, and it waits. The root releases 1: the walk resumes the child, which runs its body and
releases. The two forms that never wait follow. -/
def client : Src NativeOp := eff do
  let q ← Semaphore.make 2
  let a ← Semaphore.take q (nat 1)
  let f ← fork (Semaphore.withPermits q (nat 2) (succeed (nat 7)))
  let b ← Semaphore.release q (nat 1)
  let x ← join f
  let c ← Semaphore.takeIfAvailable q (nat 1)
  let d ← Semaphore.withPermitsIfAvailable q (nat 1) (succeed (nat 8))
  return tuple [a, b, x, c, d]

#guard verdict client = "built"
#guard typesOf client = some (.tuple [.nat, .nat, .nat, .bool, .option .nat], .never)
-- The take answers its count, the release the free count, the protected form its body's answer.
#guard exitOf client = some (.success (.list
  [.nat 1, .nat 2, .nat 7, .bool true, .some (.nat 8)]))
#guard exitAt 1000 client = exitOf client

/-- The client keeps the scope judgment: `authoring_scoped` finds each operation's law by its
name. -/
theorem client_scoped : (client : Src NativeOp).Scoped := by
  unfold client
  authoring_scoped

/-- So the tree that the client elaborates to is closed (`elaborate_scoped`). -/
example (e : Eff NativeOp) (h : elaborate client = .ok e) : Eff.scopedAt 0 e = true :=
  elaborate_scoped client_scoped h

/-! ## 4. The attempt laws at the operations' own binders

The second form of an attempt law takes two premises for each minted name: the row's scope binds
the name, and no later binder of the scope shadows it. Below, each scope of an operation is
written out as a function of the caller's scope, binder by binder. Each theorem proves the two
premises there, at every caller's scope. Then each law applies with no premise on a name.

`take` and `withPermits` hold one loop, the wrapper's at a restore site, at one scope: under the
mask's saved state. So the take's rows of the two operations stand at the same scopes. -/

section OwnBinders

open Effect4.Program.Typed
open Effect4.Semaphore.Model (cellVal)

/-- Under the mask: the saved state's name. -/
def masked (caller : Env) : Env := caller.push [caller.mint "restore"]

/-- Under the request's identity. Its name is `(masked caller).mint "answer"`. The acquired
value of a protected form has the same name, in the sibling scope after the loop. -/
def named (caller : Env) : Env := (masked caller).push [(masked caller).mint "answer"]

/-- Under the loop's cursor. -/
def looped (caller : Env) : Env := (named caller).push [(named caller).mint "cursor"]

/-- The scope of the take's row, under the round's hint. The hint's name is
`(looped caller).mint "answer"`. -/
def takeRow (caller : Env) : Env := (looped caller).push [(looped caller).mint "answer"]

/-- Under the take step's reply. The wait stands here. -/
def takeReplied (caller : Env) : Env := (takeRow caller).push [(takeRow caller).mint "answer"]

/-- The scope of the withdrawal's row, under the wait's exit. -/
def takeWithdrawRow (caller : Env) : Env :=
  (takeReplied caller).push [(takeReplied caller).mint "exit"]

/-- A protected form: the scope of the hook's release row, under the acquired value and the
body's exit. -/
def hookRow (caller : Env) : Env := (named caller).push [(named caller).mint "exit"]

/-- `release`: under the release step's reply. The helper's body is elaborated here. -/
def released (caller : Env) : Env := caller.push [caller.mint "answer"]

/-- The scope of a visit's row, under the walk's cursor. The cursor's name is
`(released caller).mint "cursor"`. -/
def walkRow (caller : Env) : Env := (released caller).push [(released caller).mint "cursor"]

/-- **The take's row: the scope binds the identity, and no later binder shadows it.** The later
binders are the loop's cursor and the round's hint. -/
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

/-- **The take's row: the scope binds the hint last**, so no later binder exists. -/
theorem takeRow_hint (caller : Env) :
    (takeRow caller).names = (looped caller).names ++ (looped caller).mint "answer" :: [] ∧
      ∀ name ∈ ([] : Names), name ≠ (looped caller).mint "answer" :=
  ⟨rfl, fun _ member => absurd member List.not_mem_nil⟩

/-- **The withdrawal's row: the scope binds the identity, and no later binder shadows it.** The
later binders are the cursor, the hint, the step's reply and the wait's exit. -/
theorem takeWithdrawRow_identity (caller : Env) :
    (takeWithdrawRow caller).names = (masked caller).names ++ (masked caller).mint "answer" ::
        [(named caller).mint "cursor", (looped caller).mint "answer",
          (takeRow caller).mint "answer", (takeReplied caller).mint "exit"] ∧
      ∀ name ∈ [(named caller).mint "cursor", (looped caller).mint "answer",
          (takeRow caller).mint "answer", (takeReplied caller).mint "exit"],
        name ≠ (masked caller).mint "answer" := by
  refine ⟨by simp only [takeWithdrawRow, takeReplied, takeRow, looped, named, Env.push,
    List.append_assoc, List.cons_append, List.nil_append], fun name member => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
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
  · exact later_mint_ne_answer (b := 101)
      (by simp only [takeReplied, takeRow, looped, named, Env.push_length, List.length_cons,
        List.length_nil]; omega)
      (by decide) (Or.inr (by decide))

/-- **A visit's row: the scope binds the walk's cursor last**, so no later binder exists. -/
theorem walkRow_cursor (caller : Env) :
    (walkRow caller).names = (released caller).names ++ (released caller).mint "cursor" :: [] ∧
      ∀ name ∈ ([] : Names), name ≠ (released caller).mint "cursor" :=
  ⟨rfl, fun _ member => absurd member List.not_mem_nil⟩

-- Red control of the premise: where a later binder has the identity's own name, the name
-- resolves to the later level, and a step would read that binder's value there.
#guard Names.resolve
  ((masked {}).names ++ [(masked {}).mint "answer", "x", (masked {}).mint "answer"])
  ((masked {}).mint "answer") == some 3
-- With no such binder it resolves to its own level, one above the mask's saved state.
#guard Names.resolve ((masked {}).names ++ [(masked {}).mint "answer", "x"])
  ((masked {}).mint "answer") == some 1
-- The row's own binder and a loop's cursor are two names, though their stems begin alike.
#guard (walkRow {}).mint "current" != (released {}).mint "cursor"

/-! Each law at the operations' own binders. The premises that stay are the caller's context:
the typed environment, the request's two handles or the cursor at their levels, the count's
variable, the cell's value and its membership. No premise on a minted name stays. Each example's
conclusion is its law's. -/

/-- A caller's variable keeps its level under a row's own binder: an author's name is no minted
name. A step of the two lemmas below. -/
theorem countBound {row : Env} {x : String} {level : Nat} (written : Name.reserved x = false)
    (bound : row.names.resolve x = some level) :
    (row.push [row.mint "current"]).names.resolve x = some level :=
  (Names.resolve_append_ne (fun same => written_ne_mint written _ "current" same.symm)
    row.names).trans bound

/-- A caller's variable under a row's own binder reads the value at its level. A step of the
examples below, for the count. -/
theorem countReads {row : Env} {x : String} {level : Nat} {captured : List Val} {v : Val}
    (path : List Nat) (cell : Val) (written : Name.reserved x = false)
    (bound : row.names.resolve x = some level) (countHeld : captured[level]? = some v) :
    Reads (var x) (row.push [row.mint "current"]) path (captured ++ [cell]) v :=
  ⟨.var level, var_tree written (countBound written bound) path,
    (List.getElem?_append_left (List.getElem?_eq_some_iff.mp countHeld).1).trans countHeld⟩

/-- The typed twin: the variable has the type at its level. -/
theorem countTypes {row : Env} {x : String} {level : Nat} {tys : List Ty} {T : Ty}
    (sig : Signature NativeOp) (path : List Nat) (C : Ty) (written : Name.reserved x = false)
    (bound : row.names.resolve x = some level) (countTyped : tys[level]? = some T) :
    TypesEach sig (var x) (row.push [row.mint "current"]) path (tys ++ [C]) T :=
  types_var written (countBound written bound)
    ((List.getElem?_append_left (List.getElem?_eq_some_iff.mp countTyped).1).trans countTyped)

/-- The take's attempt at its own binders, in `take` and in `withPermits`. The count is a
variable that the caller reads through `var`: it keeps its level under the row's own binder. -/
example (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy) (tb : Table)
    (s : Semaphore.Model.State) (id n : Nat) (hint : DeferredKey) (injective : tb.Injective)
    (caller : Env) (path : List Nat) (tys : List Ty) (w : Typed.World) (captured : List Val)
    (x : String) (level : Nat) (written : Name.reserved x = false)
    (bound : (takeRow caller).names.resolve x = some level)
    (depth : captured.length = (takeRow caller).names.length)
    (tyDepth : tys.length = (takeRow caller).names.length) (typedEnv : EnvTyped w tys captured)
    (idHeld : captured[(masked caller).names.length]? = some (Val.promise (tb.handle id)))
    (idTyped : tys[(masked caller).names.length]? = some idTy)
    (hintHeld : captured[(looped caller).names.length]? = some (Val.promise hint))
    (hintTyped : tys[(looped caller).names.length]? = some idTy)
    (countHeld : captured[level]? = some (Val.nat n)) (countTyped : tys[level]? = some .nat)
    (stores : Stores) (q : RefKey) (held : refPeek stores.refs q = some (cellVal tb s))
    (member : Fits w (cellVal tb s) Semaphore.cellTy) :=
  Semaphore.take_attempt_minted sig atoms tb s id n hint injective (path := path)
    (countSrc := var x) depth tyDepth typedEnv (takeRow_identity caller).1
    (takeRow_identity caller).2 idHeld idTyped (takeRow_hint caller).1 (takeRow_hint caller).2
    hintHeld hintTyped (countReads path _ written bound countHeld)
    (countTypes sig path _ written bound countTyped) held member

/-- The take's withdrawal at its own binders. -/
example (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy) (tb : Table)
    (s : Semaphore.Model.State) (id : Nat) (injective : tb.Injective) (caller : Env)
    (path : List Nat) (tys : List Ty) (w : Typed.World) (captured : List Val)
    (depth : captured.length = (takeWithdrawRow caller).names.length)
    (tyDepth : tys.length = (takeWithdrawRow caller).names.length)
    (typedEnv : EnvTyped w tys captured)
    (idHeld : captured[(masked caller).names.length]? = some (Val.promise (tb.handle id)))
    (idTyped : tys[(masked caller).names.length]? = some idTy)
    (stores : Stores) (q : RefKey) (held : refPeek stores.refs q = some (cellVal tb s))
    (member : Fits w (cellVal tb s) Semaphore.cellTy) :=
  Semaphore.take_withdrawal_minted sig atoms tb s id injective (path := path) depth tyDepth
    typedEnv (takeWithdrawRow_identity caller).1 (takeWithdrawRow_identity caller).2 idHeld
    idTyped held member

/-- A visit of the walk at the walk's own binder: the cursor holds an option of a stamp. -/
example (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy) (tb : Table)
    (s : Semaphore.Model.State) (cursor : Nat) (caller : Env) (path : List Nat) (tys : List Ty)
    (w : Typed.World) (captured : List Val)
    (depth : captured.length = (walkRow caller).names.length)
    (tyDepth : tys.length = (walkRow caller).names.length) (typedEnv : EnvTyped w tys captured)
    (cursorHeld : captured[(released caller).names.length]? =
      some (Store.Val.some (Val.nat cursor)))
    (cursorTyped : tys[(released caller).names.length]? = some (.option .nat))
    (stores : Stores) (q : RefKey) (held : refPeek stores.refs q = some (cellVal tb s))
    (member : Fits w (cellVal tb s) Semaphore.cellTy) :=
  Semaphore.visit_attempt_minted sig atoms tb s cursor (path := path) depth tyDepth typedEnv
    (walkRow_cursor caller).1 (walkRow_cursor caller).2 cursorHeld cursorTyped held member

/-- The release's step at a row's scope, with the count a caller's variable: the caller's own
scope in `release`, and `hookRow` in a protected form. -/
example (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy) (tb : Table)
    (s : Semaphore.Model.State) (n : Nat) (row : Env) (path : List Nat) (tys : List Ty)
    (w : Typed.World) (captured : List Val) (x : String) (level : Nat)
    (written : Name.reserved x = false) (bound : row.names.resolve x = some level)
    (depth : captured.length = row.names.length) (tyDepth : tys.length = row.names.length)
    (typedEnv : EnvTyped w tys captured) (countHeld : captured[level]? = some (Val.nat n))
    (countTyped : tys[level]? = some .nat) (stores : Stores) (q : RefKey)
    (held : refPeek stores.refs q = some (cellVal tb s))
    (member : Fits w (cellVal tb s) Semaphore.cellTy) :=
  Semaphore.release_attempt sig atoms tb s n (path := path) (countSrc := var x) depth tyDepth
    typedEnv (countReads path _ written bound countHeld)
    (countTypes sig path _ written bound countTyped) held member

/-- The step that never waits at a row's scope, with the count a caller's variable: the
caller's own scope in `takeIfAvailable`, and `masked` in `withPermitsIfAvailable`. -/
example (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy) (tb : Table)
    (s : Semaphore.Model.State) (n : Nat) (row : Env) (path : List Nat) (tys : List Ty)
    (w : Typed.World) (captured : List Val) (x : String) (level : Nat)
    (written : Name.reserved x = false) (bound : row.names.resolve x = some level)
    (depth : captured.length = row.names.length) (tyDepth : tys.length = row.names.length)
    (typedEnv : EnvTyped w tys captured) (countHeld : captured[level]? = some (Val.nat n))
    (countTyped : tys[level]? = some .nat) (stores : Stores) (q : RefKey)
    (held : refPeek stores.refs q = some (cellVal tb s))
    (member : Fits w (cellVal tb s) Semaphore.cellTy) :=
  Semaphore.takeIfAvailable_attempt sig atoms tb s n (path := path) (countSrc := var x) depth
    tyDepth typedEnv (countReads path _ written bound countHeld)
    (countTypes sig path _ written bound countTyped) held member

end OwnBinders

/-! ### Each statement's term is the term of the operation's own row

The scopes above are written by hand, binder by binder. The guards below bind them to the
operations: at each caller's scope, the term that the operation's tree holds in its row is the
tree of the statement's term at the scope that the statement names. A scope with one binder
too many or too few gives another tree, so the guard fails. -/

/-- The masked body of an operation: under the getter's `bind` and the mask. -/
def maskedBody : Eff NativeOp → Option (Eff NativeOp)
  | .bind (.withFiber .getInterruptible) (.uninterruptible body) => some body
  | _ => none

/-- The body of a node under `uninterruptible`. -/
def unmasked : Eff NativeOp → Option (Eff NativeOp)
  | .uninterruptible body => some body
  | _ => none

/-- The term of a row, alone or at the head of a sequence. -/
def rowTerm : Eff NativeOp → Option Term
  | .perform (.refModifyWith f) _ => some f
  | .bind (.perform (.refModifyWith f) _) _ => some f
  | _ => none

/-- The wrapper's loop at a restore site: the round's body, after the hint's allocation. -/
def loopAttempt : Eff NativeOp → Option (Eff NativeOp)
  | .bind _ (.bind (.iterate _ _ _ _ _ (.bind _ attempt)) _) => some attempt
  | _ => none

/-- The withdrawal inside an attempt: the second arm of the take's choice is the wait, and the
first arm of the test of the wait's exit is the withdrawal. -/
def withdrawalOf : Eff NativeOp → Option (Eff NativeOp)
  | .bind _ (.select _ _ _ (.bind (.onExit _ (.select _ _ cleanup _)) _)) => some cleanup
  | _ => none

/-- A protected form's acquisition: the first node under the mask. -/
def acquisitionOf : Eff NativeOp → Option (Eff NativeOp)
  | .bind acquire (.onExit _ _) => some acquire
  | _ => none

/-- A protected form's hook. -/
def hookOf : Eff NativeOp → Option (Eff NativeOp)
  | .bind _ (.onExit _ hook) => some hook
  | _ => none

/-- The helper's body in a release: the fork in the first arm of the test of the reply. -/
def helperOf : Eff NativeOp → Option (Eff NativeOp)
  | .bind _ (.bind (.select _ _ (.bind (.withFiber (.fork helper _)) _) _) _) => some helper
  | _ => none

/-- The body of a loop. -/
def loopBody : Eff NativeOp → Option (Eff NativeOp)
  | .iterate _ _ _ _ _ body => some body
  | _ => none

/-- A statement's term at a row's scope, under the row's own binder. -/
def termUnder (row : Env) (step : TermSrc → TermSrc) : Option Term :=
  (step (minted (row.mint "current")) (row.push [row.mint "current"]) []).toOption

/-- The callers' scopes of the binding: a handle and a count alone, between two names, and
beside two names under the reserved prefix. -/
def callers : List (List String) :=
  [["q", "n"], ["x", "q", "n", "y"], ["q", "_%answer3", "n", "_%current5"]]

/-- The take step of a statement, at a caller's scope: the caller's count, and the identity and
the hint under the names that the two `bindWith`s mint. -/
def takeTerm (caller : Env) : Option Term :=
  termUnder (takeRow caller)
    (Semaphore.takeStep (var "n") (minted ((masked caller).mint "answer"))
      (minted ((looped caller).mint "answer")))

/-- The withdrawal of a statement, at a caller's scope. -/
def withdrawTerm (caller : Env) : Option Term :=
  termUnder (takeWithdrawRow caller)
    (Semaphore.withdrawStep (minted ((masked caller).mint "answer")))

-- `take`: the attempt's row is the take step at `takeRow`, and the withdrawal's row is the
-- withdrawal at `takeWithdrawRow`.
#guard callers.all fun names =>
  let caller : Env := { names := names }
  let attempt := ((treeAt names (Semaphore.take (var "q") (var "n"))).bind maskedBody).bind
    loopAttempt
  (takeTerm caller).isSome && attempt.bind rowTerm == takeTerm caller &&
    (withdrawTerm caller).isSome &&
    (attempt.bind withdrawalOf).bind rowTerm == withdrawTerm caller
-- `withPermits`: the acquisition is the same loop at the same scope, so its two rows are the
-- same two terms. The hook's row is the release step at `hookRow`.
#guard callers.all fun names =>
  let caller : Env := { names := names }
  let form := (treeAt names (Semaphore.withPermits (var "q") (var "n") (succeed (nat 1)))).bind
    maskedBody
  let attempt := (form.bind acquisitionOf).bind loopAttempt
  attempt.bind rowTerm == takeTerm caller &&
    (attempt.bind withdrawalOf).bind rowTerm == withdrawTerm caller &&
    (termUnder (hookRow caller) (Semaphore.releaseStep (var "n"))).isSome &&
    ((form.bind hookOf).bind unmasked).bind rowTerm ==
      termUnder (hookRow caller) (Semaphore.releaseStep (var "n"))
-- `release`: the row stands at the caller's own scope, under the mask alone. The helper's
-- body is the walk, and a visit's row is the visit step at `walkRow`, with the cursor under
-- the name that the walk's loop mints, read through `getOrElse`.
#guard callers.all fun names =>
  let caller : Env := { names := names }
  let body := (treeAt names (Semaphore.release (var "q") (var "n"))).bind unmasked
  let visit := termUnder (walkRow caller)
    (Semaphore.visitStep (app "getOrElse" [minted ((released caller).mint "cursor"), nat 0]))
  (termUnder caller (Semaphore.releaseStep (var "n"))).isSome &&
    body.bind rowTerm == termUnder caller (Semaphore.releaseStep (var "n")) &&
    visit.isSome && ((body.bind helperOf).bind loopBody).bind rowTerm == visit
-- `takeIfAvailable`: the row stands at the caller's own scope. `withPermitsIfAvailable`: the
-- same step is the acquisition, under the mask's saved state.
#guard callers.all fun names =>
  let caller : Env := { names := names }
  let form := (treeAt names
    (Semaphore.withPermitsIfAvailable (var "q") (var "n") (succeed (nat 1)))).bind maskedBody
  (termUnder caller (Semaphore.takeIfAvailableStep (var "n"))).isSome &&
    (treeAt names (Semaphore.takeIfAvailable (var "q") (var "n"))).bind rowTerm ==
      termUnder caller (Semaphore.takeIfAvailableStep (var "n")) &&
    (form.bind acquisitionOf).bind rowTerm ==
      termUnder (masked caller) (Semaphore.takeIfAvailableStep (var "n"))

-- Red control of the binding: at a scope with one binder fewer, the statement's term is
-- another tree. Here the take step is read at the scope before the hint's binder.
#guard callers.all fun names =>
  let caller : Env := { names := names }
  (((treeAt names (Semaphore.take (var "q") (var "n"))).bind maskedBody).bind
      loopAttempt).bind rowTerm !=
    termUnder (looped caller)
      (Semaphore.takeStep (var "n") (minted ((masked caller).mint "answer"))
        (minted ((looped caller).mint "answer")))
-- Red control of the two names: with the identity and the hint exchanged, another tree.
#guard callers.all fun names =>
  let caller : Env := { names := names }
  (((treeAt names (Semaphore.take (var "q") (var "n"))).bind maskedBody).bind
      loopAttempt).bind rowTerm !=
    termUnder (takeRow caller)
      (Semaphore.takeStep (var "n") (minted ((looped caller).mint "answer"))
        (minted ((masked caller).mint "answer")))
-- Red control of the cursor's reading: a visit at the cursor's name with no `getOrElse` is
-- another tree.
#guard callers.all fun names =>
  let caller : Env := { names := names }
  ((((treeAt names (Semaphore.release (var "q") (var "n"))).bind unmasked).bind helperOf).bind
      loopBody).bind rowTerm !=
    termUnder (walkRow caller)
      (Semaphore.visitStep (minted ((released caller).mint "cursor")))

/-! ## 5. Hygiene: a caller's variable keeps its reading

**The promise.** A variable that a caller reads through `var` keeps its reading inside an
operation: every binder of the operation is minted, a minted name is reserved, and an author's
name is not (`var_push_minted`, `src/Effect4/Laws/Program/Author.lean`). The same holds inside
a protected body. It is no promise for an arbitrary source term, which is a function of its
scope: the last control below is one.

**The names.** The fixtures of the earlier slice wrote seven names
(`Written`, `Test/Program/SemaphoreScenarios.lean`). Six stand around a caller's variable: `id`,
`hint`, `took` and `e` around the handle of a take, `r` around the handle of a release, and
`s` around a count in each row. One stands around none: `w`, the walk's selected waiter.

**The control of one name.** A client holds the handle, or a count, in a variable of that name.
Over the library's operations its tree is the tree of the same client under another name. Over
the written forms it is another tree: the variable reads the operation's own binder. -/

section Hygiene

open Test.Program.SemaphoreScenarios (Written.ops)

/-- A client that holds the handle and a count in variables of given names, and takes. -/
def takeHolding (ops : Ops) (handle count : String) : Src NativeOp :=
  bindName handle (Semaphore.make 2) fun q =>
    bindName count (succeed (nat 1)) fun n => ops.take q n

/-- A client that holds the handle and a count, and releases. -/
def releaseHolding (ops : Ops) (handle count : String) : Src NativeOp :=
  bindName handle (Semaphore.make 2) fun q =>
    bindName count (succeed (nat 1)) fun n => ops.release q n

/-- A client that holds the handle and a count, and runs a protected body that reads the
handle. -/
def protectedHolding (ops : Ops) (handle count : String) : Src NativeOp :=
  bindName handle (Semaphore.make 2) fun q =>
    bindName count (succeed (nat 1)) fun n => ops.withPermits q n (Ref.get q)

/-- A client's tree does not depend on its variable's name: it elaborates, and its tree is the
tree of the same client under a name that nobody writes. -/
def keeps (client : String → Src NativeOp) (name : String) : Bool :=
  (elaborate (client name)).toOption.isSome &&
    elaborate (client name) == elaborate (client "caller_")

/-- The seven names that the fixtures wrote. -/
def writtenNames : List String := ["id", "hint", "took", "r", "w", "e", "s"]

-- The library's operations: a caller's variable of each written name keeps its reading, as
-- the handle and as the count of a take, of a release and of a protected form.
#guard writtenNames.all fun name =>
  keeps (fun x => takeHolding library x "count_") name &&
    keeps (fun x => takeHolding library "handle_" x) name &&
    keeps (fun x => releaseHolding library x "count_") name &&
    keeps (fun x => releaseHolding library "handle_" x) name &&
    keeps (fun x => protectedHolding library x "count_") name &&
    keeps (fun x => protectedHolding library "handle_" x) name
-- The two forms that never wait keep it too.
#guard writtenNames.all fun name =>
  keeps (fun x => bindName x (Semaphore.make 2) fun q =>
    Semaphore.withPermitsIfAvailable q (nat 1) (Ref.get q)) name &&
  keeps (fun x => bindName "handle_" (Semaphore.make 2) fun q =>
    bindName x (succeed (nat 1)) fun n => Semaphore.takeIfAvailable q n) name
-- Red controls, one for each name that stands around a caller's variable. Over the written
-- forms the handle of a take under `id`, `hint`, `took` or `e` reads the operation's own
-- binder, and so does its count under `id`, `hint` or `s`.
#guard writtenNames.filter (fun name => !keeps (fun x => takeHolding Written.ops x "count_") name) =
  ["id", "hint", "took", "e"]
#guard writtenNames.filter (fun name => !keeps (fun x => takeHolding Written.ops "handle_" x) name) =
  ["id", "hint", "s"]
-- A release: the handle under `r`, and the count under `s`.
#guard writtenNames.filter
    (fun name => !keeps (fun x => releaseHolding Written.ops x "count_") name) = ["r"]
#guard writtenNames.filter
    (fun name => !keeps (fun x => releaseHolding Written.ops "handle_" x) name) = ["s"]
-- A protected form holds a take and a release: the union of their names.
#guard writtenNames.filter
    (fun name => !keeps (fun x => protectedHolding Written.ops x "count_") name) =
  ["id", "hint", "took", "r", "e"]
#guard writtenNames.filter
    (fun name => !keeps (fun x => protectedHolding Written.ops "handle_" x) name) =
  ["id", "hint", "e", "s"]
-- So the six names of the capture are `id`, `hint`, `took`, `r`, `e` and `s`, and `w` stands
-- around no caller's variable.

-- The checker catches each of these captures: the captured value has another type. No binder
-- of a written form has a handle's type or a count's type.
#guard ["id", "hint", "took", "e"].all fun name =>
  verdict (takeHolding Written.ops name "count_") = "typing: requestNotSubtype" &&
    verdict (takeHolding library name "count_") = "built"
#guard ["id", "hint", "s"].all fun name =>
  verdict (takeHolding Written.ops "handle_" name) = "typing: binderTerm" &&
    verdict (takeHolding library "handle_" name) = "built"
#guard verdict (releaseHolding Written.ops "r" "count_") = "typing: requestNotSubtype" &&
  verdict (releaseHolding Written.ops "handle_" "s") = "typing: binderTerm" &&
  verdict (releaseHolding library "r" "count_") = "built" &&
  verdict (releaseHolding library "handle_" "s") = "built"

/-! ### The promise's boundary: a source term that is no variable read through `var`

A minted reader is a function of its scope. Here a hand-made scope holds the name that the
wrapper mints for the request's identity at that depth. A caller's term that reads that name
through `minted` reads the identity inside the operation, and the handle outside it. No author
can write such a name through `var`, which refuses the reserved prefix. -/

-- The caller's scope is one name, at depth 1. The wrapper mints `_%restore1` and then the
-- identity's name at depth 2: the name that this scope already holds.
#guard (masked { names := ["_%answer2"] }).mint "answer" == "_%answer2"
-- At the caller's scope the term reads level 0. In the take's row it reads level 2, the
-- identity: the row's request is the identity's variable, and not the caller's.
#guard (minted "_%answer2" { names := ["_%answer2"] } []).toOption == some (Term.var 0)
#guard (((treeAt ["_%answer2"] (Semaphore.take (minted "_%answer2") (nat 1))).bind
      maskedBody).bind loopAttempt).map
    (fun attempt => match attempt with
      | .bind (.perform (.refModifyWith _) request) _ => request == Term.var 2
      | _ => false) == some true
-- A variable read through `var` cannot be that name: the scope reader refuses it.
#guard (var "_%answer2" { names := ["_%answer2"] } []).toOption.isNone
-- And an author's variable in the same place reads its own level, 0.
#guard (((treeAt ["q"] (Semaphore.take (var "q") (nat 1))).bind maskedBody).bind
      loopAttempt).map
    (fun attempt => match attempt with
      | .bind (.perform (.refModifyWith _) request) _ => request == Term.var 0
      | _ => false) == some true

end Hygiene

/-! ## 6. Typing at every scope

`take_types` and its five siblings type each operation at every typed scope
(`src/Effect4/Laws/Modules/Semaphore/Ops.lean`). The examples read each at a caller's variables:
a variable that an author wrote is a kept term, at every scope that binds it. The guards run the
checker on each operation's tree, so each statement has a finite control with the checker's own
answer. -/

section Typing

open Effect4.Semaphore.Model
open Effect4.Machine.Env (Requirement)
open Conform.Effect4.Typing

-- `take` and `release` at two variables: the handle and the count.
example (table : RowTable) (s : TypedScope) (i j : Nat)
    (bound : s.env.names.resolve "q" = some i)
    (held : s.types[i]? = some (.refOf Semaphore.cellTy))
    (boundN : s.env.names.resolve "n" = some j) (heldN : s.types[j]? = some .nat) :
    Answers (nativeSignature table) (Semaphore.take (var "q") (var "n")) s .nat ∧
      Answers (nativeSignature table) (Semaphore.release (var "q") (var "n")) s .nat :=
  ⟨Semaphore.take_types (kept_var rfl bound held) (kept_var rfl boundN heldN),
    Semaphore.release_types (kept_var rfl bound held) (kept_var rfl boundN heldN)⟩

-- `take` of a number literal.
example (table : RowTable) (s : TypedScope) (i : Nat)
    (bound : s.env.names.resolve "q" = some i)
    (held : s.types[i]? = some (.refOf Semaphore.cellTy)) (n : Nat) :
    Answers (nativeSignature table) (Semaphore.take (var "q") (nat n)) s .nat :=
  Semaphore.take_types (kept_var rfl bound held) fun _ _ _ => types_nat n

-- `takeIfAvailable` reads the handle at its own scope.
example (table : RowTable) (s : TypedScope) (i : Nat)
    (bound : s.env.names.resolve "q" = some i)
    (held : s.types[i]? = some (.refOf Semaphore.cellTy)) (n : Nat) :
    Answers (nativeSignature table) (Semaphore.takeIfAvailable (var "q") (nat n)) s .bool :=
  Semaphore.takeIfAvailable_types (kept_var rfl bound held).here fun _ _ _ => types_nat n

-- The construction, at every typed scope and every positive total.
example (table : RowTable) (s : TypedScope) :
    Answers (nativeSignature table) (Semaphore.make 3) s (.refOf Semaphore.cellTy) :=
  Semaphore.make_types 3 (by decide) s

-- `withPermits` with a body that answers a number at every scope: the form answers that
-- number, with no failure and no requirement.
example (table : RowTable) (s : TypedScope) (i : Nat)
    (bound : s.env.names.resolve "q" = some i)
    (held : s.types[i]? = some (.refOf Semaphore.cellTy)) :
    Has (nativeSignature table) (Semaphore.withPermits (var "q") (nat 1) (succeed (nat 7))) s
      (EffTy.pure .nat) :=
  Semaphore.withPermits_types (b := EffTy.pure .nat) (kept_var rfl bound held)
    (fun _ _ _ => types_nat 1) fun _ _ => (answers_succeed fun _ => types_nat 7).has

-- `withPermits` with a body that fails with a number: the form keeps the failure type.
example (table : RowTable) (s : TypedScope) (i : Nat)
    (bound : s.env.names.resolve "q" = some i)
    (held : s.types[i]? = some (.refOf Semaphore.cellTy)) :
    Has (nativeSignature table) (Semaphore.withPermits (var "q") (nat 1) (fail (nat 3))) s
      ⟨.never, .nat, Requirement.empty⟩ :=
  Semaphore.withPermits_types (b := ⟨.never, .nat, Requirement.empty⟩)
    (kept_var rfl bound held) (fun _ _ _ => types_nat 1) fun _ _ _ =>
      ⟨.fail (.lit (.nat 3)), rfl, effTy_complete _ _ _ _ (.fail rfl rfl)⟩

-- `withPermitsIfAvailable` with a body that answers a number: an option of that number.
example (table : RowTable) (s : TypedScope) (i : Nat)
    (bound : s.env.names.resolve "q" = some i)
    (held : s.types[i]? = some (.refOf Semaphore.cellTy)) :
    Has (nativeSignature table)
      (Semaphore.withPermitsIfAvailable (var "q") (nat 1) (succeed (nat 7))) s
      (EffTy.pure (.option .nat)) :=
  Semaphore.withPermitsIfAvailable_types (b := EffTy.pure .nat) rfl (kept_var rfl bound held)
    (fun _ _ _ => types_nat 1) fun _ _ => (answers_succeed fun _ => types_nat 7).has

/-- The checker's answer on a source's tree, at a scope of names and their types. -/
def answerAt (names : List String) (types : List Ty) (src : Src NativeOp) : Option EffTy :=
  (src { names := names } []).toOption.bind (effTy nativeSignature types)

/-- Each operation at one scope of a handle and a count, with other names around them: the
checker answers the operation's type, with no failure and no requirement. -/
def operationsTyped (names : List String) (types : List Ty) : Bool :=
  decide (answerAt names types (Semaphore.take (var "q") (var "n")) = some (EffTy.pure .nat)) &&
  decide (answerAt names types (Semaphore.release (var "q") (var "n")) =
    some (EffTy.pure .nat)) &&
  decide (answerAt names types (Semaphore.takeIfAvailable (var "q") (var "n")) =
    some (EffTy.pure .bool)) &&
  decide (answerAt names types (Semaphore.withPermits (var "q") (var "n") (succeed (var "n"))) =
    some (EffTy.pure .nat)) &&
  decide (answerAt names types
    (Semaphore.withPermitsIfAvailable (var "q") (var "n") (succeed (var "n"))) =
      some (EffTy.pure (.option .nat))) &&
  decide (answerAt names types (Semaphore.make 2) = some (EffTy.pure (.refOf Semaphore.cellTy)))

-- At three scopes: the two names alone, the two names between others, and a scope that holds
-- names under the reserved prefix.
#guard operationsTyped ["q", "n"] [.refOf Semaphore.cellTy, .nat]
#guard operationsTyped ["x", "q", "n", "y"] [.bool, .refOf Semaphore.cellTy, .nat, .string]
#guard operationsTyped ["q", "_%answer1", "n", "_%restore3", "_%current4"]
  [.refOf Semaphore.cellTy, .bool, .nat, .bool, .unit]
-- A protected body that fails with a number: the checker answers the body's failure type.
#guard answerAt ["q", "n"] [.refOf Semaphore.cellTy, .nat]
    (Semaphore.withPermits (var "q") (var "n") (fail (nat 3))) =
  some ⟨.never, .nat, Requirement.empty⟩
#guard answerAt ["q", "n"] [.refOf Semaphore.cellTy, .nat]
    (Semaphore.withPermitsIfAvailable (var "q") (var "n") (fail (nat 3))) =
  some ⟨.option .never, .nat, Requirement.empty⟩
-- Red control: a count of another type has no answer, at each operation that takes one.
#guard [Semaphore.take (var "q") (var "n"), Semaphore.release (var "q") (var "n"),
    Semaphore.takeIfAvailable (var "q") (var "n"),
    Semaphore.withPermits (var "q") (var "n") (succeed unit),
    Semaphore.withPermitsIfAvailable (var "q") (var "n") (succeed unit)].all fun operation =>
  decide (answerAt ["q", "n"] [.refOf Semaphore.cellTy, .bool] operation = none)
-- Red control: a handle that is no cell's handle has no answer.
#guard [Semaphore.take (var "q") (var "n"), Semaphore.release (var "q") (var "n"),
    Semaphore.takeIfAvailable (var "q") (var "n"),
    Semaphore.withPermits (var "q") (var "n") (succeed unit),
    Semaphore.withPermitsIfAvailable (var "q") (var "n") (succeed unit)].all fun operation =>
  decide (answerAt ["q", "n"] [.nat, .nat] operation = none)
-- Red control: a cell at another record type has no answer: the step's type is no pair of a
-- reply and that cell's type.
#guard answerAt ["q", "n"] [.refOf Semaphore.waiterTy, .nat]
  (Semaphore.take (var "q") (var "n")) = none

end Typing

/-! ## The example of `README.md`

The section "A semaphore" of `README.md` shows this program. It is the program
`pSemaphoreHandoff` of the truth lane (`harness/truth/Truth.lean`). -/

/-- The README's example, as the README writes it. The root takes the one permit. A worker asks
for it in the protected form, and it waits. The root releases: the walk resumes the worker,
which runs its body and releases. -/
def handoff : Src NativeOp := eff do
  let gate ← Semaphore.make 1
  let _ ← Semaphore.take gate (nat 1)
  let worker ← fork (Semaphore.withPermits gate (nat 1) (succeed (nat 7)))
  let free ← Semaphore.release gate (nat 1)
  let x ← join worker
  return tuple [free, x]

-- `Effect4.Api.author` checks it at the pair of two numbers, with no failure and no
-- requirement, and its run answers the free count of the release and the worker's answer.
#guard match Effect4.Api.author handoff with
  | .ok typed => decide (typed.ty = EffTy.pure (.prod .nat .nat)) &&
      typed.runSync == .success (Val.list [.nat 1, .nat 7])
  | .error _ => false
-- Red control: with a count of another type, the checker refuses the program at a type.
#guard match Effect4.Api.author (eff do
    let gate ← Semaphore.make 1
    let a ← Semaphore.take gate (bool true)
    return a) with
  | .error (.typing _) => true
  | _ => false

/-! ## 7. The pinned outputs

Each law's axioms, and its standing as the plan derives it from its proof. No law rests on a
planned goal. The counts are of this battery's tree, which holds no step of a proof. -/

-- The attempt laws, and their forms at the operations' own binders.
/-- info: 'Effect4.Semaphore.take_attempt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Effect4.Semaphore.take_attempt

/-- info: 'Effect4.Semaphore.take_withdrawal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Effect4.Semaphore.take_withdrawal

/-- info: 'Effect4.Semaphore.release_attempt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Effect4.Semaphore.release_attempt

/-- info: 'Effect4.Semaphore.takeIfAvailable_attempt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Effect4.Semaphore.takeIfAvailable_attempt

/-- info: 'Effect4.Semaphore.visit_attempt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Effect4.Semaphore.visit_attempt

/-- info: 'Effect4.Semaphore.make_makes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Effect4.Semaphore.make_makes

/-- info: 'Effect4.Semaphore.take_attempt_minted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Effect4.Semaphore.take_attempt_minted

/-- info: 'Effect4.Semaphore.take_withdrawal_minted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Effect4.Semaphore.take_withdrawal_minted

/-- info: 'Effect4.Semaphore.visit_attempt_minted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Effect4.Semaphore.visit_attempt_minted

/--
info: Effect4.Semaphore.take_attempt: proved; nearest []; 0 lemmas, 0 definitions
Effect4.Semaphore.take_withdrawal: proved; nearest []; 0 lemmas, 0 definitions
Effect4.Semaphore.release_attempt: proved; nearest []; 0 lemmas, 0 definitions
Effect4.Semaphore.takeIfAvailable_attempt: proved; nearest []; 0 lemmas, 0 definitions
Effect4.Semaphore.visit_attempt: proved; nearest []; 0 lemmas, 0 definitions
Effect4.Semaphore.make_makes: proved; nearest []; 0 lemmas, 0 definitions
Effect4.Semaphore.take_attempt_minted: proved; nearest [Effect4.Semaphore.take_attempt]; 0 lemmas, 0 definitions
Effect4.Semaphore.take_withdrawal_minted: proved; nearest [Effect4.Semaphore.take_withdrawal]; 0 lemmas, 0 definitions
Effect4.Semaphore.visit_attempt_minted: proved; nearest [Effect4.Semaphore.visit_attempt]; 0 lemmas, 0 definitions
next goals: 0
-/
#guard_msgs in
#plan_status Effect4.Semaphore.take_attempt Effect4.Semaphore.take_withdrawal
  Effect4.Semaphore.release_attempt Effect4.Semaphore.takeIfAvailable_attempt
  Effect4.Semaphore.visit_attempt Effect4.Semaphore.make_makes
  Effect4.Semaphore.take_attempt_minted Effect4.Semaphore.take_withdrawal_minted
  Effect4.Semaphore.visit_attempt_minted

-- The typing statements of section 6.
/-- info: 'Effect4.Semaphore.make_types' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Effect4.Semaphore.make_types

/-- info: 'Effect4.Semaphore.takeIfAvailable_types' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Effect4.Semaphore.takeIfAvailable_types

/-- info: 'Effect4.Semaphore.release_types' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Effect4.Semaphore.release_types

/-- info: 'Effect4.Semaphore.take_types' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Effect4.Semaphore.take_types

/-- info: 'Effect4.Semaphore.withPermits_types' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Effect4.Semaphore.withPermits_types

/--
info: 'Effect4.Semaphore.withPermitsIfAvailable_types' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Effect4.Semaphore.withPermitsIfAvailable_types

/--
info: Effect4.Semaphore.make_types: proved; nearest []; 0 lemmas, 0 definitions
Effect4.Semaphore.takeIfAvailable_types: proved; nearest []; 0 lemmas, 0 definitions
Effect4.Semaphore.release_types: proved; nearest []; 0 lemmas, 0 definitions
Effect4.Semaphore.take_types: proved; nearest []; 0 lemmas, 0 definitions
Effect4.Semaphore.withPermits_types: proved; nearest [Effect4.Semaphore.release_types]; 0 lemmas, 0 definitions
Effect4.Semaphore.withPermitsIfAvailable_types: proved; nearest [Effect4.Semaphore.release_types, Effect4.Semaphore.takeIfAvailable_types]; 0 lemmas, 0 definitions
next goals: 0
-/
#guard_msgs in
#plan_status Effect4.Semaphore.make_types Effect4.Semaphore.takeIfAvailable_types
  Effect4.Semaphore.release_types Effect4.Semaphore.take_types
  Effect4.Semaphore.withPermits_types Effect4.Semaphore.withPermitsIfAvailable_types

-- Four scope laws, and the rules that the walk's typing and its attempt law are proved through.
/-- info: 'Effect4.Semaphore.take_scoped' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Effect4.Semaphore.take_scoped

/-- info: 'Effect4.Semaphore.release_scoped' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Effect4.Semaphore.release_scoped

/-- info: 'Effect4.Semaphore.withPermits_scoped' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Effect4.Semaphore.withPermits_scoped

/--
info: 'Effect4.Semaphore.withPermitsIfAvailable_scoped' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Effect4.Semaphore.withPermitsIfAvailable_scoped

/-- info: 'Effect4.Semaphore.walk_answers' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Effect4.Semaphore.walk_answers

/-- info: 'Effect4.Semaphore.taker_typed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Effect4.Semaphore.taker_typed

/-- info: 'Effect4.Semaphore.captured_cursorOr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Effect4.Semaphore.captured_cursorOr

/-- info: 'Effect4.Modules.kept_cursor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Effect4.Modules.kept_cursor

/-- info: 'Effect4.Modules.kept_payload' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Effect4.Modules.kept_payload

/-- info: 'Effect4.Modules.answers_iterateWith_kept' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Effect4.Modules.answers_iterateWith_kept

/--
info: 'Effect4.Modules.answers_refModifyWith_captured' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Effect4.Modules.answers_refModifyWith_captured

/--
info: 'Effect4.Modules.answers_selectOptionWith_kept' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Effect4.Modules.answers_selectOptionWith_kept

end Test.Program.SemaphoreOps
