import Effect4.Codegen.Print
import Effect4.Program.Native

/-!
# Codegen.Read — the printer's image back into `Eff` (lane A4 of the AST relation)

Plan: `docs/research/2026-09-04-a4-reader-plan.md`, under
`docs/research/2026-09-04-ast-relation-plan.md` §5.2. `readEff` is the inverse of `print`
(`Effect4/Codegen/Print.lean`) constructor by constructor, over the same target fragment
(`TypeScript.Expr`, `TypeScript.Stmt`): it takes a tree the printer could have produced
back to the `Eff` that produced it, and refuses by name every tree the printer never
produces. `ReadRefusal` is the closed refusal alphabet; a refusal is data, never a guess.

Two theorems state the relation. `read_print`: what the printer prints of a readable
program reads back to that program. `read_exact`: what the reader accepts prints back to
exactly the tree it read. `Readable` is what the printer loses and the reader cannot
recover — a variable out of scope, the request of a `unit`-request row (the printer drops
it), the `daemon` flag of a scoped fork (the fork options object has no such field), the
kind of a row (a `perform` and a `callback` on the same row print alike). `LawfulSpelling`
is what the reader needs of a signature: `spell` inverts the row table on
(spelling, trailing names), and no spelling or trailing name collides with a binder name,
`undefined`, or a reserved head.

Binders are recovered by comparison, never by decoding: `Var.read n s` is the position
`i < n` with `Var.name i = s`. Nothing here folds over a string (`String.toList` and its
kin reach `Classical.choice` on this toolchain); the injectivity of `Var.name` is proved
from the bytes of `Nat.repr`, which are a `List UInt8` the digits decode from.
-/

namespace Effect4.Program

open TypeScript (Expr Stmt)

/-! ## Refusals -/

/-- Why the reader declined a tree. -/
inductive ReadRefusal
  /-- A call whose head is a reserved name with no `Eff` reading in that position
  (`Cause.fail` outside a cause, `Effect.whileLoop` outside its suspend). -/
  | unknownHead (name : String)
  /-- An identifier that is no binder, no reserved name, and no value row. -/
  | unknownIdent (name : String)
  /-- A row called with an argument list its row table does not print. -/
  | arity (head : String)
  /-- A lambda, `const` or `step` parameter that is not the binder due at that position. -/
  | binder (expected : String)
  /-- Any other form the printer never emits; `what` names the position. -/
  | shape (what : String)
  /-- A negative integer literal. -/
  | negative (value : Int)
  /-- A statement form the printer never emits. -/
  | unsupportedStmt
deriving DecidableEq, Repr

/-! ## Binders -/

/-- The position `i < n` whose binder is `s`, searched from the newest binder down; `none`
when `s` is no binder of the first `n` positions. Comparison only: no digit is decoded. -/
def Var.read : Nat → String → Option Nat
  | 0, _ => none
  | n + 1, s => if Var.name n = s then some n else Var.read n s

/-! ## The reserved heads -/

/-- The fixed heads of the image, one per spelling the printer emits by name. -/
inductive Head
  | succeed | fail | failCause | sync | suspend | flatMap | gen | catchCause
  | matchCauseEffect | onExit | exit | uninterruptible | interruptible | whileLoop
  | yieldNowWith | join | await | forkChild | forkDetach | forkIn | forkScoped | runIn
  | interrupt | interruptAll | interruptAllAs | awaitAll | raceAll | context | fiberId
  | scopeClose | scoped | acquireRelease | causeFail | causeDie | causeInterrupt
  | causeCombine | undefined
deriving DecidableEq, Repr

/-- The spelling of each head, exactly as `print` emits it. -/
def Head.spelling : Head → String
  | .succeed => "Effect.succeed"
  | .fail => "Effect.fail"
  | .failCause => "Effect.failCause"
  | .sync => "Effect.sync"
  | .suspend => "Effect.suspend"
  | .flatMap => "Effect.flatMap"
  | .gen => "Effect.gen"
  | .catchCause => "Effect.catchCause"
  | .matchCauseEffect => "Effect.matchCauseEffect"
  | .onExit => "Effect.onExit"
  | .exit => "Effect.exit"
  | .uninterruptible => "Effect.uninterruptible"
  | .interruptible => "Effect.interruptible"
  | .whileLoop => "Effect.whileLoop"
  | .yieldNowWith => "Effect.yieldNowWith"
  | .join => "Fiber.join"
  | .await => "Fiber.await"
  | .forkChild => "Effect.forkChild"
  | .forkDetach => "Effect.forkDetach"
  | .forkIn => "Effect.forkIn"
  | .forkScoped => "Effect.forkScoped"
  | .runIn => "Fiber.runIn"
  | .interrupt => "Fiber.interrupt"
  | .interruptAll => "Fiber.interruptAll"
  | .interruptAllAs => "Fiber.interruptAllAs"
  | .awaitAll => "Fiber.awaitAll"
  | .raceAll => "Effect.raceAll"
  | .context => "Effect.context"
  | .fiberId => "Effect.fiberId"
  | .scopeClose => "Scope.close"
  | .scoped => "Effect.scoped"
  | .acquireRelease => "Effect.acquireRelease"
  | .causeFail => "Cause.fail"
  | .causeDie => "Cause.die"
  | .causeInterrupt => "Cause.interrupt"
  | .causeCombine => "Cause.combine"
  | .undefined => "undefined"

/-- Every head, once. -/
def heads : List Head :=
  [ .succeed, .fail, .failCause, .sync, .suspend, .flatMap, .gen, .catchCause
  , .matchCauseEffect, .onExit, .exit, .uninterruptible, .interruptible, .whileLoop
  , .yieldNowWith, .join, .await, .forkChild, .forkDetach, .forkIn, .forkScoped, .runIn
  , .interrupt, .interruptAll, .interruptAllAs, .awaitAll, .raceAll, .context, .fiberId
  , .scopeClose, .scoped, .acquireRelease, .causeFail, .causeDie, .causeInterrupt
  , .causeCombine, .undefined ]

/-- Every spelling the printer reserves: a row's spelling and a term's atom must avoid
these. -/
def reserved : List String := heads.map Head.spelling

/-- The head a spelling names, if any. -/
def headOf (s : String) : Option Head := heads.find? fun h => decide (h.spelling = s)

theorem heads_complete (h : Head) : h ∈ heads := by cases h <;> decide

theorem headOf_spelling (h : Head) : headOf h.spelling = some h := by cases h <;> decide

theorem headOf_exact {s : String} {h : Head} (hh : headOf s = some h) : s = h.spelling := by
  have := List.find?_some hh
  simp at this
  exact this.symm

theorem headOf_none {s : String} (hs : s ∉ reserved) : headOf s = none := by
  unfold headOf
  rw [List.find?_eq_none]
  intro h _ hp
  simp at hp
  exact hs (hp ▸ List.mem_map.mpr ⟨h, heads_complete h, rfl⟩)

theorem mem_reserved_of_headOf {s : String} {h : Head} (hh : headOf s = some h) :
    s ∈ reserved :=
  headOf_exact hh ▸ List.mem_map.mpr ⟨h, heads_complete h, rfl⟩

/-! ## Terms -/

mutual
  /-- A pure term back from its printing: a binder as its variable, `undefined` as the unit
  literal, a non-negative integer, a Boolean, a string, and `atom(args)` as the application.
  Atoms are not checked against `reserved` in term position; the printer never puts a
  combinator there. -/
  def readTerm (n : Nat) (x : Expr) : Except ReadRefusal Term :=
    match x with
    | .ident s =>
      match Var.read n s with
      | some i => .ok (.var i)
      | none => if s = "undefined" then .ok (.lit .unit) else .error (.unknownIdent s)
    | .int k => if 0 ≤ k then .ok (.lit (.nat k.toNat)) else .error (.negative k)
    | .bool b => .ok (.lit (.bool b))
    | .str s => .ok (.lit (.str s))
    | .call (.ident atom) args => (readTerms n args).map (.app atom)
    | _ => .error (.shape "term")
  termination_by structural x

  /-- An argument list, in order. -/
  def readTerms (n : Nat) (xs : List Expr) : Except ReadRefusal Terms :=
    match xs with
    | [] => .ok .nil
    | x :: rest => do
      let t ← readTerm n x
      let ts ← readTerms n rest
      .ok (.cons t ts)
  termination_by structural xs
end

/-- A cause back from the public `Cause` constructors the printer spells. -/
def readCause (n : Nat) (x : Expr) : Except ReadRefusal CauseTerm :=
  match x with
  | .call (.ident s) args =>
    match headOf s, args with
    | some .causeFail, [e] => (readTerm n e).map .fail
    | some .causeDie, [d] => (readTerm n d).map .die
    | some .causeInterrupt, [] => .ok (.interrupt none)
    | some .causeInterrupt, [who] => (readTerm n who).map fun w => .interrupt (some w)
    | some .causeCombine, [l, r] => do
      let a ← readCause n l
      let b ← readCause n r
      .ok (.both a b)
    | _, _ => .error (.shape "cause")
  | _ => .error (.shape "cause")
termination_by structural x

/-- The fork options object back into `ForkOptions`. The object carries no `daemon`
field: `Effect.forkChild` against `Effect.forkDetach` decides it for a plain fork, and the
scoped forks (`forkIn`, `forkScoped`) read it as `false`. -/
def readForkOptions (daemon : Bool) (x : Expr) :
    Except ReadRefusal Effect4.Supervision.ForkOptions :=
  match x with
  | .object [(f1, .bool start), (f2, u)] =>
    if f1 = "startImmediately" ∧ f2 = "uninterruptible" then
      match u with
      | .bool true => .ok ⟨start, daemon, .uninterruptible⟩
      | .bool false => .ok ⟨start, daemon, .interruptible⟩
      | .str s => if s = "inherit" then .ok ⟨start, daemon, .inherit⟩ else .error (.shape "forkOptions")
      | _ => .error (.shape "forkOptions")
    else .error (.shape "forkOptions")
  | _ => .error (.shape "forkOptions")

/-! ## Rows

The reader takes `spell : String → List String → Option Op`, the inverse of a row's
(spelling, trailing names): the trailing names are part of a row's identity in the image
(`Ref.update(ref, incr)` and `Ref.update(ref, double)` are two rows of one spelling). A call
row's argument list is the trailing names alone on a `unit` request, and the request
followed by the trailing names otherwise; the reader tries both readings, and
`LawfulSpelling` is what makes at most one succeed. -/

variable {Op : Type}

/-- The names of an argument list made of identifiers only. -/
def idents? : List Expr → Option (List String)
  | [] => some []
  | .ident s :: rest => (idents? rest).map (s :: ·)
  | _ :: _ => none

/-- The reading of a row: a `callback` on an `.async` row, a `perform` otherwise. -/
def rowAnswer (row : Row) (op : Op) (request : Term) : Eff Op :=
  if row.kind = .async then .callback op request else .perform op request

/-- A bare identifier as a value row. -/
def readRowValue (sig : Signature Op) (spell : String → List String → Option Op)
    (s : String) : Except ReadRefusal (Eff Op) :=
  match spell s [] with
  | some op =>
    if (sig.rowOf op).shape = .value then .ok (rowAnswer (sig.rowOf op) op (.lit .unit))
    else .error (.arity s)
  | none => .error (.unknownIdent s)

/-- A call as a call row; `none` when no row of the table has this head and argument
shape, so the caller may read an atom application instead. -/
def readRowCall (sig : Signature Op) (spell : String → List String → Option Op) (n : Nat)
    (s : String) (args : List Expr) : Option (Except ReadRefusal (Eff Op)) :=
  match (idents? args).bind (spell s) with
  | some op =>
    some (if (sig.rowOf op).shape = .call ∧ (sig.rowOf op).request = Ty.unit then
      .ok (rowAnswer (sig.rowOf op) op (.lit .unit))
    else .error (.arity s))
  | none =>
    match args with
    | request :: rest =>
      match (idents? rest).bind (spell s) with
      | some op =>
        some (if (sig.rowOf op).shape = .call ∧ (sig.rowOf op).request ≠ Ty.unit then
          (readTerm n request).map (rowAnswer (sig.rowOf op) op)
        else .error (.arity s))
      | none => none
    | [] => none

/-! ## Effects -/

mutual
  /-- `readEff sig spell n x` is `x` as a program at environment length `n`, in the order
  of the printer's table: a bare identifier is a binder, then `Effect.fiberId` or
  `undefined`, then a value row; a call is a reserved combinator, then a call row, then an
  atom application; a literal is a yielded error. -/
  def readEff (sig : Signature Op) (spell : String → List String → Option Op) (n : Nat)
      (x : Expr) : Except ReadRefusal (Eff Op) :=
    match x with
    | .ident s =>
      match Var.read n s with
      | some i => .ok (.yieldError (.var i))
      | none =>
        match headOf s with
        | some .fiberId => .ok (.withFiber .getId)
        | some .undefined => .ok (.yieldError (.lit .unit))
        | some _ => .error (.unknownHead s)
        | none => readRowValue sig spell s
    | .int k => if 0 ≤ k then .ok (.yieldError (.lit (.nat k.toNat))) else .error (.negative k)
    | .bool b => .ok (.yieldError (.lit (.bool b)))
    | .str s => .ok (.yieldError (.lit (.str s)))
    | .call (.ident s) args =>
      match headOf s with
      | some h => readHead sig spell n h args
      | none =>
        match readRowCall sig spell n s args with
        | some answer => answer
        | none => (readTerms n args).map fun ts => .yieldError (.app s ts)
    | _ => .error (.shape "expression")
  termination_by structural x

  /-- A reserved head applied to its arguments, one arm per row of the printer's table. -/
  def readHead (sig : Signature Op) (spell : String → List String → Option Op) (n : Nat)
      (h : Head) (args : List Expr) : Except ReadRefusal (Eff Op) :=
    match h, args with
    | .succeed, [v] => (readTerm n v).map .succeed
    | .fail, [e] => (readTerm n e).map .fail
    | .failCause, [c] => (readCause n c).map .failCause
    | .sync, [.arrow none t] => (readTerm n t).map .sync
    | .suspend, [.arrow none (.cond t a b)] => do
      let test ← readTerm n t
      let thenB ← readEff sig spell n a
      let elseB ← readEff sig spell n b
      .ok (.branch test thenB elseB)
    | .suspend, [.arrow none body] => (readEff sig spell n body).map .suspend
    | .suspend, [.arrowBlock [] [.letInit cursor initial,
        .ret (.call (.ident loop) [.object [(fw, .arrow none test), (fb, .arrow none body),
          (fs, .arrowBlock [answer] [.assign cursor' step])]])]] =>
      if loop = "Effect.whileLoop" ∧ fw = "while" ∧ fb = "body" ∧ fs = "step"
          ∧ cursor = Var.name n ∧ cursor' = Var.name n ∧ answer = Var.name (n + 1) then do
        let i ← readTerm n initial
        let t ← readTerm (n + 1) test
        let s ← readTerm (n + 2) step
        let b ← readEff sig spell (n + 1) body
        .ok (.whileLoop i t s b)
      else .error (.shape "whileLoop")
    | .flatMap, [first, .lambda [x] rest] =>
      if x = Var.name n then do
        let f ← readEff sig spell n first
        let r ← readEff sig spell (n + 1) rest
        .ok (.bind f r)
      else .error (.binder (Var.name n))
    | .gen, [.generator body] => (readStmts sig spell n body).map .gen
    | .catchCause, [body, .lambda [x] handler] =>
      if x = Var.name n then do
        let b ← readEff sig spell n body
        let h ← readEff sig spell (n + 1) handler
        .ok (.catchCause b h)
      else .error (.binder (Var.name n))
    | .matchCauseEffect, [body, .object [(ff, .lambda [x] onCause), (fs, .lambda [y] onValue)]] =>
      if ff = "onFailure" ∧ fs = "onSuccess" ∧ x = Var.name n ∧ y = Var.name n then do
        let b ← readEff sig spell n body
        let v ← readEff sig spell (n + 1) onValue
        let c ← readEff sig spell (n + 1) onCause
        .ok (.matchCause b v c)
      else .error (.shape "matchCause")
    | .onExit, [body, .lambda [x] finalizer] =>
      if x = Var.name n then do
        let b ← readEff sig spell n body
        let f ← readEff sig spell (n + 1) finalizer
        .ok (.onExit b f)
      else .error (.binder (Var.name n))
    | .exit, [body] => (readEff sig spell n body).map .exit
    | .uninterruptible, [body] => (readEff sig spell n body).map .uninterruptible
    | .interruptible, [body] => (readEff sig spell n body).map .interruptible
    | .yieldNowWith, [.int k] =>
      if 0 ≤ k then .ok (.yieldNow k.toNat) else .error (.negative k)
    | .join, [fiber] => (readTerm n fiber).map (.awaitFiber · .joinEffect)
    | .await, [fiber] => (readTerm n fiber).map (.awaitFiber · .awaitValue)
    | .forkChild, [program, options] => do
      let p ← readEff sig spell n program
      let o ← readForkOptions false options
      .ok (.withFiber (.fork p o))
    | .forkDetach, [program, options] => do
      let p ← readEff sig spell n program
      let o ← readForkOptions true options
      .ok (.withFiber (.fork p o))
    | .forkIn, [program, scope, options] => do
      let p ← readEff sig spell n program
      let s ← readTerm n scope
      let o ← readForkOptions false options
      .ok (.withFiber (.forkIn p o s))
    | .forkScoped, [program, options] => do
      let p ← readEff sig spell n program
      let o ← readForkOptions false options
      .ok (.withFiber (.forkScoped p o))
    | .runIn, [target, scope] => do
      let t ← readTerm n target
      let s ← readTerm n scope
      .ok (.withFiber (.runIn t s))
    | .interrupt, [target] => (readTerm n target).map fun t => .withFiber (.interrupt t)
    | .interruptAll, [targets] =>
      (readTerm n targets).map fun t => .withFiber (.interruptAll t none)
    | .interruptAllAs, [targets, who] => do
      let t ← readTerm n targets
      let w ← readTerm n who
      .ok (.withFiber (.interruptAll t (some w)))
    | .awaitAll, [targets] => (readTerm n targets).map fun t => .withFiber (.awaitAll t)
    | .raceAll, [.arr entrants] =>
      (readEffs sig spell n entrants).map fun es => .withFiber (.raceAll es)
    | .context, [] => .ok (.withFiber .getContext)
    | .scopeClose, [scope, exit] => do
      let s ← readTerm n scope
      let e ← readTerm n exit
      .ok (.withFiber (.closeScope s e))
    | .scoped, [body] => (readEff sig spell n body).map .scoped
    | .acquireRelease, [acquire, .lambda [x, y] release] =>
      if x = Var.name n ∧ y = Var.name (n + 1) then do
        let a ← readEff sig spell n acquire
        let r ← readEff sig spell (n + 2) release
        .ok (.acquireRelease a r)
      else .error (.binder (Var.name n))
    | .whileLoop, _ => .error (.unknownHead Head.whileLoop.spelling)
    | .fiberId, _ => .error (.unknownHead Head.fiberId.spelling)
    | .causeFail, _ => .error (.unknownHead Head.causeFail.spelling)
    | .causeDie, _ => .error (.unknownHead Head.causeDie.spelling)
    | .causeInterrupt, _ => .error (.unknownHead Head.causeInterrupt.spelling)
    | .causeCombine, _ => .error (.unknownHead Head.causeCombine.spelling)
    | .undefined, _ => .error (.unknownHead Head.undefined.spelling)
    | h, _ => .error (.arity h.spelling)
  termination_by structural args

  /-- A generator body, statement by statement, with the binder counts of `printStmts`. -/
  def readStmts (sig : Signature Op) (spell : String → List String → Option Op) (n : Nat)
      (stmts : List TypeScript.Stmt) : Except ReadRefusal (Stmts Op) :=
    match stmts with
    | [] => .ok .nil
    | .constYield x value :: rest =>
      if x = Var.name n then do
        let e ← readEff sig spell n value
        let tail ← readStmts sig spell (n + 1) rest
        .ok (.cons (.bindYield e) tail)
      else .error (.binder (Var.name n))
    | .yieldDiscard value :: rest => do
      let e ← readEff sig spell n value
      let tail ← readStmts sig spell n rest
      .ok (.cons (.yieldDiscard e) tail)
    | .ret value :: rest => do
      let v ← readTerm n value
      let tail ← readStmts sig spell n rest
      .ok (.cons (.ret v) tail)
    | .ifElse test thenB elseB :: rest => do
      let t ← readTerm n test
      let a ← readStmts sig spell n thenB
      let b ← readStmts sig spell n elseB
      let tail ← readStmts sig spell n rest
      .ok (.cons (.ifElse t a b) tail)
    | .whileTrue none body :: rest => do
      let b ← readStmts sig spell n body
      let tail ← readStmts sig spell n rest
      .ok (.cons (.whileTrue b) tail)
    | .breakTo none :: rest => do
      let tail ← readStmts sig spell n rest
      .ok (.cons .breakLoop tail)
    | _ :: _ => .error .unsupportedStmt
  termination_by structural stmts

  /-- The race entrants, each at the same environment length. -/
  def readEffs (sig : Signature Op) (spell : String → List String → Option Op) (n : Nat)
      (items : List Expr) : Except ReadRefusal (Effs Op) :=
    match items with
    | [] => .ok .nil
    | x :: rest => do
      let e ← readEff sig spell n x
      let es ← readEffs sig spell n rest
      .ok (.cons e es)
  termination_by structural items
end

/-- The reader after the printer: the executed shadow of `read_print`. The printer's refusal
alphabet is not the reader's, so a printer refusal is reported as the `shape` named `printer`. -/
def roundTrip (sig : Signature Op) (spell : String → List String → Option Op) (n : Nat)
    (e : Eff Op) : Except ReadRefusal (Eff Op) :=
  match print sig n e with
  | .ok x => readEff sig spell n x
  | .error _ => .error (.shape "printer")

/-! ## What the printer loses -/

mutual
  /-- Every variable of the term is in scope at `n`. -/
  def Term.scoped (n : Nat) : Term → Bool
    | .var index => decide (index < n)
    | .lit _ => true
    | .app _ args => Terms.scoped n args
  def Terms.scoped (n : Nat) : Terms → Bool
    | .nil => true
    | .cons head tail => Term.scoped n head && Terms.scoped n tail
end

def CauseTerm.scoped (n : Nat) : CauseTerm → Bool
  | .fail error => error.scoped n
  | .die defect => defect.scoped n
  | .interrupt none => true
  | .interrupt (some who) => who.scoped n
  | .both left right => left.scoped n && right.scoped n

/-- The identifiers an argument list prints as, when every argument prints as one: a
variable as its binder, the unit literal as `undefined`. -/
def Terms.names? : Terms → Option (List String)
  | .nil => some []
  | .cons (.var index) rest => (names? rest).map (Var.name index :: ·)
  | .cons (.lit .unit) rest => (names? rest).map ("undefined" :: ·)
  | .cons _ _ => none

/-- No row of the table reads the head `atom` on these arguments, in either of the two
readings `readRowCall` tries. -/
def noRow (spell : String → List String → Option Op) (atom : String) (args : Terms) : Bool :=
  ((args.names?).bind (spell atom)).isNone &&
    match args with
    | .cons _ rest => ((rest.names?).bind (spell atom)).isNone
    | .nil => true

/-- What the printer keeps of a row's request: nothing on a value row or a `unit` request
(the request must then be exactly the unit literal), the term otherwise. -/
def requestReadable (row : Row) (n : Nat) (request : Term) : Bool :=
  match row.shape with
  | .value => decide (request = .lit .unit)
  | .call =>
    if row.request = Ty.unit then decide (request = .lit .unit) else request.scoped n

mutual
  /-- The program is one the printer keeps whole: variables in scope, rows performed on the
  kind their row declares, requests the row prints, atoms that are no head and no row, no
  `choose`, no internal fiber action, and no `daemon` on a scoped fork. -/
  def readable (sig : Signature Op) (spell : String → List String → Option Op) (n : Nat) :
      Eff Op → Bool
    | .succeed value => value.scoped n
    | .fail error => error.scoped n
    | .failCause cause => cause.scoped n
    | .yieldError (.var index) => decide (index < n)
    | .yieldError (.lit _) => true
    | .yieldError (.app atom args) =>
      (headOf atom).isNone && noRow spell atom args && Terms.scoped n args
    | .sync thunk => thunk.scoped n
    | .suspend body => readable sig spell n body
    | .perform op request =>
      decide ((sig.rowOf op).kind ≠ .async) && requestReadable (sig.rowOf op) n request
    | .bind first rest => readable sig spell n first && readable sig spell (n + 1) rest
    | .gen body => readableStmts sig spell n body
    | .catchCause body handler =>
      readable sig spell n body && readable sig spell (n + 1) handler
    | .matchCause body onValue onCause =>
      readable sig spell n body && readable sig spell (n + 1) onValue
        && readable sig spell (n + 1) onCause
    | .onExit body finalizer => readable sig spell n body && readable sig spell (n + 1) finalizer
    | .exit body => readable sig spell n body
    | .uninterruptible body => readable sig spell n body
    | .interruptible body => readable sig spell n body
    | .branch test thenB elseB =>
      test.scoped n && readable sig spell n thenB && readable sig spell n elseB
    | .whileLoop initial test step body =>
      initial.scoped n && test.scoped (n + 1) && step.scoped (n + 2)
        && readable sig spell (n + 1) body
    | .yieldNow _ => true
    | .callback register request =>
      decide ((sig.rowOf register).kind = .async) && requestReadable (sig.rowOf register) n request
    | .awaitFiber fiber _ => fiber.scoped n
    | .withFiber action => readableAction sig spell n action
    | .scoped body => readable sig spell n body
    | .acquireRelease acquire release =>
      readable sig spell n acquire && readable sig spell (n + 2) release
    | .choose _ _ _ => false

  def readableStmts (sig : Signature Op) (spell : String → List String → Option Op)
      (n : Nat) : Stmts Op → Bool
    | .nil => true
    | .cons (.bindYield effect) rest =>
      readable sig spell n effect && readableStmts sig spell (n + 1) rest
    | .cons (.yieldDiscard effect) rest =>
      readable sig spell n effect && readableStmts sig spell n rest
    | .cons (.ret value) rest => value.scoped n && readableStmts sig spell n rest
    | .cons (.ifElse test thenB elseB) rest =>
      test.scoped n && readableStmts sig spell n thenB && readableStmts sig spell n elseB
        && readableStmts sig spell n rest
    | .cons (.whileTrue body) rest =>
      readableStmts sig spell n body && readableStmts sig spell n rest
    | .cons .breakLoop rest => readableStmts sig spell n rest

  def readableEffs (sig : Signature Op) (spell : String → List String → Option Op)
      (n : Nat) : Effs Op → Bool
    | .nil => true
    | .cons head tail => readable sig spell n head && readableEffs sig spell n tail

  def readableAction (sig : Signature Op) (spell : String → List String → Option Op)
      (n : Nat) : ActionTerm Op → Bool
    | .fork program _ => readable sig spell n program
    | .forkIn program options scope =>
      readable sig spell n program && !options.daemon && scope.scoped n
    | .forkScoped program options => readable sig spell n program && !options.daemon
    | .runIn target scope => target.scoped n && scope.scoped n
    | .interrupt target => target.scoped n
    | .interruptScoped _ => false
    | .interruptAll targets none => targets.scoped n
    | .interruptAll targets (some who) => targets.scoped n && who.scoped n
    | .awaitAll targets => targets.scoped n
    | .awaitAllFailFast _ => false
    | .snapshotChildren => false
    | .awaitNewChildren _ => false
    | .raceAll entrants => readableEffs sig spell n entrants
    | .setContext _ => false
    | .getContext => true
    | .getId => true
    | .closeScope scope exit => scope.scoped n && exit.scoped n
end

/-! ## What the reader needs of a signature -/

/-- `spell` inverts the row table on (spelling, trailing names), a value row has no trailing
names (the printer drops them), and no spelling or trailing name is a binder name,
`undefined`, or a reserved head. -/
structure LawfulSpelling (sig : Signature Op) (spell : String → List String → Option Op) :
    Prop where
  spell_row : ∀ op, spell (sig.rowOf op).spelling (sig.rowOf op).trailing = some op
  row_of_spell : ∀ s names op, spell s names = some op →
    (sig.rowOf op).spelling = s ∧ (sig.rowOf op).trailing = names
  value_trailing : ∀ op, (sig.rowOf op).shape = .value → (sig.rowOf op).trailing = []
  spelling_ne_name : ∀ op i, (sig.rowOf op).spelling ≠ Var.name i
  spelling_not_reserved : ∀ op, (sig.rowOf op).spelling ∉ reserved
  trailing_ne_name : ∀ op i, Var.name i ∉ (sig.rowOf op).trailing
  trailing_ne_undefined : ∀ op, "undefined" ∉ (sig.rowOf op).trailing

/-! ## Receipts: what the reader needs of `Except` -/

@[simp] theorem ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

@[simp] theorem map_ok {ε α β : Type} (f : α → β) (a : α) :
    (Except.ok a : Except ε α).map f = .ok (f a) := rfl

theorem bind_eq_ok {ε α β : Type} {m : Except ε α} {f : α → Except ε β} {b : β} :
    (m >>= f) = .ok b ↔ ∃ a, m = .ok a ∧ f a = .ok b := by
  cases m <;> simp [Bind.bind, Except.bind]

theorem map_eq_ok {ε α β : Type} {m : Except ε α} {f : α → β} {b : β} :
    m.map f = .ok b ↔ ∃ a, m = .ok a ∧ f a = b := by
  cases m <;> simp [Except.map]

/-! ## Binders are injective

`Var.name i = "a" ++ Nat.repr i`, and `Nat.repr` is `String.ofList` of the decimal digits.
The string layer's injectivity lemmas reach `Classical.choice` on this toolchain (they go
through `String.toList`), so injectivity is taken from the bytes instead: the UTF-8 bytes of
a decimal string are its digits, and `decodeBytes` reads the number back. -/

/-- The digit a byte spells, `'0'` as `0`. -/
def digitOfByte (b : UInt8) : Nat := b.toNat - 48

/-- The number a byte string spells in decimal. -/
def decodeBytes (bs : List UInt8) : Nat := bs.foldl (fun acc b => acc * 10 + digitOfByte b) 0

theorem decodeBytes_append (bs : List UInt8) (b : UInt8) :
    decodeBytes (bs ++ [b]) = decodeBytes bs * 10 + digitOfByte b := by
  simp [decodeBytes, List.foldl_append]

theorem utf8_digitChar : ∀ m, m < 10 →
    String.utf8EncodeChar (Nat.digitChar m) = [UInt8.ofNat (48 + m)] := by decide

theorem digitOfByte_digit : ∀ m, m < 10 → digitOfByte (UInt8.ofNat (48 + m)) = m := by decide

theorem toDigitsCore_append (fuel : Nat) : ∀ (n : Nat) (ds : List Char), n < fuel →
    Nat.toDigitsCore 10 fuel n ds = Nat.toDigitsCore 10 fuel n [] ++ ds := by
  induction fuel with
  | zero => intro n ds h; omega
  | succ fuel ih =>
    intro n ds hn
    simp only [Nat.toDigitsCore]
    by_cases h0 : n / 10 = 0
    · simp [h0]
    · simp only [h0, if_false]
      rw [ih (n / 10) (Nat.digitChar (n % 10) :: ds) (by omega),
        ih (n / 10) [Nat.digitChar (n % 10)] (by omega), List.append_assoc]
      rfl

theorem decodeBytes_toDigitsCore (fuel : Nat) : ∀ n, n < fuel →
    decodeBytes ((Nat.toDigitsCore 10 fuel n []).flatMap String.utf8EncodeChar) = n := by
  induction fuel with
  | zero => intro n h; omega
  | succ fuel ih =>
    intro n hn
    have hm : n % 10 < 10 := Nat.mod_lt _ (by decide)
    simp only [Nat.toDigitsCore]
    by_cases h0 : n / 10 = 0
    · simp only [h0, if_true, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        utf8_digitChar _ hm]
      simp only [decodeBytes, List.foldl_cons, List.foldl_nil, Nat.zero_mul, Nat.zero_add,
        digitOfByte_digit _ hm]
      omega
    · simp only [h0, if_false]
      rw [toDigitsCore_append fuel (n / 10) [Nat.digitChar (n % 10)] (by omega),
        List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        utf8_digitChar _ hm, decodeBytes_append, ih (n / 10) (by omega), digitOfByte_digit _ hm]
      omega

theorem decodeBytes_repr (n : Nat) : decodeBytes (Nat.repr n).toByteArray.data.toList = n := by
  rw [Nat.repr, String.toByteArray_ofList, List.utf8Encode, List.toList_data_toByteArray,
    Nat.toDigits]
  exact decodeBytes_toDigitsCore (n + 1) n (Nat.lt_succ_self n)

theorem repr_inj {a b : Nat} (h : Nat.repr a = Nat.repr b) : a = b := by
  have := congrArg (fun s => decodeBytes s.toByteArray.data.toList) h
  simpa [decodeBytes_repr] using this

theorem Var.name_inj {i j : Nat} (h : Var.name i = Var.name j) : i = j :=
  repr_inj (String.append_right_inj _ |>.mp h)

theorem Var.name_head (i : Nat) : (Var.name i).toByteArray.data.toList.head? = some 97 := by
  have ha : "a".toByteArray.data.toList = [97] := by decide
  rw [Var.name, String.toByteArray_append, ByteArray.data_append, Array.toList_append, ha]
  rfl

/-- A string whose first byte is not `'a'` is no binder name. -/
theorem Var.name_ne {s : String} (hs : s.toByteArray.data.toList.head? ≠ some 97) (i : Nat) :
    Var.name i ≠ s := fun h => hs (h ▸ Var.name_head i)

theorem Var.name_ne_undefined (i : Nat) : Var.name i ≠ "undefined" := Var.name_ne (by decide) i

theorem Var.name_ne_fiberId (i : Nat) : Var.name i ≠ "Effect.fiberId" :=
  Var.name_ne (by decide) i

theorem Var.read_exact : ∀ {n : Nat} {s : String} {i : Nat},
    Var.read n s = some i → s = Var.name i ∧ i < n
  | 0, _, _, h => by simp [Var.read] at h
  | n + 1, s, i, h => by
    simp only [Var.read] at h
    split at h
    · rename_i heq; cases h; exact ⟨heq.symm, Nat.lt_succ_self _⟩
    · obtain ⟨hs, hi⟩ := Var.read_exact h; exact ⟨hs, Nat.lt_succ_of_lt hi⟩

theorem Var.read_name : ∀ {n i : Nat}, i < n → Var.read n (Var.name i) = some i
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, i, h => by
    simp only [Var.read]
    split
    · rename_i heq; rw [Var.name_inj heq]
    · rename_i hne
      have : i ≠ n := fun e => hne (by rw [e])
      exact Var.read_name (by omega)

theorem Var.read_none : ∀ {n : Nat} {s : String}, (∀ i, Var.name i ≠ s) → Var.read n s = none
  | 0, _, _ => rfl
  | n + 1, s, h => by simp only [Var.read]; rw [if_neg (h n)]; exact Var.read_none h

/-! ## Terms round-trip -/

mutual
  theorem readTerm_printTerm {n : Nat} (t : Term) (h : Term.scoped n t = true) :
      readTerm n (printTerm t) = .ok t :=
    match t, h with
    | .var i, h => by
      simp only [Term.scoped, decide_eq_true_eq] at h
      simp [printTerm, readTerm, Var.read_name h]
    | .lit .unit, _ => by
      simp [printTerm, printLit, readTerm, Var.read_none Var.name_ne_undefined]
    | .lit (.nat k), _ => by simp [printTerm, printLit, readTerm]
    | .lit (.bool b), _ => by simp [printTerm, printLit, readTerm]
    | .lit (.str s), _ => by simp [printTerm, printLit, readTerm]
    | .app atom args, h => by
      simp only [Term.scoped] at h
      simp [printTerm, readTerm, readTerms_printTerms args h]
  termination_by structural t

  theorem readTerms_printTerms {n : Nat} (ts : Terms) (h : Terms.scoped n ts = true) :
      readTerms n (printTerms ts) = .ok ts :=
    match ts, h with
    | .nil, _ => by simp [printTerms, readTerms]
    | .cons t ts, h => by
      simp only [Terms.scoped, Bool.and_eq_true] at h
      simp [printTerms, readTerms, readTerm_printTerm t h.1, readTerms_printTerms ts h.2]
  termination_by structural ts
end

mutual
  theorem readTerm_exact {n : Nat} (x : Expr) {t : Term} (h : readTerm n x = .ok t) :
      printTerm t = x :=
    match x, h with
    | .ident s, h => by
      simp only [readTerm] at h
      split at h
      · rename_i i hi; cases h; obtain ⟨hs, _⟩ := Var.read_exact hi; simp [printTerm, hs]
      · split at h
        · cases h; rename_i hs; simp [printTerm, printLit, hs]
        · cases h
    | .int k, h => by
      simp only [readTerm] at h
      split at h
      · cases h; rename_i hk; simp [printTerm, printLit, Int.toNat_of_nonneg hk]
      · cases h
    | .bool b, h => by simp [readTerm] at h; subst h; rfl
    | .str s, h => by simp [readTerm] at h; subst h; rfl
    | .call (.ident atom) args, h => by
      simp only [readTerm, map_eq_ok] at h
      obtain ⟨ts, hts, rfl⟩ := h
      simp [printTerm, readTerms_exact args hts]
    | .call (.str _) _, h | .call (.int _) _, h | .call (.float64Bits _) _, h
    | .call (.bool _) _, h | .call .jsNull _, h | .call (.call _ _) _, h
    | .call (.object _) _, h | .call (.objectML _) _, h | .call (.objectQuoted _) _, h
    | .call (.objectQuotedML _) _, h | .call (.objectFromEntries _) _, h | .call (.arr _) _, h
    | .call (.arrow _ _) _, h | .call (.generic _ _) _, h | .call (.lambda _ _) _, h
    | .call (.method _ _ _) _, h | .call (.member _ _) _, h | .call (.generator _) _, h
    | .call (.cond _ _ _) _, h | .call (.arrowBlock _ _) _, h => by simp [readTerm] at h
    | .float64Bits _, h | .jsNull, h | .object _, h | .objectML _, h | .objectQuoted _, h
    | .objectQuotedML _, h | .objectFromEntries _, h | .arr _, h | .arrow _ _, h
    | .generic _ _, h | .lambda _ _, h | .method _ _ _, h | .member _ _, h | .generator _, h
    | .cond _ _ _, h | .arrowBlock _ _, h => by simp [readTerm] at h
  termination_by structural x

  theorem readTerms_exact {n : Nat} (xs : List Expr) {ts : Terms} (h : readTerms n xs = .ok ts) :
      printTerms ts = xs :=
    match xs, h with
    | [], h => by simp [readTerms] at h; subst h; rfl
    | x :: rest, h => by
      simp only [readTerms, bind_eq_ok] at h
      obtain ⟨t, ht, ts', hts', hts⟩ := h
      cases hts
      simp [printTerms, readTerm_exact x ht, readTerms_exact rest hts']
  termination_by structural xs
end

/-! ## Causes, fork options, rows: the small round trips -/

theorem headOf_lit (h : Head) (s : String) (hs : h.spelling = s) : headOf s = some h :=
  hs ▸ headOf_spelling h

theorem readCause_printCause {n : Nat} (c : CauseTerm) (h : CauseTerm.scoped n c = true) :
    readCause n (printCause c) = .ok c := by
  induction c with
  | fail e =>
    simp only [CauseTerm.scoped] at h
    rw [printCause]; unfold readCause; simp [headOf_lit .causeFail "Cause.fail" rfl, readTerm_printTerm e h]
  | die d =>
    simp only [CauseTerm.scoped] at h
    rw [printCause]; unfold readCause; simp [headOf_lit .causeDie "Cause.die" rfl, readTerm_printTerm d h]
  | interrupt who =>
    cases who with
    | none => rw [printCause]; unfold readCause; simp [headOf_lit .causeInterrupt "Cause.interrupt" rfl]
    | some w =>
      simp only [CauseTerm.scoped] at h
      rw [printCause]; unfold readCause; simp [headOf_lit .causeInterrupt "Cause.interrupt" rfl, readTerm_printTerm w h]
  | both l r ihl ihr =>
    simp only [CauseTerm.scoped, Bool.and_eq_true] at h
    rw [printCause]; unfold readCause; simp [headOf_lit .causeCombine "Cause.combine" rfl, ihl h.1, ihr h.2]

theorem readCause_exact {n : Nat} (x : Expr) {c : CauseTerm} (h : readCause n x = .ok c) :
    printCause c = x := by
  induction x using readCause.induct generalizing c with
  | case1 s e hh =>
    unfold readCause at h; simp only [hh, map_eq_ok] at h
    obtain ⟨t, ht, rfl⟩ := h
    simp [printCause, Head.spelling, readTerm_exact e ht, headOf_exact hh]
  | case2 s d hh =>
    unfold readCause at h; simp only [hh, map_eq_ok] at h
    obtain ⟨t, ht, rfl⟩ := h
    simp [printCause, Head.spelling, readTerm_exact d ht, headOf_exact hh]
  | case3 s hh => unfold readCause at h; simp only [hh] at h; cases h; simp [printCause, Head.spelling, headOf_exact hh]
  | case4 s w hh =>
    unfold readCause at h; simp only [hh, map_eq_ok] at h
    obtain ⟨t, ht, rfl⟩ := h
    simp [printCause, Head.spelling, readTerm_exact w ht, headOf_exact hh]
  | case5 s l r hh ihl ihr =>
    unfold readCause at h; simp only [hh, bind_eq_ok] at h
    obtain ⟨a, ha, b, hb, hab⟩ := h
    cases hab
    simp [printCause, Head.spelling, ihl ha, ihr hb, headOf_exact hh]
  | case6 s args h1 h2 h3 h4 h5 => unfold readCause at h; split at h <;> simp_all
  | case7 t hne => unfold readCause at h; split at h <;> simp_all

theorem readForkOptions_print (o : Effect4.Supervision.ForkOptions) :
    readForkOptions o.daemon (printForkOptions o) = .ok o := by
  obtain ⟨s, d, m⟩ := o
  cases m <;> simp [printForkOptions, readForkOptions]

theorem readForkOptions_exact {d : Bool} {x : Expr} {o : Effect4.Supervision.ForkOptions}
    (h : readForkOptions d x = .ok o) : printForkOptions o = x ∧ o.daemon = d := by
  unfold readForkOptions at h
  split at h
  · split at h
    · rename_i hf
      split at h
      · cases h; simp [printForkOptions, hf]
      · cases h; simp [printForkOptions, hf]
      · split at h
        · cases h; rename_i hs; simp [printForkOptions, hf, hs]
        · cases h
      · cases h
    · cases h
  · cases h

theorem idents?_map (l : List String) : idents? (l.map Expr.ident) = some l := by
  induction l with
  | nil => rfl
  | cons s rest ih => simp [idents?, ih]

theorem idents?_exact {args : List Expr} {l : List String} (h : idents? args = some l) :
    args = l.map Expr.ident := by
  induction args generalizing l with
  | nil => simp [idents?] at h; subst h; rfl
  | cons x rest ih =>
    cases x <;> (unfold idents? at h; simp at h)
    obtain ⟨l', hl', rfl⟩ := h
    simp [ih hl']

theorem idents?_cons_none {e : Expr} {l : List Expr} (h : ∀ x, e ≠ Expr.ident x) :
    idents? (e :: l) = none := by
  cases e <;> first | exact absurd rfl (h _) | (unfold idents?; simp)

theorem idents?_printTerms : ∀ ts : Terms, idents? (printTerms ts) = ts.names?
  | .nil => rfl
  | .cons t rest => by
    cases t with
    | var i => simp [printTerms, printTerm, idents?, Terms.names?, idents?_printTerms rest]
    | lit v => cases v <;> simp [printTerms, printTerm, printLit, idents?, Terms.names?, idents?_printTerms rest]
    | app a args => simp [printTerms, printTerm, idents?, Terms.names?]

theorem printTerm_ident {t : Term} {x : String} (h : printTerm t = .ident x) :
    (∃ i, t = .var i ∧ x = Var.name i) ∨ (t = .lit .unit ∧ x = "undefined") := by
  cases t with
  | var i => simp [printTerm] at h; exact .inl ⟨i, rfl, h.symm⟩
  | lit v => cases v <;> simp [printTerm, printLit] at h; exact .inr ⟨rfl, h.symm⟩
  | app a args => simp [printTerm] at h

theorem print_not_cond {sig : Signature Op} {n : Nat} {e : Eff Op} {t a b : Expr}
    (hp : print sig n e = .ok (.cond t a b)) : False := by
  cases e
  case yieldError v =>
    cases v with
    | var i => simp [print, printTerm] at hp
    | lit l => cases l <;> simp [print, printTerm, printLit] at hp
    | app atom args => simp [print, printTerm] at hp
  case perform op r =>
    simp only [print, printRow, Except.ok.injEq] at hp
    split at hp
    · simp at hp
    · split at hp <;> simp at hp
  case callback op r =>
    simp only [print, printRow, Except.ok.injEq] at hp
    split at hp
    · simp at hp
    · split at hp <;> simp at hp
  case awaitFiber f m => cases m <;> simp [print] at hp
  case withFiber act =>
    cases act
    case interruptAll targets who => cases who <;> simp [print, printAction] at hp
    all_goals simp [print, printAction, bind_eq_ok] at hp
  all_goals simp [print, bind_eq_ok] at hp

theorem readRowCall_none {sig : Signature Op} {spell : String → List String → Option Op} {n : Nat}
    {atom : String} {args : Terms} (h : noRow spell atom args = true) :
    readRowCall sig spell n atom (printTerms args) = none := by
  cases args with
  | nil =>
    simp only [noRow, Bool.and_true, Option.isNone_iff_eq_none] at h
    unfold readRowCall; rw [idents?_printTerms, h]; simp [printTerms]
  | cons t rest =>
    simp only [noRow, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
    unfold readRowCall
    rw [idents?_printTerms, h.1]
    simp only [printTerms]
    rw [idents?_printTerms, h.2]

theorem readRowCall_unit {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} (op : Op)
    (hshape : (sig.rowOf op).shape = .call) (hreq : (sig.rowOf op).request = Ty.unit) :
    readRowCall sig spell n (sig.rowOf op).spelling ((sig.rowOf op).trailing.map Expr.ident)
      = some (.ok (rowAnswer (sig.rowOf op) op (.lit .unit))) := by
  unfold readRowCall
  rw [idents?_map, Option.bind_some, hl.spell_row]
  simp [hshape, hreq]

theorem readRowCall_request {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} (op : Op) (r : Term)
    (hshape : (sig.rowOf op).shape = .call) (hreq : (sig.rowOf op).request ≠ Ty.unit) :
    readRowCall sig spell n (sig.rowOf op).spelling
        (printTerm r :: (sig.rowOf op).trailing.map Expr.ident)
      = some ((readTerm n (printTerm r)).map (rowAnswer (sig.rowOf op) op)) := by
  have key : ∀ x, (∀ op', x ∉ (sig.rowOf op').trailing) →
      spell (sig.rowOf op).spelling (x :: (sig.rowOf op).trailing) = none := by
    intro x hx
    cases hsp : spell (sig.rowOf op).spelling (x :: (sig.rowOf op).trailing) with
    | none => rfl
    | some op' =>
      exfalso
      obtain ⟨_, htr⟩ := hl.row_of_spell _ _ _ hsp
      exact hx op' (htr ▸ List.mem_cons_self)
  have hA : ((idents? (printTerm r :: (sig.rowOf op).trailing.map Expr.ident)).bind
      (spell (sig.rowOf op).spelling)) = none := by
    cases r with
    | var i =>
      simp [printTerm, idents?, idents?_map, key (Var.name i) (fun op' => hl.trailing_ne_name op' i)]
    | lit v =>
      cases v with
      | unit => simp [printTerm, printLit, idents?, idents?_map, key "undefined" hl.trailing_ne_undefined]
      | nat k => simp [printTerm, printLit, idents?]
      | bool b => simp [printTerm, printLit, idents?]
      | str s => simp [printTerm, printLit, idents?]
    | app a args => simp [printTerm, idents?]
  unfold readRowCall
  rw [hA]
  dsimp only
  rw [idents?_map, Option.bind_some, hl.spell_row]
  simp [hshape, hreq]

/-! ## `read_print`: what the printer prints of a readable program reads back to it -/

theorem readable_row_unit {row : Row} {n : Nat} {r : Term} (hshape : row.shape = .call)
    (hreq : row.request = Ty.unit) (h : requestReadable row n r = true) : r = .lit .unit := by
  simp only [requestReadable, hshape, hreq, if_true, decide_eq_true_eq] at h; exact h

theorem readable_row_value {row : Row} {n : Nat} {r : Term} (hshape : row.shape = .value)
    (h : requestReadable row n r = true) : r = .lit .unit := by
  simp only [requestReadable, hshape, decide_eq_true_eq] at h; exact h

theorem readable_row_request {row : Row} {n : Nat} {r : Term} (hshape : row.shape = .call)
    (hreq : row.request ≠ Ty.unit) (h : requestReadable row n r = true) : r.scoped n = true := by
  simp only [requestReadable, hshape, hreq, if_false] at h; exact h

/-- A row prints and reads back to `rowAnswer`. -/
theorem read_printRow {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} (op : Op) (r : Term)
    (h : requestReadable (sig.rowOf op) n r = true) :
    readEff sig spell n (printRow (sig.rowOf op) r) = .ok (rowAnswer (sig.rowOf op) op r) := by
  have hname : ∀ i, Var.name i ≠ (sig.rowOf op).spelling := fun i => (hl.spelling_ne_name op i).symm
  have hhead : headOf (sig.rowOf op).spelling = none := headOf_none (hl.spelling_not_reserved op)
  cases hshape : (sig.rowOf op).shape with
  | value =>
    rw [readable_row_value hshape h]
    have htr := hl.value_trailing op hshape
    have hsp := hl.spell_row op
    rw [htr] at hsp
    simp only [printRow, hshape]
    unfold readEff
    simp [Var.read_none hname, hhead, readRowValue, hsp, hshape]
  | call =>
    by_cases hreq : (sig.rowOf op).request = Ty.unit
    · rw [readable_row_unit hshape hreq h]
      simp only [printRow, hshape, hreq, if_true]
      unfold readEff
      simp [hhead, readRowCall_unit hl op hshape hreq]
    · simp only [printRow, hshape, hreq, if_false]
      unfold readEff
      simp [hhead, readRowCall_request hl op r hshape hreq,
        readTerm_printTerm r (readable_row_request hshape hreq h)]

mutual
theorem read_print {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} (e : Eff Op) (hr : readable sig spell n e = true)
    {x : Expr} (hp : print sig n e = .ok x) : readEff sig spell n x = .ok e :=
  match e, hr, hp with
  | .succeed v, hr, hp => by
    simp only [readable] at hr
    simp only [print, Except.ok.injEq] at hp; subst hp
    unfold readEff readHead; simp [headOf_lit .succeed "Effect.succeed" rfl, readTerm_printTerm v hr]
  | .fail v, hr, hp => by
    simp only [readable] at hr
    simp only [print, Except.ok.injEq] at hp; subst hp
    unfold readEff readHead; simp [headOf_lit .fail "Effect.fail" rfl, readTerm_printTerm v hr]
  | .failCause c, hr, hp => by
    simp only [readable] at hr
    simp only [print, Except.ok.injEq] at hp; subst hp
    unfold readEff readHead
    simp [headOf_lit .failCause "Effect.failCause" rfl, readCause_printCause c hr]
  | .yieldError t, hr, hp => by
    simp only [print, Except.ok.injEq] at hp; subst hp
    cases t with
    | var i =>
      simp only [readable, decide_eq_true_eq] at hr
      unfold readEff; simp [printTerm, Var.read_name hr]
    | lit v =>
      cases v with
      | unit =>
        unfold readEff
        simp [printTerm, printLit, Var.read_none Var.name_ne_undefined,
          headOf_lit .undefined "undefined" rfl]
      | nat k => unfold readEff; simp [printTerm, printLit]
      | bool b => unfold readEff; simp [printTerm, printLit]
      | str s => unfold readEff; simp [printTerm, printLit]
    | app atom args =>
      simp only [readable, Bool.and_eq_true, Option.isNone_iff_eq_none] at hr
      obtain ⟨⟨hhead, hnorow⟩, hsc⟩ := hr
      unfold readEff
      simp [printTerm, hhead, readRowCall_none hnorow, readTerms_printTerms args hsc]
  | .sync t, hr, hp => by
    simp only [readable] at hr
    simp only [print, Except.ok.injEq] at hp; subst hp
    unfold readEff readHead; simp [headOf_lit .sync "Effect.sync" rfl, readTerm_printTerm t hr]
  | .suspend body, hr, hp => by
    simp only [readable] at hr
    simp only [print, bind_eq_ok] at hp
    obtain ⟨pb, hpb, hx⟩ := hp
    simp only [Except.ok.injEq] at hx; subst hx
    have ih := read_print hl body hr hpb
    unfold readEff; simp only [headOf_lit .suspend "Effect.suspend" rfl]
    cases pb <;> first | exact (print_not_cond hpb).elim | (unfold readHead; simp [ih])
  | .perform op r, hr, hp => by
    simp only [readable, Bool.and_eq_true, decide_eq_true_eq] at hr
    obtain ⟨hkind, hreq⟩ := hr
    simp only [print, Except.ok.injEq] at hp; subst hp
    rw [read_printRow hl op r hreq]
    simp [rowAnswer, hkind]
  | .bind first rest, hr, hp => by
    simp only [readable, Bool.and_eq_true] at hr
    simp only [print, bind_eq_ok] at hp
    obtain ⟨f, hf, r, hr', hx⟩ := hp
    simp only [Except.ok.injEq] at hx; subst hx
    unfold readEff readHead
    simp [headOf_lit .flatMap "Effect.flatMap" rfl, read_print hl first hr.1 hf,
      read_print hl rest hr.2 hr']
  | .gen body, hr, hp => by
    simp only [readable] at hr
    simp only [print, bind_eq_ok] at hp
    obtain ⟨ss, hss, hx⟩ := hp
    simp only [Except.ok.injEq] at hx; subst hx
    unfold readEff readHead
    simp [headOf_lit .gen "Effect.gen" rfl, read_print_stmts hl body hr hss]
  | .catchCause body handler, hr, hp => by
    simp only [readable, Bool.and_eq_true] at hr
    simp only [print, bind_eq_ok] at hp
    obtain ⟨b, hb, h, hh, hx⟩ := hp
    simp only [Except.ok.injEq] at hx; subst hx
    unfold readEff readHead
    simp [headOf_lit .catchCause "Effect.catchCause" rfl, read_print hl body hr.1 hb,
      read_print hl handler hr.2 hh]
  | .matchCause body onValue onCause, hr, hp => by
    simp only [readable, Bool.and_eq_true] at hr
    obtain ⟨⟨h1, h2⟩, h3⟩ := hr
    simp only [print, bind_eq_ok] at hp
    obtain ⟨b, hb, v, hv, c, hc, hx⟩ := hp
    simp only [Except.ok.injEq] at hx; subst hx
    unfold readEff readHead
    simp [headOf_lit .matchCauseEffect "Effect.matchCauseEffect" rfl, read_print hl body h1 hb,
      read_print hl onValue h2 hv, read_print hl onCause h3 hc]
  | .onExit body finalizer, hr, hp => by
    simp only [readable, Bool.and_eq_true] at hr
    simp only [print, bind_eq_ok] at hp
    obtain ⟨b, hb, f, hf, hx⟩ := hp
    simp only [Except.ok.injEq] at hx; subst hx
    unfold readEff readHead
    simp [headOf_lit .onExit "Effect.onExit" rfl, read_print hl body hr.1 hb,
      read_print hl finalizer hr.2 hf]
  | .exit body, hr, hp => by
    simp only [readable] at hr
    simp only [print, bind_eq_ok] at hp
    obtain ⟨b, hb, hx⟩ := hp
    simp only [Except.ok.injEq] at hx; subst hx
    unfold readEff readHead; simp [headOf_lit .exit "Effect.exit" rfl, read_print hl body hr hb]
  | .uninterruptible body, hr, hp => by
    simp only [readable] at hr
    simp only [print, bind_eq_ok] at hp
    obtain ⟨b, hb, hx⟩ := hp
    simp only [Except.ok.injEq] at hx; subst hx
    unfold readEff readHead
    simp [headOf_lit .uninterruptible "Effect.uninterruptible" rfl, read_print hl body hr hb]
  | .interruptible body, hr, hp => by
    simp only [readable] at hr
    simp only [print, bind_eq_ok] at hp
    obtain ⟨b, hb, hx⟩ := hp
    simp only [Except.ok.injEq] at hx; subst hx
    unfold readEff readHead
    simp [headOf_lit .interruptible "Effect.interruptible" rfl, read_print hl body hr hb]
  | .branch test thenB elseB, hr, hp => by
    simp only [readable, Bool.and_eq_true] at hr
    obtain ⟨⟨h1, h2⟩, h3⟩ := hr
    simp only [print, bind_eq_ok] at hp
    obtain ⟨a, ha, b, hb, hx⟩ := hp
    simp only [Except.ok.injEq] at hx; subst hx
    unfold readEff readHead
    simp [headOf_lit .suspend "Effect.suspend" rfl, readTerm_printTerm test h1,
      read_print hl thenB h2 ha, read_print hl elseB h3 hb]
  | .whileLoop initial test step body, hr, hp => by
    simp only [readable, Bool.and_eq_true] at hr
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hr
    simp only [print, bind_eq_ok] at hp
    obtain ⟨b, hb, hx⟩ := hp
    simp only [Except.ok.injEq] at hx; subst hx
    unfold readEff readHead
    simp [headOf_lit .suspend "Effect.suspend" rfl, readTerm_printTerm initial h1,
      readTerm_printTerm test h2, readTerm_printTerm step h3, read_print hl body h4 hb]
  | .yieldNow p, _, hp => by
    simp only [print, Except.ok.injEq] at hp; subst hp
    unfold readEff readHead; simp [headOf_lit .yieldNowWith "Effect.yieldNowWith" rfl]
  | .callback op r, hr, hp => by
    simp only [readable, Bool.and_eq_true, decide_eq_true_eq] at hr
    obtain ⟨hkind, hreq⟩ := hr
    simp only [print, Except.ok.injEq] at hp; subst hp
    rw [read_printRow hl op r hreq]
    simp [rowAnswer, hkind]
  | .awaitFiber f mode, hr, hp => by
    simp only [readable] at hr
    cases mode with
    | joinEffect =>
      simp only [print, Except.ok.injEq] at hp; subst hp
      unfold readEff readHead; simp [headOf_lit .join "Fiber.join" rfl, readTerm_printTerm f hr]
    | awaitValue =>
      simp only [print, Except.ok.injEq] at hp; subst hp
      unfold readEff readHead; simp [headOf_lit .await "Fiber.await" rfl, readTerm_printTerm f hr]
  | .withFiber a, hr, hp => by
    simp only [readable] at hr
    simp only [print] at hp
    exact read_print_action hl a hr hp
  | .scoped body, hr, hp => by
    simp only [readable] at hr
    simp only [print, bind_eq_ok] at hp
    obtain ⟨b, hb, hx⟩ := hp
    simp only [Except.ok.injEq] at hx; subst hx
    unfold readEff readHead; simp [headOf_lit .scoped "Effect.scoped" rfl, read_print hl body hr hb]
  | .acquireRelease acquire release, hr, hp => by
    simp only [readable, Bool.and_eq_true] at hr
    simp only [print, bind_eq_ok] at hp
    obtain ⟨a, ha, r, hr', hx⟩ := hp
    simp only [Except.ok.injEq] at hx; subst hx
    unfold readEff readHead
    simp [headOf_lit .acquireRelease "Effect.acquireRelease" rfl, read_print hl acquire hr.1 ha,
      read_print hl release hr.2 hr']
  | .choose _ _ _, hr, _ => by simp [readable] at hr
termination_by structural e

theorem read_print_stmts {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} (ss : Stmts Op)
    (hr : readableStmts sig spell n ss = true) {xs : List TypeScript.Stmt}
    (hp : printStmts sig n ss = .ok xs) : readStmts sig spell n xs = .ok ss :=
  match ss, hr, hp with
  | .nil, _, hp => by
    simp only [printStmts, Except.ok.injEq] at hp; subst hp; rfl
  | .cons (.bindYield e) rest, hr, hp => by
    simp only [readableStmts, Bool.and_eq_true] at hr
    simp only [printStmts, bind_eq_ok] at hp
    obtain ⟨v, hv, t, ht, hx⟩ := hp
    simp only [Except.ok.injEq] at hx; subst hx
    unfold readStmts; simp [read_print hl e hr.1 hv, read_print_stmts hl rest hr.2 ht]
  | .cons (.yieldDiscard e) rest, hr, hp => by
    simp only [readableStmts, Bool.and_eq_true] at hr
    simp only [printStmts, bind_eq_ok] at hp
    obtain ⟨v, hv, t, ht, hx⟩ := hp
    simp only [Except.ok.injEq] at hx; subst hx
    unfold readStmts; simp [read_print hl e hr.1 hv, read_print_stmts hl rest hr.2 ht]
  | .cons (.ret v) rest, hr, hp => by
    simp only [readableStmts, Bool.and_eq_true] at hr
    simp only [printStmts, bind_eq_ok] at hp
    obtain ⟨t, ht, hx⟩ := hp
    simp only [Except.ok.injEq] at hx; subst hx
    unfold readStmts; simp [readTerm_printTerm v hr.1, read_print_stmts hl rest hr.2 ht]
  | .cons (.ifElse test thenB elseB) rest, hr, hp => by
    simp only [readableStmts, Bool.and_eq_true] at hr
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hr
    simp only [printStmts, bind_eq_ok] at hp
    obtain ⟨a, ha, b, hb, t, ht, hx⟩ := hp
    simp only [Except.ok.injEq] at hx; subst hx
    unfold readStmts
    simp [readTerm_printTerm test h1, read_print_stmts hl thenB h2 ha,
      read_print_stmts hl elseB h3 hb, read_print_stmts hl rest h4 ht]
  | .cons (.whileTrue body) rest, hr, hp => by
    simp only [readableStmts, Bool.and_eq_true] at hr
    simp only [printStmts, bind_eq_ok] at hp
    obtain ⟨b, hb, t, ht, hx⟩ := hp
    simp only [Except.ok.injEq] at hx; subst hx
    unfold readStmts; simp [read_print_stmts hl body hr.1 hb, read_print_stmts hl rest hr.2 ht]
  | .cons .breakLoop rest, hr, hp => by
    simp only [readableStmts] at hr
    simp only [printStmts, bind_eq_ok] at hp
    obtain ⟨t, ht, hx⟩ := hp
    simp only [Except.ok.injEq] at hx; subst hx
    unfold readStmts; simp [read_print_stmts hl rest hr ht]
termination_by structural ss

theorem read_print_effs {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} (es : Effs Op)
    (hr : readableEffs sig spell n es = true) {xs : List Expr}
    (hp : printEffs sig n es = .ok xs) : readEffs sig spell n xs = .ok es :=
  match es, hr, hp with
  | .nil, _, hp => by
    simp only [printEffs, Except.ok.injEq] at hp; subst hp; rfl
  | .cons e rest, hr, hp => by
    simp only [readableEffs, Bool.and_eq_true] at hr
    simp only [printEffs, bind_eq_ok] at hp
    obtain ⟨h, hh, t, ht, hx⟩ := hp
    simp only [Except.ok.injEq] at hx; subst hx
    unfold readEffs; simp [read_print hl e hr.1 hh, read_print_effs hl rest hr.2 ht]
termination_by structural es

theorem read_print_action {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} (a : ActionTerm Op)
    (hr : readableAction sig spell n a = true) {x : Expr}
    (hp : printAction sig n a = .ok x) : readEff sig spell n x = .ok (.withFiber a) :=
  match a, hr, hp with
  | .fork program options, hr, hp => by
    simp only [readableAction] at hr
    simp only [printAction, bind_eq_ok] at hp
    obtain ⟨p, hpp, hx⟩ := hp
    simp only [Except.ok.injEq] at hx; subst hx
    obtain ⟨s, d, m⟩ := options
    have ih := read_print hl program hr hpp
    have ho := readForkOptions_print ⟨s, d, m⟩
    cases d with
    | false =>
      unfold readEff readHead
      simp [headOf_lit .forkChild "Effect.forkChild" rfl, ih, ho]
    | true =>
      unfold readEff readHead
      simp [headOf_lit .forkDetach "Effect.forkDetach" rfl, ih, ho]
  | .forkIn program options scope, hr, hp => by
    simp only [readableAction, Bool.and_eq_true, Bool.not_eq_true'] at hr
    obtain ⟨⟨h1, hd⟩, h3⟩ := hr
    simp only [printAction, bind_eq_ok] at hp
    obtain ⟨p, hpp, hx⟩ := hp
    simp only [Except.ok.injEq] at hx; subst hx
    have ho := readForkOptions_print options
    rw [hd] at ho
    unfold readEff readHead
    simp [headOf_lit .forkIn "Effect.forkIn" rfl, read_print hl program h1 hpp,
      readTerm_printTerm scope h3, ho]
  | .forkScoped program options, hr, hp => by
    simp only [readableAction, Bool.and_eq_true, Bool.not_eq_true'] at hr
    obtain ⟨h1, hd⟩ := hr
    simp only [printAction, bind_eq_ok] at hp
    obtain ⟨p, hpp, hx⟩ := hp
    simp only [Except.ok.injEq] at hx; subst hx
    have ho := readForkOptions_print options
    rw [hd] at ho
    unfold readEff readHead
    simp [headOf_lit .forkScoped "Effect.forkScoped" rfl, read_print hl program h1 hpp, ho]
  | .runIn target scope, hr, hp => by
    simp only [readableAction, Bool.and_eq_true] at hr
    simp only [printAction, Except.ok.injEq] at hp; subst hp
    unfold readEff readHead
    simp [headOf_lit .runIn "Fiber.runIn" rfl, readTerm_printTerm target hr.1,
      readTerm_printTerm scope hr.2]
  | .interrupt target, hr, hp => by
    simp only [readableAction] at hr
    simp only [printAction, Except.ok.injEq] at hp; subst hp
    unfold readEff readHead
    simp [headOf_lit .interrupt "Fiber.interrupt" rfl, readTerm_printTerm target hr]
  | .interruptScoped _, _, hp => by simp [printAction] at hp
  | .interruptAll targets none, hr, hp => by
    simp only [readableAction] at hr
    simp only [printAction, Except.ok.injEq] at hp; subst hp
    unfold readEff readHead
    simp [headOf_lit .interruptAll "Fiber.interruptAll" rfl, readTerm_printTerm targets hr]
  | .interruptAll targets (some who), hr, hp => by
    simp only [readableAction, Bool.and_eq_true] at hr
    simp only [printAction, Except.ok.injEq] at hp; subst hp
    unfold readEff readHead
    simp [headOf_lit .interruptAllAs "Fiber.interruptAllAs" rfl, readTerm_printTerm targets hr.1,
      readTerm_printTerm who hr.2]
  | .awaitAll targets, hr, hp => by
    simp only [readableAction] at hr
    simp only [printAction, Except.ok.injEq] at hp; subst hp
    unfold readEff readHead
    simp [headOf_lit .awaitAll "Fiber.awaitAll" rfl, readTerm_printTerm targets hr]
  | .awaitAllFailFast _, _, hp => by simp [printAction] at hp
  | .snapshotChildren, _, hp => by simp [printAction] at hp
  | .awaitNewChildren _, _, hp => by simp [printAction] at hp
  | .raceAll entrants, hr, hp => by
    simp only [readableAction] at hr
    simp only [printAction, bind_eq_ok] at hp
    obtain ⟨items, hitems, hx⟩ := hp
    simp only [Except.ok.injEq] at hx; subst hx
    unfold readEff readHead
    simp [headOf_lit .raceAll "Effect.raceAll" rfl, read_print_effs hl entrants hr hitems]
  | .setContext _, _, hp => by simp [printAction] at hp
  | .getContext, _, hp => by
    simp only [printAction, Except.ok.injEq] at hp; subst hp
    unfold readEff readHead; simp [headOf_lit .context "Effect.context" rfl]
  | .getId, _, hp => by
    simp only [printAction, Except.ok.injEq] at hp; subst hp
    unfold readEff
    simp [Var.read_none Var.name_ne_fiberId, headOf_lit .fiberId "Effect.fiberId" rfl]
  | .closeScope scope exit, hr, hp => by
    simp only [readableAction, Bool.and_eq_true] at hr
    simp only [printAction, Except.ok.injEq] at hp; subst hp
    unfold readEff readHead
    simp [headOf_lit .scopeClose "Scope.close" rfl, readTerm_printTerm scope hr.1,
      readTerm_printTerm exit hr.2]
termination_by structural a
end


/-- The printed form of a row answer: both kinds print through `printRow`. -/
theorem print_rowAnswer (sig : Signature Op) (n : Nat) (op : Op) (r : Term) :
    print sig n (rowAnswer (sig.rowOf op) op r) = .ok (printRow (sig.rowOf op) r) := by
  unfold rowAnswer; split <;> simp [print]


section ReadExact

/-- Closes an arm of a wildcard case of the reader: the arm's own negated-pattern hypothesis
is contradictory, or the arm is a refusal. -/
local macro "close_arm" h:ident : tactic => `(tactic| first
  | (exfalso; subst_vars; solve_by_elim [rfl])
  | cases $h:ident
  | (split at $h:ident <;> first | (exfalso; subst_vars; solve_by_elim [rfl]) | cases $h:ident))

/-- The exactness of the reader, over the four mutual readers at once, by the functional
induction principle Lean generates for `readEff`: one case per arm of the reader. -/
theorem read_exact_all {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) (n : Nat) (x : Expr) :
    ∀ e, readEff sig spell n x = .ok e → print sig n e = .ok x := by
  apply readEff.induct sig spell
    (motive_1 := fun n x => ∀ e, readEff sig spell n x = .ok e → print sig n e = .ok x)
    (motive_2 := fun n h args => ∀ e, readHead sig spell n h args = .ok e →
      print sig n e = .ok (.call (.ident h.spelling) args))
    (motive_3 := fun n items => ∀ es, readEffs sig spell n items = .ok es →
      printEffs sig n es = .ok items)
    (motive_4 := fun n stmts => ∀ ss, readStmts sig spell n stmts = .ok ss →
      printStmts sig n ss = .ok stmts)
  -- readEff
  case case1 =>
    intro n s i hi e h
    unfold readEff at h; simp only [hi] at h; cases h
    obtain ⟨hs, _⟩ := Var.read_exact hi
    simp [print, printTerm, hs]
  case case2 =>
    intro n s hr hh e h
    unfold readEff at h; simp only [hr, hh] at h; cases h
    simp [print, printAction, headOf_exact hh, Head.spelling]
  case case3 =>
    intro n s hr hh e h
    unfold readEff at h; simp only [hr, hh] at h; cases h
    simp [print, printTerm, printLit, headOf_exact hh, Head.spelling]
  case case4 =>
    intro n s hr val h1 h2 hh e h
    unfold readEff at h; simp only [hr, hh] at h
    cases val <;> simp_all
  case case5 =>
    intro n s hr hh e h
    unfold readEff at h; simp only [hr, hh] at h
    unfold readRowValue at h
    split at h
    · rename_i op hsp
      split at h
      · rename_i hshape
        cases h
        obtain ⟨hs, _⟩ := hl.row_of_spell _ _ _ hsp
        rw [print_rowAnswer]
        simp [printRow, hshape, hs]
      · cases h
    · cases h
  case case6 =>
    intro n k hk e h
    unfold readEff at h; simp only [hk, if_true] at h; cases h
    simp [print, printTerm, printLit, Int.toNat_of_nonneg hk]
  case case7 =>
    intro n k hk e h
    unfold readEff at h; simp [hk] at h
  case case8 =>
    intro n b e h
    unfold readEff at h; simp at h; subst h; simp [print, printTerm, printLit]
  case case9 =>
    intro n s e h
    unfold readEff at h; simp at h; subst h; simp [print, printTerm, printLit]
  case case10 =>
    intro n atom args hd hh ih e h
    unfold readEff at h; simp only [hh] at h
    rw [headOf_exact hh]
    exact ih e h
  case case11 =>
    intro n atom args hh answer hrow e h
    unfold readEff at h; simp only [hh, hrow] at h
    subst h
    unfold readRowCall at hrow
    split at hrow
    · rename_i op hA
      simp only [Option.some.injEq] at hrow
      split at hrow
      · rename_i hc
        cases hrow
        obtain ⟨names, hnames, hsp⟩ := Option.bind_eq_some_iff.mp hA
        obtain ⟨hs, htr⟩ := hl.row_of_spell _ _ _ hsp
        rw [print_rowAnswer, idents?_exact hnames]
        simp [printRow, hc.1, hc.2, hs, htr]
      · cases hrow
    · split at hrow
      · split at hrow
        · simp only [Option.some.injEq] at hrow
          split at hrow
          · rename_i hc
            simp only [map_eq_ok] at hrow
            obtain ⟨r, hr, he⟩ := hrow
            subst he
            obtain ⟨names, hnames, hsp⟩ :=
              Option.bind_eq_some_iff.mp ‹(idents? _).bind (spell atom) = some _›
            obtain ⟨hs, htr⟩ := hl.row_of_spell _ _ _ hsp
            rw [print_rowAnswer, idents?_exact hnames]
            simp [printRow, hc.1, hc.2, hs, htr, readTerm_exact _ hr]
          · cases hrow
        · cases hrow
      · cases hrow
  case case12 =>
    intro n atom args hh hrow e h
    unfold readEff at h; simp only [hh, hrow, map_eq_ok] at h
    obtain ⟨ts, hts, rfl⟩ := h
    simp [print, printTerm, readTerms_exact args hts]
  case case13 =>
    intro t n h1 h2 h3 h4 h5 e h
    unfold readEff at h
    split at h <;> close_arm h
  -- readHead
  case case14 =>
    intro n v e h
    unfold readHead at h; simp only [map_eq_ok] at h
    obtain ⟨t, ht, rfl⟩ := h
    simp [print, readTerm_exact v ht, Head.spelling]
  case case15 =>
    intro n v e h
    unfold readHead at h; simp only [map_eq_ok] at h
    obtain ⟨t, ht, rfl⟩ := h
    simp [print, readTerm_exact v ht, Head.spelling]
  case case16 =>
    intro n c e h
    unfold readHead at h; simp only [map_eq_ok] at h
    obtain ⟨t, ht, rfl⟩ := h
    simp [print, readCause_exact c ht, Head.spelling]
  case case17 =>
    intro n t e h
    unfold readHead at h; simp only [map_eq_ok] at h
    obtain ⟨t', ht, rfl⟩ := h
    simp [print, readTerm_exact t ht, Head.spelling]
  case case18 =>
    intro n t a b iha ihb e h
    unfold readHead at h; simp only [bind_eq_ok] at h
    obtain ⟨test, htest, x, hx, y, hy, he⟩ := h
    cases he
    simp [print, iha x hx, ihb y hy, readTerm_exact t htest, Head.spelling]
  case case19 =>
    intro n body hnc ih e h
    unfold readHead at h
    cases body <;> first
      | exact (hnc _ _ _ rfl).elim
      | (simp only [map_eq_ok] at h; obtain ⟨b', hb', rfl⟩ := h; simp [print, ih _ hb', Head.spelling])
  case case20 =>
    intro n cursor initial loop fw test fb body fs answer cursor' step hc ih e h
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hc
    unfold readHead at h
    simp only [and_self, if_true, bind_eq_ok] at h
    obtain ⟨i, hi, t, ht, s, hs, b, hb, he⟩ := h
    cases he
    simp [print, ih b hb, readTerm_exact initial hi, readTerm_exact test ht, readTerm_exact step hs,
      Head.spelling]
  case case21 =>
    intro n cursor initial loop fw test fb body fs answer cursor' step hc e h
    unfold readHead at h; simp [hc] at h
  case case22 =>
    intro n first rest ih1 ih2 e h
    unfold readHead at h
    simp only [if_true, bind_eq_ok] at h
    obtain ⟨f, hf, r, hr, he⟩ := h
    cases he
    simp [print, ih1 f hf, ih2 r hr, Head.spelling]
  case case23 =>
    intro n first x rest hx e h
    unfold readHead at h; simp [hx] at h
  case case24 =>
    intro n body ih e h
    unfold readHead at h; simp only [map_eq_ok] at h
    obtain ⟨ss, hss, rfl⟩ := h
    simp [print, ih ss hss, Head.spelling]
  case case25 =>
    intro n body handler ih1 ih2 e h
    unfold readHead at h
    simp only [if_true, bind_eq_ok] at h
    obtain ⟨b, hb, hd, hhd, he⟩ := h
    cases he
    simp [print, ih1 b hb, ih2 hd hhd, Head.spelling]
  case case26 =>
    intro n body x handler hx e h
    unfold readHead at h; simp [hx] at h
  case case27 =>
    intro n body ff x onCause fs y onValue hc ih1 ih2 ih3 e h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hc
    unfold readHead at h
    simp only [and_self, if_true, bind_eq_ok] at h
    obtain ⟨b, hb, v, hv, c, hc, he⟩ := h
    cases he
    simp [print, ih1 b hb, ih2 v hv, ih3 c hc, Head.spelling]
  case case28 =>
    intro n body ff x onCause fs y onValue hc e h
    unfold readHead at h; simp [hc] at h
  case case29 =>
    intro n body finalizer ih1 ih2 e h
    unfold readHead at h
    simp only [if_true, bind_eq_ok] at h
    obtain ⟨b, hb, f, hf, he⟩ := h
    cases he
    simp [print, ih1 b hb, ih2 f hf, Head.spelling]
  case case30 =>
    intro n body x finalizer hx e h
    unfold readHead at h; simp [hx] at h
  case case31 =>
    intro n body ih e h
    unfold readHead at h; simp only [map_eq_ok] at h
    obtain ⟨b, hb, rfl⟩ := h
    simp [print, ih b hb, Head.spelling]
  case case32 =>
    intro n body ih e h
    unfold readHead at h; simp only [map_eq_ok] at h
    obtain ⟨b, hb, rfl⟩ := h
    simp [print, ih b hb, Head.spelling]
  case case33 =>
    intro n body ih e h
    unfold readHead at h; simp only [map_eq_ok] at h
    obtain ⟨b, hb, rfl⟩ := h
    simp [print, ih b hb, Head.spelling]
  case case34 =>
    intro n k hk e h
    unfold readHead at h; simp only [hk, if_true] at h; cases h
    simp [print, Int.toNat_of_nonneg hk, Head.spelling]
  case case35 =>
    intro n k hk e h
    unfold readHead at h; simp [hk] at h
  case case36 =>
    intro n fiber e h
    unfold readHead at h; simp only [map_eq_ok] at h
    obtain ⟨t, ht, rfl⟩ := h
    simp [print, readTerm_exact fiber ht, Head.spelling]
  case case37 =>
    intro n fiber e h
    unfold readHead at h; simp only [map_eq_ok] at h
    obtain ⟨t, ht, rfl⟩ := h
    simp [print, readTerm_exact fiber ht, Head.spelling]
  case case38 =>
    intro n program options ih e h
    unfold readHead at h; simp only [bind_eq_ok] at h
    obtain ⟨p, hp, o, ho, he⟩ := h
    cases he
    obtain ⟨hpo, hd⟩ := readForkOptions_exact ho
    simp [print, printAction, ih p hp, hpo, hd, Head.spelling]
  case case39 =>
    intro n program options ih e h
    unfold readHead at h; simp only [bind_eq_ok] at h
    obtain ⟨p, hp, o, ho, he⟩ := h
    cases he
    obtain ⟨hpo, hd⟩ := readForkOptions_exact ho
    simp [print, printAction, ih p hp, hpo, hd, Head.spelling]
  case case40 =>
    intro n program scope options ih e h
    unfold readHead at h; simp only [bind_eq_ok] at h
    obtain ⟨p, hp, s, hs, o, ho, he⟩ := h
    cases he
    obtain ⟨hpo, _⟩ := readForkOptions_exact ho
    simp [print, printAction, ih p hp, readTerm_exact scope hs, hpo, Head.spelling]
  case case41 =>
    intro n program options ih e h
    unfold readHead at h; simp only [bind_eq_ok] at h
    obtain ⟨p, hp, o, ho, he⟩ := h
    cases he
    obtain ⟨hpo, _⟩ := readForkOptions_exact ho
    simp [print, printAction, ih p hp, hpo, Head.spelling]
  case case42 =>
    intro n target scope e h
    unfold readHead at h; simp only [bind_eq_ok] at h
    obtain ⟨t, ht, s, hs, he⟩ := h
    cases he
    simp [print, printAction, readTerm_exact target ht, readTerm_exact scope hs, Head.spelling]
  case case43 =>
    intro n target e h
    unfold readHead at h; simp only [map_eq_ok] at h
    obtain ⟨t, ht, rfl⟩ := h
    simp [print, printAction, readTerm_exact target ht, Head.spelling]
  case case44 =>
    intro n targets e h
    unfold readHead at h; simp only [map_eq_ok] at h
    obtain ⟨t, ht, rfl⟩ := h
    simp [print, printAction, readTerm_exact targets ht, Head.spelling]
  case case45 =>
    intro n targets who e h
    unfold readHead at h; simp only [bind_eq_ok] at h
    obtain ⟨t, ht, w, hw, he⟩ := h
    cases he
    simp [print, printAction, readTerm_exact targets ht, readTerm_exact who hw, Head.spelling]
  case case46 =>
    intro n targets e h
    unfold readHead at h; simp only [map_eq_ok] at h
    obtain ⟨t, ht, rfl⟩ := h
    simp [print, printAction, readTerm_exact targets ht, Head.spelling]
  case case47 =>
    intro n entrants ih e h
    unfold readHead at h; simp only [map_eq_ok] at h
    obtain ⟨es, hes, rfl⟩ := h
    simp [print, printAction, ih es hes, Head.spelling]
  case case48 =>
    intro n e h
    unfold readHead at h; simp at h; subst h
    simp [print, printAction, Head.spelling]
  case case49 =>
    intro n scope exit e h
    unfold readHead at h; simp only [bind_eq_ok] at h
    obtain ⟨s, hs, x, hx, he⟩ := h
    cases he
    simp [print, printAction, readTerm_exact scope hs, readTerm_exact exit hx, Head.spelling]
  case case50 =>
    intro n body ih e h
    unfold readHead at h; simp only [map_eq_ok] at h
    obtain ⟨b, hb, rfl⟩ := h
    simp [print, ih b hb, Head.spelling]
  case case51 =>
    intro n acquire x y release hxy ih1 ih2 e h
    obtain ⟨rfl, rfl⟩ := hxy
    unfold readHead at h
    simp only [and_self, if_true, bind_eq_ok] at h
    obtain ⟨a, ha, r, hr, he⟩ := h
    cases he
    simp [print, ih1 a ha, ih2 r hr, Head.spelling]
  case case52 =>
    intro n acquire x y release hne e h
    unfold readHead at h; simp [hne] at h
  case case53 => intro t n e h; unfold readHead at h; simp at h
  case case54 => intro t n e h; unfold readHead at h; simp at h
  case case55 => intro t n e h; unfold readHead at h; simp at h
  case case56 => intro t n e h; unfold readHead at h; simp at h
  case case57 => intro t n e h; unfold readHead at h; simp at h
  case case58 => intro t n e h; unfold readHead at h; simp at h
  case case59 => intro t n e h; unfold readHead at h; simp at h
  case case60 =>
    intro n hd t
    intros
    rename_i e h
    unfold readHead at h
    split at h <;> close_arm h
  -- readEffs
  case case61 =>
    intro n es h
    unfold readEffs at h; simp at h; subst h; rfl
  case case62 =>
    intro n x rest ih1 ih2 es h
    unfold readEffs at h; simp only [bind_eq_ok] at h
    obtain ⟨e, he, es', hes', hes⟩ := h
    cases hes
    simp [printEffs, ih1 e he, ih2 es' hes']
  -- readStmts
  case case63 =>
    intro n ss h
    unfold readStmts at h; simp at h; subst h; rfl
  case case64 =>
    intro n value rest ih1 ih2 ss h
    unfold readStmts at h
    simp only [if_true, bind_eq_ok] at h
    obtain ⟨e, he, tail, htail, hss⟩ := h
    cases hss
    simp [printStmts, ih1 e he, ih2 tail htail]
  case case65 =>
    intro n x value rest hx ss h
    unfold readStmts at h; simp [hx] at h
  case case66 =>
    intro n value rest ih1 ih2 ss h
    unfold readStmts at h; simp only [bind_eq_ok] at h
    obtain ⟨e, he, tail, htail, hss⟩ := h
    cases hss
    simp [printStmts, ih1 e he, ih2 tail htail]
  case case67 =>
    intro n value rest ih ss h
    unfold readStmts at h; simp only [bind_eq_ok] at h
    obtain ⟨v, hv, tail, htail, hss⟩ := h
    cases hss
    simp [printStmts, readTerm_exact value hv, ih tail htail]
  case case68 =>
    intro n test thenB elseB rest ih1 ih2 ih3 ss h
    unfold readStmts at h; simp only [bind_eq_ok] at h
    obtain ⟨t, ht, a, ha, b, hb, tail, htail, hss⟩ := h
    cases hss
    simp [printStmts, readTerm_exact test ht, ih1 a ha, ih2 b hb, ih3 tail htail]
  case case69 =>
    intro n body rest ih1 ih2 ss h
    unfold readStmts at h; simp only [bind_eq_ok] at h
    obtain ⟨b, hb, tail, htail, hss⟩ := h
    cases hss
    simp [printStmts, ih1 b hb, ih2 tail htail]
  case case70 =>
    intro n rest ih ss h
    unfold readStmts at h; simp only [bind_eq_ok] at h
    obtain ⟨tail, htail, hss⟩ := h
    cases hss
    simp [printStmts, ih tail htail]
  case case71 =>
    intro n head tail
    intros
    rename_i ss h
    rcases head with ⟨x, v⟩ | ⟨v⟩ | ⟨v⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨_ | _, b⟩ | ⟨a, b⟩ | ⟨a, b, c⟩
      | ⟨a, b⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨_ | _⟩ | ⟨_⟩ | ⟨_⟩ <;>
      unfold readStmts at h <;> (try dsimp only at h) <;> close_arm h


/-- `read_exact`: what the reader accepts prints back to exactly the tree it read. -/
theorem read_exact {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} {x : Expr} {e : Eff Op}
    (h : readEff sig spell n x = .ok e) : print sig n e = .ok x :=
  read_exact_all hl n x e h

end ReadExact

/-! ## The native profile

`nativeSpell` inverts `NativeOp.row` on (spelling, trailing names): the forty read-modify-write
rows share eight spellings and are told apart by the pure function's name, the two `Scope.make`
rows by the `"parallel"` strategy. `nativeLawful` is the receipt that the native table meets
`LawfulSpelling`; the two theorems specialise to it below. -/

def fnNames : List Effect4.Machine.FnName := [.incr, .double, .zeroWhenPositive, .noChange, .takeAndBump]

/-- Every native operation, once. -/
def NativeOp.all : List NativeOp :=
  [.refMake, .refGet, .refSet, .refGetAndSet, .refSetAndGet]
  ++ fnNames.flatMap (fun f =>
      [.refUpdate f, .refGetAndUpdate f, .refUpdateAndGet f, .refUpdateSome f,
       .refGetAndUpdateSome f, .refUpdateSomeAndGet f, .refModify f, .refModifySome f])
  ++ [.deferredMake, .deferredIsDone, .deferredPoll, .deferredSucceed, .deferredFail,
      .deferredAwait, .scopeMake .sequential, .scopeMake .parallel]

/-- The native row a (spelling, trailing names) pair names. -/
def nativeSpell (s : String) (names : List String) : Option NativeOp :=
  NativeOp.all.find? fun op => decide (op.row.spelling = s ∧ op.row.trailing = names)

theorem name_notin (l : List String) (h : ∀ s ∈ l, s.toByteArray.data.toList.head? ≠ some 97)
    (i : Nat) : Var.name i ∉ l := fun hm => Var.name_ne (h _ hm) i rfl

theorem NativeOp.all_complete (op : NativeOp) : op ∈ NativeOp.all := by
  cases op <;> first | decide | (rename_i f; cases f <;> decide)

theorem nativeLawful : LawfulSpelling nativeSignature nativeSpell where
  spell_row := by
    intro op
    cases op <;> first | decide | (rename_i f; cases f <;> decide)
  row_of_spell := by
    intro s names op h
    have := List.find?_some h
    simpa [nativeSignature] using this
  value_trailing := by
    intro op
    cases op <;> first | decide | (rename_i f; cases f <;> decide)
  spelling_ne_name := by
    intro op i
    cases op <;> first
      | exact (Var.name_ne (by decide) i).symm
      | (rename_i f; cases f <;> exact (Var.name_ne (by decide) i).symm)
  spelling_not_reserved := by
    intro op
    cases op <;> first | decide | (rename_i f; cases f <;> decide)
  trailing_ne_name := by
    intro op i
    cases op <;> first
      | exact name_notin _ (by decide) i
      | (rename_i f; cases f <;> exact name_notin _ (by decide) i)
  trailing_ne_undefined := by
    intro op
    cases op <;> first | decide | (rename_i f; cases f <;> decide)


theorem read_print_native {n : Nat} (e : NativeEff)
    (hr : readable nativeSignature nativeSpell n e = true) {x : Expr}
    (hp : print nativeSignature n e = .ok x) : readEff nativeSignature nativeSpell n x = .ok e :=
  read_print nativeLawful e hr hp

/-- `read_print` as the round trip: a readable program that prints comes back as itself. -/
theorem roundTrip_eq {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} {e : Eff Op}
    (hr : readable sig spell n e = true) {x : Expr} (hp : print sig n e = .ok x) :
    roundTrip sig spell n e = .ok e := by
  unfold roundTrip; rw [hp]; exact read_print hl e hr hp

theorem read_exact_native {n : Nat} {x : Expr} {e : NativeEff}
    (h : readEff nativeSignature nativeSpell n x = .ok e) : print nativeSignature n e = .ok x :=
  read_exact nativeLawful h

end Effect4.Program
