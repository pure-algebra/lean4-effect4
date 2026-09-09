import Effect4.Codegen.Print
import Effect4.Program.Native

/-!
# Codegen.Read — the printer's image back into `Eff` (lane A4 of the AST relation)

Plan: `docs/research/2026-09-04-a4-reader-plan.md`, under
`docs/research/2026-09-04-ast-relation-plan.md` §5.2. `readEff` is the inverse of `print`
(`src/Effect4/Codegen/Print.lean`) constructor by constructor, over the same target fragment
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
Service keys decode those decimal bytes and check the full canonical spelling,
including the type argument supplied by the signature.
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
  | causeCombine | undefined | withFiber
  -- the join (2026-09-07): the three context constructors and the layer spellings the printer
  -- emits; layers and keys are read only in the positions that accept them
  | contextService | provide | service | provideService
  | layerSucceed | layerEffect | layerEffectDiscard | layerProvide | layerProvideMerge
  | layerMerge | layerFresh | layerOrDie
  -- the host rows slice (2026-09-08): the n-ary merge; a layer reference is an identifier,
  -- not a head
  | layerMergeAll
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
  | .withFiber => "Effect.withFiber"
  | .contextService => "Context.Service"
  | .provide => "Effect.provide"
  | .service => "Effect.service"
  | .provideService => "Effect.provideService"
  | .layerSucceed => "Layer.succeed"
  | .layerEffect => "Layer.effect"
  | .layerEffectDiscard => "Layer.effectDiscard"
  | .layerProvide => "Layer.provide"
  | .layerProvideMerge => "Layer.provideMerge"
  | .layerMerge => "Layer.merge"
  | .layerFresh => "Layer.fresh"
  | .layerOrDie => "Layer.orDie"
  | .layerMergeAll => "Layer.mergeAll"

/-- Every head, once. -/
def heads : List Head :=
  [ .succeed, .fail, .failCause, .sync, .suspend, .flatMap, .gen, .catchCause
  , .matchCauseEffect, .onExit, .exit, .uninterruptible, .interruptible, .whileLoop
  , .yieldNowWith, .join, .await, .forkChild, .forkDetach, .forkIn, .forkScoped, .runIn
  , .interrupt, .interruptAll, .interruptAllAs, .awaitAll, .raceAll, .context, .fiberId
  , .scopeClose, .scoped, .acquireRelease, .causeFail, .causeDie, .causeInterrupt
  , .causeCombine, .undefined, .withFiber
  , .contextService, .provide, .service, .provideService
  , .layerSucceed, .layerEffect, .layerEffectDiscard, .layerProvide, .layerProvideMerge
  , .layerMerge, .layerFresh, .layerOrDie, .layerMergeAll ]

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

/-- The saved variable whose two components a tuple-call row receives, when its two
arguments are exactly `fst(a)` and `snd(a)` of one identifier `a` (source-repairs §18). -/
def savedVar? : Expr → Expr → Option String
  | .call (.ident f) [.ident v], .call (.ident g) [.ident w] =>
    if f = "fst" ∧ g = "snd" ∧ v = w then some v else none
  | _, _ => none

theorem savedVar?_some {x y : Expr} {v : String} (h : savedVar? x y = some v) :
    x = .call (.ident "fst") [.ident v] ∧ y = .call (.ident "snd") [.ident v] := by
  unfold savedVar? at h
  split at h
  · split at h
    · rename_i hc
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨rfl, rfl, rfl⟩ := hc
      exact ⟨rfl, rfl⟩
    · cases h
  · cases h

/-- The request of a tuple-call row from its two arguments: the components of one saved
variable read back as that variable, any other two terms as their `pair` application. -/
def readTupleArgs (n : Nat) (x y : Expr) : Except ReadRefusal Term :=
  match savedVar? x y with
  | some v => readTerm n (.ident v)
  | none => do
    let a ← readTerm n x
    let b ← readTerm n y
    .ok (.app "pair" (.cons a (.cons b .nil)))

/-- A call as a call row; `none` when no row of the table has this head and argument
shape, so the caller may read an atom application instead. A call row's argument list is
the trailing names alone on a `unit` request, and the request followed by the trailing
names otherwise; a tuple-call row's is its two request arguments followed by the trailing
names. The three readings are tried in that order, and `LawfulSpelling` is what makes at
most one succeed. -/
def readRowCall (sig : Signature Op) (spell : String → List String → Option Op) (n : Nat)
    (s : String) (typeArgs : List String) (args : List Expr) : Option (Except ReadRefusal (Eff Op)) :=
  -- the call's type arguments must be exactly the ones the row declares: a row that needs
  -- them refuses a bare call, and a row that declares none refuses a call that carries any
  -- (`E4-CHECK-CE-013`)
  match (idents? args).bind (spell s) with
  | some op =>
    some (if (sig.rowOf op).shape = .call ∧ (sig.rowOf op).request = Ty.unit ∧
        (sig.rowOf op).typeArgs = typeArgs then
      .ok (rowAnswer (sig.rowOf op) op (.lit .unit))
    else .error (.arity s))
  | none =>
    match args with
    | request :: rest =>
      match (idents? rest).bind (spell s) with
      | some op =>
        some (if (sig.rowOf op).shape = .call ∧ (sig.rowOf op).request ≠ Ty.unit ∧
            (sig.rowOf op).typeArgs = typeArgs then
          (readTerm n request).map (rowAnswer (sig.rowOf op) op)
        else .error (.arity s))
      | none =>
        match rest with
        | second :: names =>
          match (idents? names).bind (spell s) with
          | some op =>
            some (if (sig.rowOf op).shape = .tupleCall ∧
                (sig.rowOf op).typeArgs = typeArgs then
              (readTupleArgs n request second).map (rowAnswer (sig.rowOf op) op)
            else .error (.arity s))
          | none => none
        | [] => none
    | [] => none

/-- The ordinary call view of each row's method arguments; row identities and
argument-name hygiene are unchanged. -/
def methodSignature (sig : Signature Op) : Signature Op :=
  { sig with rowOf := fun op => methodArgsRow (sig.rowOf op) }

def addReceiver (sig : Signature Op) (receiver : Term) : Eff Op → Except ReadRefusal (Eff Op)
  | .perform op args | .callback op args =>
    if (sig.rowOf op).shape = .method then
      .ok (rowAnswer (sig.rowOf op) op (.app "pair" (.cons receiver (.cons args .nil))))
    else .error (.shape "method row")
  | _ => .error (.shape "method row")

/-- Method arguments use the same three arity readings as ordinary row calls. -/
def readRowMethod (sig : Signature Op) (spell : String → List String → Option Op) (n : Nat)
    (receiver : Expr) (s : String) (typeArgs : List String) (args : List Expr) :
    Except ReadRefusal (Eff Op) := do
  let recv ← readTerm n receiver
  let body ← (readRowCall (methodSignature sig) spell n s typeArgs args).getD
    (.error (.unknownHead s))
  addReceiver sig recv body

/-- Methods have their own receiver syntax. Empty generic lists are outside the printed image. -/
def readMethod (sig : Signature Op) (spell : String → List String → Option Op) (n : Nat)
    (x : Expr) : Except ReadRefusal (Eff Op) :=
  match x with
  | .method receiver s args => readRowMethod sig spell n receiver s [] args
  | .call (.generic (.member receiver s) (ta :: tas)) args =>
    readRowMethod sig spell n receiver s (ta :: tas) args
  | _ => .error (.shape "expression")

/-- The canonical adapter for the synchronous rc.112 `Fiber.runIn` export. The
callback adds no binder, links the fiber once, and returns the unit effect. -/
def readRunIn (n : Nat) (args : List Expr) : Except ReadRefusal (Eff Op) :=
  match args with
  | [.arrowBlock [] [.exprStmt (.call (.ident runIn) [target, scope]), .ret (.ident unit)]] =>
    if runIn = "Fiber.runIn" ∧ unit = "Effect.void" then do
      let t ← readTerm n target
      let s ← readTerm n scope
      .ok (.withFiber (.runIn t s))
    else .error (.shape "runIn")
  | _ => .error (.shape "runIn")

/-- The digit a byte spells, `'0'` as `0`. -/
def digitOfByte (b : UInt8) : Nat := b.toNat - 48

/-- The number a byte string spells in decimal. -/
def decodeBytes (bs : List UInt8) : Nat := bs.foldl (fun acc b => acc * 10 + digitOfByte b) 0

/-- Decode the two numeric fields; `readKey` checks the complete canonical spelling. -/
def keyFromText (text : String) : ServiceKey :=
  let bytes := text.toByteArray.data.toList.drop 1
  ⟨⟨decodeBytes (bytes.takeWhile (· != 95))⟩,
    ⟨decodeBytes ((bytes.dropWhile (· != 95)).drop 1)⟩⟩

def keyText (key : ServiceKey) : String :=
  "k" ++ toString key.name.value ++ "_" ++ toString key.service.value

/-- Only the exact printed key is admitted, including its optional type argument. -/
def readKey {Op : Type} (sig : Signature Op) : Expr → Except ReadRefusal ServiceKey
  | .call (.ident head) [.str text] =>
    let key := keyFromText text
    if head = "Context.Service" ∧ sig.serviceTy key = none ∧ text = keyText key then
      .ok key
    else .error (.shape "service key")
  | .call (.generic (.ident head) [arg]) [.str text] =>
    let key := keyFromText text
    match sig.serviceTy key with
    | some ty =>
      if head = "Context.Service" ∧ arg = ty.render ∧ text = keyText key then
        .ok key
      else .error (.shape "service key")
    | none => .error (.shape "service key")
  | _ => .error (.shape "service key")

/-- The literal domain of `Layer.succeed`, using the ordinary term reader. -/
def readLiteral (x : Expr) : Except ReadRefusal Lit := do
  let term ← readTerm 0 x
  match term with
  | .lit value => .ok value
  | _ => .error (.shape "literal")

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
        match readRowCall sig spell n s [] args with
        | some answer => answer
        | none => (readTerms n args).map fun ts => .yieldError (.app s ts)
    -- a call carrying explicit type arguments is a row call and nothing else: no reserved
    -- head and no atom application is printed with them. An *empty* argument list is not a
    -- spelling the printer emits, so it falls through to the shape refusal
    -- (`E4-CHECK-CE-013`).
    | .call (.generic (.ident s) (ta :: tas)) args =>
      match readRowCall sig spell n s (ta :: tas) args with
      | some answer => answer
      | none => .error (.unknownHead s)
    | _ => readMethod sig spell n x
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
    -- `forkIn` and `forkScoped` are *daemon* forks in rc.112: `internal/effect.ts:5366`
    -- passes `true` for `forkUnsafe`'s `daemon` parameter (`:5264-5269`), and `forkScoped`
    -- is `flatMap(scope, scope => forkIn(self, scope, options))` (`:5406`). The printed
    -- options object therefore carries no daemon field to recover — the export's own
    -- meaning fixes it. `E4-CHECK-CE-015`.
    | .forkIn, [program, scope, options] => do
      let p ← readEff sig spell n program
      let s ← readTerm n scope
      let o ← readForkOptions true options
      .ok (.withFiber (.forkIn p o s))
    | .forkScoped, [program, options] => do
      let p ← readEff sig spell n program
      let o ← readForkOptions true options
      .ok (.withFiber (.forkScoped p o))
    | .withFiber, args => readRunIn n args
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
    | .provide, [body, layer] => do
      let b ← readEff sig spell n body
      let l ← readLayer sig spell layer
      .ok (.provideLayer l false b)
    | .provide, [body, layer, .object [(field, .bool true)]] =>
      if field = "local" then do
        let b ← readEff sig spell n body
        let l ← readLayer sig spell layer
        .ok (.provideLayer l true b)
      else .error (.shape "provide options")
    | .service, [key] => (readKey sig key).map .service
    | .provideService, [body, key, value] => do
      let b ← readEff sig spell n body
      let k ← readKey sig key
      let v ← readTerm n value
      .ok (.provideService k v b)
    | .whileLoop, _ => .error (.unknownHead Head.whileLoop.spelling)
    | .fiberId, _ => .error (.unknownHead Head.fiberId.spelling)
    | .causeFail, _ => .error (.unknownHead Head.causeFail.spelling)
    | .causeDie, _ => .error (.unknownHead Head.causeDie.spelling)
    | .causeInterrupt, _ => .error (.unknownHead Head.causeInterrupt.spelling)
    | .causeCombine, _ => .error (.unknownHead Head.causeCombine.spelling)
    | .undefined, _ => .error (.unknownHead Head.undefined.spelling)
    -- A layer or key does not stand alone in program position.
    | .contextService, _ => .error (.unknownHead Head.contextService.spelling)
    | .layerSucceed, _ => .error (.unknownHead Head.layerSucceed.spelling)
    | .layerEffect, _ => .error (.unknownHead Head.layerEffect.spelling)
    | .layerEffectDiscard, _ => .error (.unknownHead Head.layerEffectDiscard.spelling)
    | .layerProvide, _ => .error (.unknownHead Head.layerProvide.spelling)
    | .layerProvideMerge, _ => .error (.unknownHead Head.layerProvideMerge.spelling)
    | .layerMerge, _ => .error (.unknownHead Head.layerMerge.spelling)
    | .layerFresh, _ => .error (.unknownHead Head.layerFresh.spelling)
    | .layerOrDie, _ => .error (.unknownHead Head.layerOrDie.spelling)
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

  /-- The ten printed layer forms. Layer effect bodies have an empty environment. A bare
  identifier in layer position is a reference to the path its name carries
  (`LayerTerm.readRefName`, `Refs.lean`), admitted only when the name is exactly that path's
  spelling, so what is read is what `printLayer` prints. -/
  def readLayer (sig : Signature Op) (spell : String → List String → Option Op)
      (x : Expr) : Except ReadRefusal (LayerTerm Op) :=
    match x with
    | .ident s =>
      match LayerTerm.readRefName s with
      | some target =>
        if LayerTerm.refName target = s then .ok (.ref target) else .error (.shape "layer")
      | none => .error (.shape "layer")
    | .call (.ident "Layer.mergeAll") items => (readLayers sig spell items).map .mergeAll
    | .call (.ident "Layer.succeed") [key, value] => do
      let k ← readKey sig key
      let v ← readLiteral value
      .ok (.succeed k v)
    | .call (.ident "Layer.effect") [key, body] => do
      let k ← readKey sig key
      let b ← readEff sig spell 0 body
      .ok (.effect k b)
    | .call (.ident "Layer.effectDiscard") [body] =>
      (readEff sig spell 0 body).map .effectDiscard
    | .method self "pipe" [.call (.ident "Layer.provide") [that]] => do
      let s ← readLayer sig spell self
      let t ← readLayer sig spell that
      .ok (.provide s t)
    | .method self "pipe" [.call (.ident "Layer.provideMerge") [that]] => do
      let s ← readLayer sig spell self
      let t ← readLayer sig spell that
      .ok (.provideMerge s t)
    | .call (.ident "Layer.merge") [left, right] => do
      let l ← readLayer sig spell left
      let r ← readLayer sig spell right
      .ok (.merge l r)
    | .call (.ident "Layer.fresh") [inner] => (readLayer sig spell inner).map .fresh
    | .call (.ident "Layer.orDie") [inner] => (readLayer sig spell inner).map .orDie
    | _ => .error (.shape "layer")
  termination_by structural x

  /-- The layers of a `mergeAll`. -/
  def readLayers (sig : Signature Op) (spell : String → List String → Option Op)
      (items : List Expr) : Except ReadRefusal (LayerTerms Op) :=
    match items with
    | [] => .ok .nil
    | x :: rest => do
      let l ← readLayer sig spell x
      let ls ← readLayers sig spell rest
      .ok (.cons l ls)
  termination_by structural items
end

/-- A declaration block back to the program (the host rows slice): every
`const L_<path> = <layer>` read as a layer at the path its name carries and put back at that
path (`Refs.lean` `restoreAll`, ancestors first), the last declaration the main program.
The inverse of `printModule` on the blocks it prints; `shape "module"` on every other. -/
def readModule (sig : Signature Op) (spell : String → List String → Option Op)
    (decls : List TypeScript.Decl) : Except ReadRefusal (Eff Op) :=
  match decls.getLast?, decls.dropLast with
  | some (.const main), layerDecls => do
    let e ← readEff sig spell 0 main.value
    let ds ← layerDecls.mapM fun d =>
      match d with
      | .const c =>
        match LayerTerm.readRefName c.name with
        | some t =>
          if LayerTerm.refName t = c.name then do
            let l ← readLayer sig spell c.value
            .ok (t, l)
          else .error (.shape "module")
        | none => .error (.shape "module")
      | _ => .error (.shape "module")
    match e.restoreAll ds with
    | some e' => .ok e'
    | none => .error (.shape "module")
  | _, _ => .error (.shape "module")

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
    | .cons _ rest =>
      ((rest.names?).bind (spell atom)).isNone &&
        match rest with
        | .cons _ names => ((names.names?).bind (spell atom)).isNone
        | .nil => true
    | .nil => true

/-- What the printer keeps of a row's request: nothing on a value row or a `unit` request
(the request must then be exactly the unit literal), the term otherwise. A tuple-call
row keeps a `pair` application of scoped components or a scoped variable; a `pair` whose
printed components spell the saved-variable form `fst(a)`, `snd(a)` reads back as that
variable and is outside the image (source-repairs §18). -/
def tupleRequestReadable (n : Nat) (request : Term) : Bool :=
    match pairArgs? request with
    | some (x, y) => x.scoped n && y.scoped n && (savedVar? (printTerm x) (printTerm y)).isNone
    | none =>
      -- the requests whose printed form is one identifier: a binder, or `undefined`
      match request with
      | .var _ => request.scoped n
      | .lit .unit => true
      | _ => false

def requestReadable (row : Row) (n : Nat) (request : Term) : Bool :=
  match row.shape with
  | .value => decide (request = .lit .unit)
  | .call =>
    if row.request = Ty.unit then decide (request = .lit .unit) else request.scoped n
  | .tupleCall => tupleRequestReadable n request
  | .method =>
    match pairArgs? request with
    | some (receiver, args) =>
      receiver.scoped n &&
        if (methodArgsRow row).shape = .tupleCall then tupleRequestReadable n args
        else if (methodArgsRow row).request = Ty.unit then decide (args = .lit .unit)
        else args.scoped n
    | none => false

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
      decide ((sig.rowOf op).kind ≠ .async) && sig.dom op && requestReadable (sig.rowOf op) n request
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
      decide ((sig.rowOf register).kind = .async) && sig.dom register && requestReadable (sig.rowOf register) n request
    | .awaitFiber fiber _ => fiber.scoped n
    | .withFiber action => readableAction sig spell n action
    | .scoped body => readable sig spell n body
    | .acquireRelease acquire release =>
      readable sig spell n acquire && readable sig spell (n + 2) release
    | .choose _ _ _ => false
    | .provideLayer layer _ body => readableLayer sig spell layer && readable sig spell n body
    | .service _ => true
    | .provideService _ value body => value.scoped n && readable sig spell n body

  /-- The layer's closed effects must retain their printed form. A reference is readable
  exactly when its identifier decodes back to its path (`LayerTerm.readRefName` after
  `refName`), which is the executed fact the reader's identifier arm relies on; the `const`
  that binds the identifier is a declaration block's (`printModule`/`readModule`). -/
  def readableLayer (sig : Signature Op) (spell : String → List String → Option Op) :
      LayerTerm Op → Bool
    | .succeed _ _ => true
    | .effect _ body | .effectDiscard body => readable sig spell 0 body
    | .provide self that | .provideMerge self that | .merge self that =>
      readableLayer sig spell self && readableLayer sig spell that
    | .fresh inner | .orDie inner => readableLayer sig spell inner
    | .ref target =>
      decide (LayerTerm.readRefName (LayerTerm.refName target) = some target)
    | .mergeAll layers => readableLayers sig spell layers

  /-- Every layer of a `mergeAll`. -/
  def readableLayers (sig : Signature Op) (spell : String → List String → Option Op) :
      LayerTerms Op → Bool
    | .nil => true
    | .cons head tail => readableLayer sig spell head && readableLayers sig spell tail


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
    -- rc.112's `forkIn`/`forkScoped` fork a daemon (`internal/effect.ts:5366`, `:5406`), so
    -- the readable image is the one the export means: `daemon = true`. A non-daemon
    -- `forkIn` action has no rc.112 spelling and stays outside the readable domain
    -- (`E4-CHECK-CE-015`).
    | .forkIn program options scope =>
      readable sig spell n program && options.daemon && scope.scoped n
    | .forkScoped program options => readable sig spell n program && options.daemon
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
  spell_row : ∀ op, sig.dom op = true →
    spell (sig.rowOf op).spelling (sig.rowOf op).trailing = some op
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

theorem readKey_exact {Op : Type} {sig : Signature Op} {x : Expr} {key : ServiceKey}
    (h : readKey sig x = .ok key) : printKey sig key = x := by
  unfold readKey at h
  split at h
  · dsimp only at h
    split at h
    · rename_i heq
      cases h
      rw [printKey, heq.2.1]
      change Expr.call (.ident "Context.Service") [.str (keyText _)] = _
      rw [← heq.2.2, heq.1]
    · cases h
  · dsimp only at h
    split at h
    · rename_i ty hty
      split at h
      · rename_i heq
        cases h
        rw [printKey, hty]
        change Expr.call (.generic (.ident "Context.Service") [ty.render]) [.str (keyText _)] = _
        rw [← heq.2.2, heq.1, heq.2.1]
      · cases h
    · cases h
  · cases h

private theorem repr_no_separator (n : Nat) :
    ∀ b ∈ (Nat.repr n).toByteArray.data.toList, (b != (95 : UInt8)) = true := by
  rw [Nat.repr, String.toByteArray_ofList, List.utf8Encode, List.toList_data_toByteArray,
    Nat.toDigits]
  suffices h : ∀ fuel n ds, n < fuel →
      (∀ c ∈ ds, ∀ b ∈ String.utf8EncodeChar c, (b != (95 : UInt8)) = true) →
      ∀ b ∈ (Nat.toDigitsCore 10 fuel n ds).flatMap String.utf8EncodeChar,
        (b != (95 : UInt8)) = true from h (n + 1) n [] (Nat.lt_succ_self n) (by simp)
  intro fuel
  induction fuel with
  | zero => intro n ds h; omega
  | succ fuel ih =>
    intro n ds hn hds
    have hm : n % 10 < 10 := Nat.mod_lt _ (by decide)
    have hd : ∀ b ∈ String.utf8EncodeChar (Nat.digitChar (n % 10)),
        (b != (95 : UInt8)) = true := by
      rw [utf8_digitChar _ hm]
      have : ∀ m, m < 10 → ((UInt8.ofNat (48 + m)) != (95 : UInt8)) = true := by decide
      simp only [List.mem_singleton]
      intro b hb
      subst b
      exact this _ hm
    have hcons : ∀ c ∈ Nat.digitChar (n % 10) :: ds,
        ∀ b ∈ String.utf8EncodeChar c, (b != (95 : UInt8)) = true := by
      intro c hc
      cases List.mem_cons.mp hc with
      | inl h => subst c; exact hd
      | inr h => exact hds c h
    rw [Nat.toDigitsCore]
    split
    · intro b hb
      obtain ⟨c, hc, hb⟩ := List.mem_flatMap.mp hb
      exact hcons c hc b hb
    · exact ih (n / 10) _ (by omega) hcons

private theorem split_separator (xs ys : List UInt8)
    (h : ∀ b ∈ xs, (b != (95 : UInt8)) = true) :
    (xs ++ 95 :: ys).takeWhile (· != 95) = xs ∧
      (xs ++ 95 :: ys).dropWhile (· != 95) = 95 :: ys := by
  induction xs with
  | nil => simp
  | cons b bs ih =>
    have hb := h b (List.mem_cons_self)
    have hbs : ∀ c ∈ bs, (c != (95 : UInt8)) = true :=
      fun c hc => h c (List.mem_cons_of_mem b hc)
    simp only [List.cons_append, List.takeWhile_cons, List.dropWhile_cons,
      hb, if_true, (ih hbs).1, (ih hbs).2, and_self]

theorem keyFromText_print (name service : Nat) :
    keyFromText ("k" ++ toString name ++ "_" ++ toString service) = ⟨⟨name⟩, ⟨service⟩⟩ := by
  have hk : "k".toByteArray.data.toList = [107] := by decide
  have hs : "_".toByteArray.data.toList = [95] := by decide
  simp only [keyFromText, String.toByteArray_append, ByteArray.data_append,
    Array.toList_append, hk, hs, List.append_assoc, List.cons_append,
    List.nil_append, List.drop_succ_cons, List.drop_zero]
  change ServiceKey.mk
    ⟨decodeBytes (((Nat.repr name).toByteArray.data.toList ++
      95 :: (Nat.repr service).toByteArray.data.toList).takeWhile (· != 95))⟩
    ⟨decodeBytes ((((Nat.repr name).toByteArray.data.toList ++
      95 :: (Nat.repr service).toByteArray.data.toList).dropWhile (· != 95)).drop 1)⟩ = _
  rw [(split_separator _ _ (repr_no_separator name)).1,
    (split_separator _ _ (repr_no_separator name)).2]
  simp only [List.drop_succ_cons, List.drop_zero, decodeBytes_repr]


theorem readKey_printKey {Op : Type} (sig : Signature Op) (key : ServiceKey) :
    readKey sig (printKey sig key) = .ok key := by
  obtain ⟨⟨name⟩, ⟨service⟩⟩ := key
  cases ht : sig.serviceTy ⟨⟨name⟩, ⟨service⟩⟩ <;>
    simp only [printKey, ht, readKey, keyFromText_print, keyText, and_self, if_true]


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

theorem readLiteral_print (value : Lit) : readLiteral (printLit value) = .ok value := by
  unfold readLiteral
  have ht := readTerm_printTerm (n := 0) (.lit value) rfl
  change readTerm 0 (printLit value) = .ok (.lit value) at ht
  rw [ht]
  rfl

theorem readLiteral_exact {x : Expr} {value : Lit} (h : readLiteral x = .ok value) :
    printLit value = x := by
  simp only [readLiteral, bind_eq_ok] at h
  obtain ⟨term, ht, h⟩ := h
  cases term with
  | var _ | app _ _ => cases h
  | lit v =>
    cases h
    exact readTerm_exact x ht

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
    · simp at hp
    · split at hp <;> unfold printMethod at hp <;> split at hp <;> cases hp
  case callback op r =>
    simp only [print, printRow, Except.ok.injEq] at hp
    split at hp
    · simp at hp
    · split at hp <;> simp at hp
    · simp at hp
    · split at hp <;> unfold printMethod at hp <;> split at hp <;> cases hp
  case awaitFiber f m => cases m <;> simp [print] at hp
  case withFiber act =>
    cases act
    case interruptAll targets who => cases who <;> simp [print, printAction] at hp
    all_goals simp [print, printAction, bind_eq_ok] at hp
  all_goals simp [print, bind_eq_ok] at hp

theorem readRowCall_none {sig : Signature Op} {spell : String → List String → Option Op} {n : Nat}
    {atom : String} {args : Terms} (h : noRow spell atom args = true) :
    readRowCall sig spell n atom [] (printTerms args) = none := by
  cases args with
  | nil =>
    simp only [noRow, Bool.and_true, Option.isNone_iff_eq_none] at h
    unfold readRowCall; rw [idents?_printTerms, h]; simp [printTerms]
  | cons t rest =>
    cases rest with
    | nil =>
      simp only [noRow, Bool.and_eq_true, Bool.and_true, Option.isNone_iff_eq_none] at h
      unfold readRowCall
      rw [idents?_printTerms (.cons t .nil), h.1]
      simp only [printTerms]
      rw [show idents? ([] : List Expr) = Terms.nil.names? from rfl, h.2]
    | cons u names =>
      simp only [noRow, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
      unfold readRowCall
      rw [idents?_printTerms (.cons t (.cons u names)), h.1]
      rw [printTerms.eq_2]
      dsimp only
      rw [idents?_printTerms (.cons u names), h.2.1]
      rw [printTerms.eq_2]
      dsimp only
      rw [idents?_printTerms names, h.2.2]

theorem readRowCall_unit {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} (op : Op) (hd : sig.dom op = true)
    (hshape : (sig.rowOf op).shape = .call) (hreq : (sig.rowOf op).request = Ty.unit) :
    readRowCall sig spell n (sig.rowOf op).spelling (sig.rowOf op).typeArgs
        ((sig.rowOf op).trailing.map Expr.ident)
      = some (.ok (rowAnswer (sig.rowOf op) op (.lit .unit))) := by
  unfold readRowCall
  rw [idents?_map, Option.bind_some, hl.spell_row op hd]
  simp [hshape, hreq]

theorem readRowCall_request {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} (op : Op) (hd : sig.dom op = true) (r : Term)
    (hshape : (sig.rowOf op).shape = .call) (hreq : (sig.rowOf op).request ≠ Ty.unit) :
    readRowCall sig spell n (sig.rowOf op).spelling (sig.rowOf op).typeArgs
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
  rw [idents?_map, Option.bind_some, hl.spell_row op hd]
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

/-- A printed term is an identifier only as a binder or as `undefined`, never as a trailing
name of any row. -/
theorem printTerm_ident_not_trailing {sig : Signature Op}
    {spell : String → List String → Option Op} (hl : LawfulSpelling sig spell) (r : Term)
    (op : Op) (v : String) (h : printTerm r = .ident v) : v ∉ (sig.rowOf op).trailing := by
  cases r with
  | var i =>
    simp only [printTerm, Expr.ident.injEq] at h
    subst h
    exact hl.trailing_ne_name op i
  | lit value =>
    cases value with
    | unit =>
      simp only [printTerm, printLit, Expr.ident.injEq] at h
      subst h
      exact hl.trailing_ne_undefined op
    | nat _ | bool _ | str _ => simp [printTerm, printLit] at h
  | app _ _ => simp [printTerm] at h

/-- The tuple reading of a row: two arguments that are not trailing names, then the row's
trailing names, read through `readTupleArgs`. -/
theorem readRowCall_tuple {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} (op : Op) (hd : sig.dom op = true) (x y : Expr)
    (hshape : (sig.rowOf op).shape = .tupleCall)
    (hx : ∀ op' v, x = .ident v → v ∉ (sig.rowOf op').trailing)
    (hy : ∀ op' v, y = .ident v → v ∉ (sig.rowOf op').trailing) :
    readRowCall sig spell n (sig.rowOf op).spelling (sig.rowOf op).typeArgs
        (x :: y :: (sig.rowOf op).trailing.map Expr.ident)
      = some ((readTupleArgs n x y).map (rowAnswer (sig.rowOf op) op)) := by
  have key : ∀ (names : List String) (v : String), (∀ op', v ∉ (sig.rowOf op').trailing) →
      spell (sig.rowOf op).spelling (v :: names) = none := by
    intro names v hv
    cases hsp : spell (sig.rowOf op).spelling (v :: names) with
    | none => rfl
    | some op' =>
      exfalso
      obtain ⟨_, htr⟩ := hl.row_of_spell _ _ _ hsp
      exact hv op' (htr ▸ List.mem_cons_self)
  have hA : ((idents? (x :: y :: (sig.rowOf op).trailing.map Expr.ident)).bind
      (spell (sig.rowOf op).spelling)) = none := by
    cases x
    case ident v =>
      cases y
      case ident w =>
        simp only [idents?, idents?_map, Option.map_some, Option.bind_some]
        exact key _ v (fun op' => hx op' v rfl)
      all_goals simp [idents?]
    all_goals simp [idents?]
  have hB : ((idents? (y :: (sig.rowOf op).trailing.map Expr.ident)).bind
      (spell (sig.rowOf op).spelling)) = none := by
    cases y
    case ident w =>
      simp only [idents?, idents?_map, Option.map_some, Option.bind_some]
      exact key _ w (fun op' => hy op' w rfl)
    all_goals simp [idents?]
  unfold readRowCall
  rw [hA]
  dsimp only
  rw [hB]
  dsimp only
  rw [idents?_map, Option.bind_some, hl.spell_row op hd]
  simp [hshape]

/-- The tuple request round trip is shared by free calls and receiver methods. -/
theorem readRowCall_printTupleArgs {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} (op : Op) (hd : sig.dom op = true)
    (hshape : (sig.rowOf op).shape = .tupleCall) (r : Term)
    (h : tupleRequestReadable n r = true) :
    readRowCall sig spell n (sig.rowOf op).spelling (sig.rowOf op).typeArgs
      (printTupleArgs r ++ (sig.rowOf op).trailing.map Expr.ident) =
      some (.ok (rowAnswer (sig.rowOf op) op r)) := by
  simp only [tupleRequestReadable] at h
  rcases hpa : pairArgs? r with _ | ⟨x, y⟩
  · simp only [hpa] at h
    cases r with
    | var i =>
      simp only at h
      simp only [printTupleArgs, hpa, printTerm, List.cons_append, List.nil_append]
      rw [readRowCall_tuple hl op hd _ _ hshape
        (fun _ _ hx => by cases hx) (fun _ _ hy => by cases hy)]
      have hv : readTerm n (.ident (Var.name i)) = .ok (.var i) :=
        readTerm_printTerm (.var i) h
      simp [readTupleArgs, savedVar?, hv]
    | lit value =>
      cases value with
      | unit =>
        simp only [printTupleArgs, hpa, printTerm, printLit, List.cons_append, List.nil_append]
        rw [readRowCall_tuple hl op hd _ _ hshape
          (fun _ _ hx => by cases hx) (fun _ _ hy => by cases hy)]
        have hv : readTerm n (.ident "undefined") = .ok (.lit .unit) :=
          readTerm_printTerm (.lit .unit) rfl
        simp [readTupleArgs, savedVar?, hv]
      | nat _ | bool _ | str _ => simp at h
    | app _ _ => simp at h
  · simp only [hpa, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
    obtain ⟨⟨hx, hy⟩, hsv⟩ := h
    obtain rfl := pairArgs?_some hpa
    simp only [printTupleArgs, hpa, List.cons_append, List.nil_append]
    rw [readRowCall_tuple hl op hd _ _ hshape
      (fun op' v hv => printTerm_ident_not_trailing hl x op' v hv)
      (fun op' v hv => printTerm_ident_not_trailing hl y op' v hv)]
    simp [readTupleArgs, hsv, readTerm_printTerm x hx, readTerm_printTerm y hy]

/-- Method projection keeps the same row identities and name hygiene. -/
theorem methodLawful {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) : LawfulSpelling (methodSignature sig) spell where
  spell_row := hl.spell_row
  row_of_spell := hl.row_of_spell
  value_trailing := by
    intro op hv
    have hs := methodArgsRow_shape (sig.rowOf op)
    change (methodArgsRow (sig.rowOf op)).shape = .value at hv
    rcases hs with hs | hs <;> simp [hs] at hv
  spelling_ne_name := hl.spelling_ne_name
  spelling_not_reserved := hl.spelling_not_reserved
  trailing_ne_name := hl.trailing_ne_name
  trailing_ne_undefined := hl.trailing_ne_undefined

theorem readRowCall_methodArgs {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} (op : Op) (hd : sig.dom op = true) (args : Term)
    (h : (if (methodArgsRow (sig.rowOf op)).shape = .tupleCall then tupleRequestReadable n args
      else if (methodArgsRow (sig.rowOf op)).request = Ty.unit then decide (args = .lit .unit)
      else args.scoped n) = true) :
    readRowCall (methodSignature sig) spell n (sig.rowOf op).spelling (sig.rowOf op).typeArgs
      (printMethodArgs (sig.rowOf op) args) = some (.ok (rowAnswer (sig.rowOf op) op args)) := by
  have hm := methodLawful hl
  rcases methodArgsRow_shape (sig.rowOf op) with hs | hs
  · simp only [hs, reduceCtorEq, if_false] at h
    by_cases ht : (methodArgsRow (sig.rowOf op)).request = Ty.unit
    · simp only [ht, if_true, decide_eq_true_eq] at h
      subst args
      simp only [printMethodArgs, hs, reduceCtorEq, if_false, ht, if_true]
      have result := readRowCall_unit (n := n) hm op hd hs ht
      dsimp +instances only [methodSignature, methodArgsRow, rowAnswer] at result ⊢
      exact result
    · simp only [ht, if_false] at h
      simp only [printMethodArgs, hs, reduceCtorEq, if_false, ht]
      have result := readRowCall_request (n := n) hm op hd args hs ht
      rw [readTerm_printTerm args h] at result
      simp only [map_ok] at result
      dsimp +instances only [methodSignature, methodArgsRow, rowAnswer] at result ⊢
      exact result
  · simp only [hs, if_true] at h
    simp only [printMethodArgs, hs, if_true]
    have result := readRowCall_printTupleArgs (n := n) hm op hd hs args h
    dsimp +instances only [methodSignature, methodArgsRow, rowAnswer] at result ⊢
    exact result

theorem readRowMethod_print {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} (op : Op) (hd : sig.dom op = true)
    (receiver args : Term) (hs : (sig.rowOf op).shape = .method)
    (hr : receiver.scoped n = true)
    (ha : (if (methodArgsRow (sig.rowOf op)).shape = .tupleCall then tupleRequestReadable n args
      else if (methodArgsRow (sig.rowOf op)).request = Ty.unit then decide (args = .lit .unit)
      else args.scoped n) = true) :
    readRowMethod sig spell n (printTerm receiver) (sig.rowOf op).spelling (sig.rowOf op).typeArgs
      (printMethodArgs (sig.rowOf op) args) =
      .ok (rowAnswer (sig.rowOf op) op (.app "pair" (.cons receiver (.cons args .nil)))) := by
  simp only [readRowMethod, readTerm_printTerm receiver hr, ok_bind,
    readRowCall_methodArgs hl op hd args ha, Option.getD_some]
  unfold rowAnswer
  split <;> simp [addReceiver, hs, rowAnswer, *]

/-- The printed form of a row answer is independent of the synchronous/asynchronous choice. -/
theorem print_rowAnswer {sig : Signature Op} {n : Nat} (op : Op) (r : Term) :
    print sig n (rowAnswer (sig.rowOf op) op r) = .ok (printRow (sig.rowOf op) r) := by
  unfold rowAnswer
  split <;> rfl

/-- The reader's two call arms agree on a row's printed head: with no declared type
arguments it is a plain `spelling(...)` call, and with them a `spelling<T…>(...)` call; both
route to `readRowCall` at the row's own type arguments (`E4-CHECK-CE-013`). -/
theorem readEff_printRowHead {sig : Signature Op} {spell : String → List String → Option Op}
    {n : Nat} (op : Op) (args : List Expr) (answer : Except ReadRefusal (Eff Op))
    (hhead : headOf (sig.rowOf op).spelling = none)
    (hrow : readRowCall sig spell n (sig.rowOf op).spelling (sig.rowOf op).typeArgs args
      = some answer) :
    readEff sig spell n (.call (printRowHead (sig.rowOf op)) args) = answer := by
  unfold printRowHead
  cases htargs : (sig.rowOf op).typeArgs with
  | nil =>
    rw [htargs] at hrow
    unfold readEff
    rw [hhead]
    dsimp only
    rw [hrow]
  | cons a rest =>
    rw [htargs] at hrow
    unfold readEff
    rw [hrow]

/-- A row prints and reads back to `rowAnswer`. -/
theorem read_printRow {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} (op : Op) (hd : sig.dom op = true) (r : Term)
    (h : requestReadable (sig.rowOf op) n r = true) :
    readEff sig spell n (printRow (sig.rowOf op) r) = .ok (rowAnswer (sig.rowOf op) op r) := by
  have hname : ∀ i, Var.name i ≠ (sig.rowOf op).spelling := fun i => (hl.spelling_ne_name op i).symm
  have hhead : headOf (sig.rowOf op).spelling = none := headOf_none (hl.spelling_not_reserved op)
  cases hshape : (sig.rowOf op).shape with
  | value =>
    rw [readable_row_value hshape h]
    have htr := hl.value_trailing op hshape
    have hsp := hl.spell_row op hd
    rw [htr] at hsp
    simp only [printRow, hshape]
    unfold readEff
    simp [Var.read_none hname, hhead, readRowValue, hsp, hshape]
  | call =>
    by_cases hreq : (sig.rowOf op).request = Ty.unit
    · rw [readable_row_unit hshape hreq h]
      simp only [printRow, hshape, hreq, if_true]
      rw [readEff_printRowHead op _ _ hhead (readRowCall_unit hl op hd hshape hreq)]
    · simp only [printRow, hshape, hreq, if_false]
      rw [readEff_printRowHead op _ _ hhead (readRowCall_request hl op hd r hshape hreq)]
      simp [readTerm_printTerm r (readable_row_request hshape hreq h)]
  | tupleCall =>
    simp only [requestReadable, hshape] at h
    simp only [printRow, hshape]
    exact readEff_printRowHead op _ _ hhead (readRowCall_printTupleArgs hl op hd hshape r h)
  | method =>
    simp only [requestReadable, hshape] at h
    cases hp : pairArgs? r with
    | none => simp [hp] at h
    | some parts =>
      obtain ⟨receiver, args⟩ := parts
      simp only [hp, Bool.and_eq_true_iff] at h
      obtain ⟨hr, ha⟩ := h
      have hm := readRowMethod_print hl op hd receiver args hshape hr ha
      obtain rfl := pairArgs?_some hp
      cases ht : (sig.rowOf op).typeArgs with
      | nil =>
        simp only [ht] at hm
        simp [printRow, hshape, pairArgs?, printMethod, ht, readEff, readMethod, hm,
          print_rowAnswer]
      | cons t ts =>
        simp only [ht] at hm
        simp [printRow, hshape, pairArgs?, printMethod, ht, readEff, readMethod, hm,
          print_rowAnswer]

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
    obtain ⟨⟨hkind, hd⟩, hreq⟩ := hr
    simp only [print, Except.ok.injEq] at hp; subst hp
    rw [read_printRow hl op hd r hreq]
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
    obtain ⟨⟨hkind, hd⟩, hreq⟩ := hr
    simp only [print, Except.ok.injEq] at hp; subst hp
    rw [read_printRow hl op hd r hreq]
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
  | .provideLayer layer isLocal body, hr, hp => by
    simp only [readable, Bool.and_eq_true] at hr
    simp only [print, bind_eq_ok] at hp
    obtain ⟨b, hb, l, hlayer, hx⟩ := hp
    simp only [Except.ok.injEq] at hx; subst hx
    cases isLocal <;> unfold readEff readHead <;>
      simp [headOf_lit .provide "Effect.provide" rfl,
        read_print hl body hr.2 hb, read_print_layer hl layer hr.1 hlayer]
  | .service key, _, hp => by
    simp only [print, Except.ok.injEq] at hp; subst hp
    unfold readEff readHead
    simp [headOf_lit .service "Effect.service" rfl, readKey_printKey]
  | .provideService key value body, hr, hp => by
    simp only [readable, Bool.and_eq_true] at hr
    simp only [print, bind_eq_ok] at hp
    obtain ⟨b, hb, hx⟩ := hp
    simp only [Except.ok.injEq] at hx; subst hx
    unfold readEff readHead
    simp [headOf_lit .provideService "Effect.provideService" rfl,
      read_print hl body hr.2 hb, readKey_printKey, readTerm_printTerm value hr.1]
termination_by structural e

theorem read_print_layer {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) (layer : LayerTerm Op)
    (hr : readableLayer sig spell layer = true) {x : Expr}
    (hp : printLayer sig layer = .ok x) : readLayer sig spell x = .ok layer :=
  match layer, hr, hp with
  | .succeed key value, _, hp => by
    simp only [printLayer, Except.ok.injEq] at hp; subst hp
    simp [readLayer, readKey_printKey, readLiteral_print]
  | .effect key body, hr, hp => by
    simp only [readableLayer] at hr
    simp only [printLayer, bind_eq_ok] at hp
    obtain ⟨b, hb, hx⟩ := hp
    simp only [Except.ok.injEq] at hx; subst hx
    simp [readLayer, readKey_printKey, read_print hl body hr hb]
  | .effectDiscard body, hr, hp => by
    simp only [readableLayer] at hr
    simp only [printLayer, bind_eq_ok] at hp
    obtain ⟨b, hb, hx⟩ := hp
    simp only [Except.ok.injEq] at hx; subst hx
    simp [readLayer, read_print hl body hr hb]
  | .provide self that, hr, hp | .provideMerge self that, hr, hp | .merge self that, hr, hp => by
    simp only [readableLayer, Bool.and_eq_true] at hr
    simp only [printLayer, bind_eq_ok] at hp
    obtain ⟨a, ha, b, hb, hx⟩ := hp
    simp only [Except.ok.injEq] at hx; subst hx
    simp [readLayer, read_print_layer hl self hr.1 ha, read_print_layer hl that hr.2 hb]
  | .fresh inner, hr, hp | .orDie inner, hr, hp => by
    simp only [readableLayer] at hr
    simp only [printLayer, bind_eq_ok] at hp
    obtain ⟨i, hi, hx⟩ := hp
    simp only [Except.ok.injEq] at hx; subst hx
    simp [readLayer, read_print_layer hl inner hr hi]
  | .ref target, hr, hp => by
    simp only [readableLayer, decide_eq_true_eq] at hr
    simp only [printLayer, Except.ok.injEq] at hp; subst hp
    simp [readLayer, hr]
  | .mergeAll layers, hr, hp => by
    simp only [readableLayer] at hr
    simp only [printLayer, bind_eq_ok] at hp
    obtain ⟨items, hitems, hx⟩ := hp
    simp only [Except.ok.injEq] at hx; subst hx
    simp [readLayer, read_print_layers hl layers hr hitems]
termination_by structural layer

theorem read_print_layers {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) (layers : LayerTerms Op)
    (hr : readableLayers sig spell layers = true) {items : List Expr}
    (hp : printLayers sig layers = .ok items) : readLayers sig spell items = .ok layers :=
  match layers, hr, hp with
  | .nil, _, hp => by
    simp only [printLayers, Except.ok.injEq] at hp; subst hp; rfl
  | .cons head tail, hr, hp => by
    simp only [readableLayers, Bool.and_eq_true] at hr
    simp only [printLayers, bind_eq_ok] at hp
    obtain ⟨h, hh, t, ht, hx⟩ := hp
    simp only [Except.ok.injEq] at hx; subst hx
    simp [readLayers, read_print_layer hl head hr.1 hh, read_print_layers hl tail hr.2 ht]
termination_by structural layers

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
    simp [headOf_lit .withFiber "Effect.withFiber" rfl, readRunIn,
      readTerm_printTerm target hr.1, readTerm_printTerm scope hr.2]
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



/-- The tuple reading reconstructs its two arguments: a saved variable prints as its two
component reads, any other pair as the printed components. -/
theorem readTupleArgs_exact {n : Nat} {x y : Expr} {r : Term}
    (h : readTupleArgs n x y = .ok r) : printTupleArgs r = [x, y] := by
  unfold readTupleArgs at h
  split at h
  · rename_i v hv
    obtain ⟨rfl, rfl⟩ := savedVar?_some hv
    have hp := readTerm_exact (.ident v) h
    have hpa : pairArgs? r = none := by
      cases r with
      | var _ => rfl
      | lit _ => rfl
      | app _ _ => simp [printTerm] at hp
    simp [printTupleArgs, hpa, hp]
  · simp only [bind_eq_ok] at h
    obtain ⟨a, ha, b, hb, he⟩ := h
    cases he
    simp [printTupleArgs, pairArgs?, readTerm_exact x ha, readTerm_exact y hb]

/-- An accepted runIn adapter reconstructs both scoped terms and its exact block. -/
theorem readRunIn_exact {sig : Signature Op} {n : Nat} {args : List Expr} {e : Eff Op}
    (h : readRunIn n args = .ok e) :
    print sig n e = .ok (.call (.ident "Effect.withFiber") args) := by
  unfold readRunIn at h
  split at h
  · rename_i runIn target scope unit
    split at h
    · rename_i heads
      obtain ⟨rfl, rfl⟩ := heads
      simp only [bind_eq_ok] at h
      obtain ⟨t, ht, s, hs, he⟩ := h
      cases he
      simp [print, printAction, readTerm_exact target ht, readTerm_exact scope hs]
    · cases h
  · cases h


section ReadExact

/-- Closes an arm of a wildcard case of the reader: the arm's own negated-pattern hypothesis
is contradictory, or the arm is a refusal. -/
local macro "close_arm" h:ident : tactic => `(tactic| first
  | (exfalso; subst_vars; solve_by_elim [rfl])
  | cases $h:ident
  | (split at $h:ident <;> first | (exfalso; subst_vars; solve_by_elim [rfl]) | cases $h:ident))

/-- The call reader recovers the method's row identity and exactly its argument syntax. -/
theorem readRowCall_method_parts {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} {s : String} {ta : List String} {args : List Expr}
    {e : Eff Op}
    (h : readRowCall (methodSignature sig) spell n s ta args = some (.ok e)) :
    ∃ op r, e = rowAnswer (sig.rowOf op) op r ∧ (sig.rowOf op).spelling = s ∧
      (sig.rowOf op).typeArgs = ta ∧ printMethodArgs (sig.rowOf op) r = args := by
  unfold readRowCall at h
  split at h
  · rename_i op hA
    simp only [Option.some.injEq] at h
    split at h
    · rename_i hc
      dsimp only [methodSignature] at hc
      cases h
      obtain ⟨names, hn, hsp⟩ := Option.bind_eq_some_iff.mp hA
      obtain ⟨hs, htr⟩ := hl.row_of_spell _ _ _ hsp
      refine ⟨op, .lit .unit, rfl, hs, hc.2.2, ?_⟩
      rw [idents?_exact hn]
      simp only [printMethodArgs, hc.1, reduceCtorEq, if_false, hc.2.1, if_true, htr]
    · cases h
  · split at h
    · split at h
      · simp only [Option.some.injEq] at h
        split at h
        · rename_i hc
          dsimp only [methodSignature] at hc
          obtain ⟨r, hr, rfl⟩ := map_eq_ok.mp h
          obtain ⟨names, hn, hsp⟩ :=
            Option.bind_eq_some_iff.mp ‹(idents? _).bind (spell s) = some _›
          obtain ⟨hs, htr⟩ := hl.row_of_spell _ _ _ hsp
          refine ⟨_, r, rfl, hs, hc.2.2, ?_⟩
          rw [idents?_exact hn]
          simp only [printMethodArgs, hc.1, reduceCtorEq, if_false, hc.2.1, htr,
            readTerm_exact _ hr]
        · cases h
      · split at h
        · split at h
          · simp only [Option.some.injEq] at h
            split at h
            · rename_i hc
              dsimp only [methodSignature] at hc
              obtain ⟨r, hr, rfl⟩ := map_eq_ok.mp h
              obtain ⟨names, hn, hsp⟩ :=
                Option.bind_eq_some_iff.mp ‹(idents? _).bind (spell s) = some _›
              obtain ⟨hs, htr⟩ := hl.row_of_spell _ _ _ hsp
              refine ⟨_, r, rfl, hs, hc.2, ?_⟩
              rw [idents?_exact hn]
              simp only [printMethodArgs, hc.1, if_true, htr, readTupleArgs_exact hr,
                List.cons_append, List.nil_append]
            · cases h
          · cases h
        · cases h
    · cases h

theorem addReceiver_rowAnswer (sig : Signature Op) (receiver : Term) (op : Op) (args : Term) :
    addReceiver sig receiver (rowAnswer (sig.rowOf op) op args) =
      if (sig.rowOf op).shape = .method then
        .ok (rowAnswer (sig.rowOf op) op (.app "pair" (.cons receiver (.cons args .nil))))
      else .error (.shape "method row") := by
  unfold rowAnswer
  split <;> simp [addReceiver, rowAnswer, *]

theorem readRowMethod_exact {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} {receiver : Expr} {s : String}
    {ta : List String} {args : List Expr} {e : Eff Op}
    (h : readRowMethod sig spell n receiver s ta args = .ok e) :
    print sig n e = .ok (match ta with
      | [] => .method receiver s args
      | ts => .call (.generic (.member receiver s) ts) args) := by
  unfold readRowMethod at h
  obtain ⟨recv, hr, h⟩ := bind_eq_ok.mp h
  obtain ⟨body, hb, h⟩ := bind_eq_ok.mp h
  cases hc : readRowCall (methodSignature sig) spell n s ta args with
  | none => simp [hc] at hb
  | some answer =>
    simp only [hc, Option.getD_some] at hb
    rw [hb] at hc
    obtain ⟨op, request, rfl, hs, ht, ha⟩ := readRowCall_method_parts hl hc
    rw [addReceiver_rowAnswer] at h
    split at h
    · rename_i hshape
      cases h
      simp [print_rowAnswer, printRow, hshape, pairArgs?, printMethod,
        hs, ht, ha, readTerm_exact _ hr]
      cases ta <;> rfl
    · cases h

theorem readMethod_exact {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} {x : Expr} {e : Eff Op}
    (h : readMethod sig spell n x = .ok e) : print sig n e = .ok x := by
  unfold readMethod at h
  split at h
  · exact readRowMethod_exact hl h
  · exact readRowMethod_exact hl h
  · cases h

/-- The exactness of the reader, over the six mutual readers at once, by the functional
induction principle Lean generates for `readEff`: one case per arm of the reader. -/
theorem read_exact_all {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) (n : Nat) (x : Expr) :
    ∀ e, readEff sig spell n x = .ok e → print sig n e = .ok x := by
  apply readEff.induct sig spell
    (motive_1 := fun n x => ∀ e, readEff sig spell n x = .ok e → print sig n e = .ok x)
    (motive_2 := fun n h args => ∀ e, readHead sig spell n h args = .ok e →
      print sig n e = .ok (.call (.ident h.spelling) args))
    (motive_3 := fun x => ∀ layer, readLayer sig spell x = .ok layer →
      printLayer sig layer = .ok x)
    (motive_4 := fun items => ∀ ls, readLayers sig spell items = .ok ls →
      printLayers sig ls = .ok items)
    (motive_5 := fun n items => ∀ es, readEffs sig spell n items = .ok es →
      printEffs sig n es = .ok items)
    (motive_6 := fun n stmts => ∀ ss, readStmts sig spell n stmts = .ok ss →
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
        simp [printRow, printRowHead, hc.1, hc.2.1, hc.2.2, hs, htr]
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
            simp [printRow, printRowHead, hc.1, hc.2.1, hc.2.2, hs, htr, readTerm_exact _ hr]
          · cases hrow
        · split at hrow
          · split at hrow
            · simp only [Option.some.injEq] at hrow
              split at hrow
              · rename_i hshape
                simp only [map_eq_ok] at hrow
                obtain ⟨r, hr, he⟩ := hrow
                subst he
                obtain ⟨names, hnames, hsp⟩ :=
                  Option.bind_eq_some_iff.mp ‹(idents? _).bind (spell atom) = some _›
                obtain ⟨hs, htr⟩ := hl.row_of_spell _ _ _ hsp
                rw [print_rowAnswer, idents?_exact hnames]
                simp [printRow, printRowHead, hshape.1, hshape.2, hs, htr, readTupleArgs_exact hr]
              · cases hrow
            · cases hrow
          · cases hrow
      · cases hrow
  case case12 =>
    intro n atom args hh hrow e h
    unfold readEff at h; simp only [hh, hrow, map_eq_ok] at h
    obtain ⟨ts, hts, rfl⟩ := h
    simp [print, printTerm, readTerms_exact args hts]
  -- the generic-head call arm: a row call carrying the row's own type arguments
  -- (`E4-CHECK-CE-013`). It prints back through `printRowHead`'s non-empty branch.
  case case13 =>
    intro n atom ta tas args answer hrow e h
    unfold readEff at h; simp only [hrow] at h
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
        simp [printRow, printRowHead, hc.1, hc.2.1, hc.2.2, hs, htr]
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
            simp [printRow, printRowHead, hc.1, hc.2.1, hc.2.2, hs, htr, readTerm_exact _ hr]
          · cases hrow
        · split at hrow
          · split at hrow
            · simp only [Option.some.injEq] at hrow
              split at hrow
              · rename_i hshape
                simp only [map_eq_ok] at hrow
                obtain ⟨r, hr, he⟩ := hrow
                subst he
                obtain ⟨names, hnames, hsp⟩ :=
                  Option.bind_eq_some_iff.mp ‹(idents? _).bind (spell atom) = some _›
                obtain ⟨hs, htr⟩ := hl.row_of_spell _ _ _ hsp
                rw [print_rowAnswer, idents?_exact hnames]
                simp [printRow, printRowHead, hshape.1, hshape.2, hs, htr, readTupleArgs_exact hr]
              · cases hrow
            · cases hrow
          · cases hrow
      · cases hrow
  -- no row of the table has this head with type arguments: the reader refuses, so there is
  -- nothing to print back
  case case14 =>
    intro n atom ta tas args hrow e h
    unfold readEff at h; simp only [hrow] at h
    cases h
  case case15 =>
    intros
    rename_i e h
    unfold readEff at h
    split at h <;> first | exact readMethod_exact hl h | close_arm h
  -- readHead
  case case29 =>
    intro n v e h
    unfold readHead at h; simp only [map_eq_ok] at h
    obtain ⟨t, ht, rfl⟩ := h
    simp [print, readTerm_exact v ht, Head.spelling]
  case case30 =>
    intro n v e h
    unfold readHead at h; simp only [map_eq_ok] at h
    obtain ⟨t, ht, rfl⟩ := h
    simp [print, readTerm_exact v ht, Head.spelling]
  case case31 =>
    intro n c e h
    unfold readHead at h; simp only [map_eq_ok] at h
    obtain ⟨t, ht, rfl⟩ := h
    simp [print, readCause_exact c ht, Head.spelling]
  case case32 =>
    intro n t e h
    unfold readHead at h; simp only [map_eq_ok] at h
    obtain ⟨t', ht, rfl⟩ := h
    simp [print, readTerm_exact t ht, Head.spelling]
  case case33 =>
    intro n t a b iha ihb e h
    unfold readHead at h; simp only [bind_eq_ok] at h
    obtain ⟨test, htest, x, hx, y, hy, he⟩ := h
    cases he
    simp [print, iha x hx, ihb y hy, readTerm_exact t htest, Head.spelling]
  case case34 =>
    intro n body hnc ih e h
    unfold readHead at h
    cases body <;> first
      | exact (hnc _ _ _ rfl).elim
      | (simp only [map_eq_ok] at h; obtain ⟨b', hb', rfl⟩ := h; simp [print, ih _ hb', Head.spelling])
  case case35 =>
    intro n cursor initial loop fw test fb body fs answer cursor' step hc ih e h
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hc
    unfold readHead at h
    simp only [and_self, if_true, bind_eq_ok] at h
    obtain ⟨i, hi, t, ht, s, hs, b, hb, he⟩ := h
    cases he
    simp [print, ih b hb, readTerm_exact initial hi, readTerm_exact test ht, readTerm_exact step hs,
      Head.spelling]
  case case36 =>
    intro n cursor initial loop fw test fb body fs answer cursor' step hc e h
    unfold readHead at h; simp [hc] at h
  case case37 =>
    intro n first rest ih1 ih2 e h
    unfold readHead at h
    simp only [if_true, bind_eq_ok] at h
    obtain ⟨f, hf, r, hr, he⟩ := h
    cases he
    simp [print, ih1 f hf, ih2 r hr, Head.spelling]
  case case38 =>
    intro n first x rest hx e h
    unfold readHead at h; simp [hx] at h
  case case39 =>
    intro n body ih e h
    unfold readHead at h; simp only [map_eq_ok] at h
    obtain ⟨ss, hss, rfl⟩ := h
    simp [print, ih ss hss, Head.spelling]
  case case40 =>
    intro n body handler ih1 ih2 e h
    unfold readHead at h
    simp only [if_true, bind_eq_ok] at h
    obtain ⟨b, hb, hd, hhd, he⟩ := h
    cases he
    simp [print, ih1 b hb, ih2 hd hhd, Head.spelling]
  case case41 =>
    intro n body x handler hx e h
    unfold readHead at h; simp [hx] at h
  case case42 =>
    intro n body ff x onCause fs y onValue hc ih1 ih2 ih3 e h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hc
    unfold readHead at h
    simp only [and_self, if_true, bind_eq_ok] at h
    obtain ⟨b, hb, v, hv, c, hc, he⟩ := h
    cases he
    simp [print, ih1 b hb, ih2 v hv, ih3 c hc, Head.spelling]
  case case43 =>
    intro n body ff x onCause fs y onValue hc e h
    unfold readHead at h; simp [hc] at h
  case case44 =>
    intro n body finalizer ih1 ih2 e h
    unfold readHead at h
    simp only [if_true, bind_eq_ok] at h
    obtain ⟨b, hb, f, hf, he⟩ := h
    cases he
    simp [print, ih1 b hb, ih2 f hf, Head.spelling]
  case case45 =>
    intro n body x finalizer hx e h
    unfold readHead at h; simp [hx] at h
  case case46 =>
    intro n body ih e h
    unfold readHead at h; simp only [map_eq_ok] at h
    obtain ⟨b, hb, rfl⟩ := h
    simp [print, ih b hb, Head.spelling]
  case case47 =>
    intro n body ih e h
    unfold readHead at h; simp only [map_eq_ok] at h
    obtain ⟨b, hb, rfl⟩ := h
    simp [print, ih b hb, Head.spelling]
  case case48 =>
    intro n body ih e h
    unfold readHead at h; simp only [map_eq_ok] at h
    obtain ⟨b, hb, rfl⟩ := h
    simp [print, ih b hb, Head.spelling]
  case case49 =>
    intro n k hk e h
    unfold readHead at h; simp only [hk, if_true] at h; cases h
    simp [print, Int.toNat_of_nonneg hk, Head.spelling]
  case case50 =>
    intro n k hk e h
    unfold readHead at h; simp [hk] at h
  case case51 =>
    intro n fiber e h
    unfold readHead at h; simp only [map_eq_ok] at h
    obtain ⟨t, ht, rfl⟩ := h
    simp [print, readTerm_exact fiber ht, Head.spelling]
  case case52 =>
    intro n fiber e h
    unfold readHead at h; simp only [map_eq_ok] at h
    obtain ⟨t, ht, rfl⟩ := h
    simp [print, readTerm_exact fiber ht, Head.spelling]
  case case53 =>
    intro n program options ih e h
    unfold readHead at h; simp only [bind_eq_ok] at h
    obtain ⟨p, hp, o, ho, he⟩ := h
    cases he
    obtain ⟨hpo, hd⟩ := readForkOptions_exact ho
    simp [print, printAction, ih p hp, hpo, hd, Head.spelling]
  case case54 =>
    intro n program options ih e h
    unfold readHead at h; simp only [bind_eq_ok] at h
    obtain ⟨p, hp, o, ho, he⟩ := h
    cases he
    obtain ⟨hpo, hd⟩ := readForkOptions_exact ho
    simp [print, printAction, ih p hp, hpo, hd, Head.spelling]
  case case55 =>
    intro n program scope options ih e h
    unfold readHead at h; simp only [bind_eq_ok] at h
    obtain ⟨p, hp, s, hs, o, ho, he⟩ := h
    cases he
    obtain ⟨hpo, _⟩ := readForkOptions_exact ho
    simp [print, printAction, ih p hp, readTerm_exact scope hs, hpo, Head.spelling]
  case case56 =>
    intro n program options ih e h
    unfold readHead at h; simp only [bind_eq_ok] at h
    obtain ⟨p, hp, o, ho, he⟩ := h
    cases he
    obtain ⟨hpo, _⟩ := readForkOptions_exact ho
    simp [print, printAction, ih p hp, hpo, Head.spelling]
  case case57 =>
    intro n args e h
    simp only [readHead] at h
    exact readRunIn_exact h
  case case58 =>
    intro n target e h
    unfold readHead at h; simp only [map_eq_ok] at h
    obtain ⟨t, ht, rfl⟩ := h
    simp [print, printAction, readTerm_exact target ht, Head.spelling]
  case case59 =>
    intro n targets e h
    unfold readHead at h; simp only [map_eq_ok] at h
    obtain ⟨t, ht, rfl⟩ := h
    simp [print, printAction, readTerm_exact targets ht, Head.spelling]
  case case60 =>
    intro n targets who e h
    unfold readHead at h; simp only [bind_eq_ok] at h
    obtain ⟨t, ht, w, hw, he⟩ := h
    cases he
    simp [print, printAction, readTerm_exact targets ht, readTerm_exact who hw, Head.spelling]
  case case61 =>
    intro n targets e h
    unfold readHead at h; simp only [map_eq_ok] at h
    obtain ⟨t, ht, rfl⟩ := h
    simp [print, printAction, readTerm_exact targets ht, Head.spelling]
  case case62 =>
    intro n entrants ih e h
    unfold readHead at h; simp only [map_eq_ok] at h
    obtain ⟨es, hes, rfl⟩ := h
    simp [print, printAction, ih es hes, Head.spelling]
  case case63 =>
    intro n e h
    unfold readHead at h; simp at h; subst h
    simp [print, printAction, Head.spelling]
  case case64 =>
    intro n scope exit e h
    unfold readHead at h; simp only [bind_eq_ok] at h
    obtain ⟨s, hs, x, hx, he⟩ := h
    cases he
    simp [print, printAction, readTerm_exact scope hs, readTerm_exact exit hx, Head.spelling]
  case case65 =>
    intro n body ih e h
    unfold readHead at h; simp only [map_eq_ok] at h
    obtain ⟨b, hb, rfl⟩ := h
    simp [print, ih b hb, Head.spelling]
  case case66 =>
    intro n acquire x y release hxy ih1 ih2 e h
    obtain ⟨rfl, rfl⟩ := hxy
    unfold readHead at h
    simp only [and_self, if_true, bind_eq_ok] at h
    obtain ⟨a, ha, r, hr, he⟩ := h
    cases he
    simp [print, ih1 a ha, ih2 r hr, Head.spelling]
  case case67 =>
    intro n acquire x y release hne e h
    unfold readHead at h; simp [hne] at h
  case case68 =>
    intro n body layer ihb ihl e h
    unfold readHead at h; simp only [bind_eq_ok] at h
    obtain ⟨b, hb, l, hlayer, he⟩ := h
    cases he
    simp [print, ihb b hb, ihl l hlayer, Head.spelling]
  case case69 =>
    intro n body layer ihb ihl e h
    unfold readHead at h; simp only [if_true, bind_eq_ok] at h
    obtain ⟨b, hb, l, hlayer, he⟩ := h
    cases he
    simp [print, ihb b hb, ihl l hlayer, Head.spelling]
  case case70 =>
    intro n body layer field hfield e h
    unfold readHead at h; simp [hfield] at h
  case case71 =>
    intro n key e h
    unfold readHead at h; simp only [map_eq_ok] at h
    obtain ⟨k, hk, rfl⟩ := h
    simp [print, readKey_exact hk, Head.spelling]
  case case72 =>
    intro n body key value ih e h
    unfold readHead at h; simp only [bind_eq_ok] at h
    obtain ⟨b, hb, k, hk, v, hv, he⟩ := h
    cases he
    simp [print, ih b hb, readKey_exact hk, readTerm_exact value hv, Head.spelling]
  case case73 => intro t n e h; unfold readHead at h; simp at h
  case case74 => intro t n e h; unfold readHead at h; simp at h
  case case75 => intro t n e h; unfold readHead at h; simp at h
  case case76 => intro t n e h; unfold readHead at h; simp at h
  case case77 => intro t n e h; unfold readHead at h; simp at h
  case case78 => intro t n e h; unfold readHead at h; simp at h
  case case79 => intro t n e h; unfold readHead at h; simp at h
  case case80 => intro t n e h; unfold readHead at h; simp at h
  case case81 => intro t n e h; unfold readHead at h; simp at h
  case case82 => intro t n e h; unfold readHead at h; simp at h
  case case83 => intro t n e h; unfold readHead at h; simp at h
  case case84 => intro t n e h; unfold readHead at h; simp at h
  case case85 => intro t n e h; unfold readHead at h; simp at h
  case case86 => intro t n e h; unfold readHead at h; simp at h
  case case87 => intro t n e h; unfold readHead at h; simp at h
  case case88 => intro t n e h; unfold readHead at h; simp at h
  case case89 =>
    intro n hd t
    intros
    rename_i e h
    unfold readHead at h
    split at h <;> close_arm h
  -- readLayer: a reference by the identifier that carries its path (the host rows slice);
  -- the reader admits the name only when it is exactly the path's spelling, so the printer's
  -- identifier is recovered by that very equation
  case case16 =>
    intro target hread layer h
    unfold readLayer at h
    simp [hread] at h
    subst h
    rfl
  case case17 =>
    intro s target hread hne layer h
    unfold readLayer at h
    simp [hread, hne] at h
  case case18 =>
    intro s hread layer h
    unfold readLayer at h
    simp [hread] at h
  case case19 =>
    intro items ih layer h
    unfold readLayer at h; simp only [map_eq_ok] at h
    obtain ⟨ls, hls, rfl⟩ := h
    simp [printLayer, ih ls hls]
  case case20 =>
    intro key value layer h
    unfold readLayer at h; simp only [bind_eq_ok] at h
    obtain ⟨k, hk, v, hv, hlayer⟩ := h
    cases hlayer
    simp [printLayer, readKey_exact hk, readLiteral_exact hv]
  case case21 =>
    intro key body ih layer h
    unfold readLayer at h; simp only [bind_eq_ok] at h
    obtain ⟨k, hk, b, hb, hlayer⟩ := h
    cases hlayer
    simp [printLayer, readKey_exact hk, ih b hb]
  case case22 =>
    intro body ih layer h
    unfold readLayer at h; simp only [map_eq_ok] at h
    obtain ⟨b, hb, rfl⟩ := h
    simp [printLayer, ih b hb]
  case case23 =>
    intro self that ihs iht layer h
    unfold readLayer at h; simp only [bind_eq_ok] at h
    obtain ⟨s, hs, t, ht, hlayer⟩ := h
    cases hlayer
    simp [printLayer, ihs s hs, iht t ht]
  case case24 =>
    intro self that ihs iht layer h
    unfold readLayer at h; simp only [bind_eq_ok] at h
    obtain ⟨s, hs, t, ht, hlayer⟩ := h
    cases hlayer
    simp [printLayer, ihs s hs, iht t ht]
  case case25 =>
    intro left right ihl ihr layer h
    unfold readLayer at h; simp only [bind_eq_ok] at h
    obtain ⟨l, hl, r, hr, hlayer⟩ := h
    cases hlayer
    simp [printLayer, ihl l hl, ihr r hr]
  case case26 =>
    intro inner ih layer h
    unfold readLayer at h; simp only [map_eq_ok] at h
    obtain ⟨i, hi, rfl⟩ := h
    simp [printLayer, ih i hi]
  case case27 =>
    intro inner ih layer h
    unfold readLayer at h; simp only [map_eq_ok] at h
    obtain ⟨i, hi, rfl⟩ := h
    simp [printLayer, ih i hi]
  case case28 =>
    intro x
    intros
    rename_i layer h
    unfold readLayer at h
    split at h <;> close_arm h
  -- readEffs
  case case92 =>
    intro n es h
    unfold readEffs at h; simp at h; subst h; rfl
  case case93 =>
    intro n x rest ih1 ih2 es h
    unfold readEffs at h; simp only [bind_eq_ok] at h
    obtain ⟨e, he, es', hes', hes⟩ := h
    cases hes
    simp [printEffs, ih1 e he, ih2 es' hes']
  -- readLayers
  case case90 =>
    intro ls h
    unfold readLayers at h; simp at h; subst h; rfl
  case case91 =>
    intro x rest ih1 ih2 ls h
    unfold readLayers at h; simp only [bind_eq_ok] at h
    obtain ⟨l, hl, ls', hls', hls⟩ := h
    cases hls
    simp [printLayers, ih1 l hl, ih2 ls' hls']
  -- readStmts
  case case94 =>
    intro n ss h
    unfold readStmts at h; simp at h; subst h; rfl
  case case95 =>
    intro n value rest ih1 ih2 ss h
    unfold readStmts at h
    simp only [if_true, bind_eq_ok] at h
    obtain ⟨e, he, tail, htail, hss⟩ := h
    cases hss
    simp [printStmts, ih1 e he, ih2 tail htail]
  case case96 =>
    intro n x value rest hx ss h
    unfold readStmts at h; simp [hx] at h
  case case97 =>
    intro n value rest ih1 ih2 ss h
    unfold readStmts at h; simp only [bind_eq_ok] at h
    obtain ⟨e, he, tail, htail, hss⟩ := h
    cases hss
    simp [printStmts, ih1 e he, ih2 tail htail]
  case case98 =>
    intro n value rest ih ss h
    unfold readStmts at h; simp only [bind_eq_ok] at h
    obtain ⟨v, hv, tail, htail, hss⟩ := h
    cases hss
    simp [printStmts, readTerm_exact value hv, ih tail htail]
  case case99 =>
    intro n test thenB elseB rest ih1 ih2 ih3 ss h
    unfold readStmts at h; simp only [bind_eq_ok] at h
    obtain ⟨t, ht, a, ha, b, hb, tail, htail, hss⟩ := h
    cases hss
    simp [printStmts, readTerm_exact test ht, ih1 a ha, ih2 b hb, ih3 tail htail]
  case case100 =>
    intro n body rest ih1 ih2 ss h
    unfold readStmts at h; simp only [bind_eq_ok] at h
    obtain ⟨b, hb, tail, htail, hss⟩ := h
    cases hss
    simp [printStmts, ih1 b hb, ih2 tail htail]
  case case101 =>
    intro n rest ih ss h
    unfold readStmts at h; simp only [bind_eq_ok] at h
    obtain ⟨tail, htail, hss⟩ := h
    cases hss
    simp [printStmts, ih tail htail]
  case case102 =>
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

def rowKey (row : Row) : String × List String := (row.spelling, row.trailing)

/-- Uniqueness makes the first matching row exactly the supplied position. -/
theorem rowIndex_roundTrip (table : List Row) (hn : (table.map rowKey).Nodup)
    (i : Nat) (hi : i < table.length) :
    table.findIdx? (fun row => decide (rowKey row = rowKey table[i])) = some i := by
  induction table generalizing i with
  | nil => cases hi
  | cons row rest ih =>
    have hnodup := List.nodup_cons.mp hn
    cases i with
    | zero => simp [List.findIdx?_cons]
    | succ i =>
      have hi' : i < rest.length := Nat.lt_of_succ_lt_succ hi
      have hne : rowKey row ≠ rowKey rest[i] := by
        intro he
        exact hnodup.1 (List.mem_map.mpr ⟨rest[i], List.getElem_mem hi', he.symm⟩)
      simpa [List.findIdx?_cons, hne, ih hnodup.2 i hi']

/-- A successful lookup names an existing row with exactly the supplied key. -/
theorem rowIndex_exact (table : List Row) (key : String × List String) (i : Nat)
    (h : table.findIdx? (fun row => decide (rowKey row = key)) = some i) :
    ∃ hi : i < table.length, rowKey table[i] = key := by
  induction table generalizing i with
  | nil => simp at h
  | cons row rest ih =>
    rw [List.findIdx?_cons] at h
    split at h
    · rename_i hk
      cases h
      exact ⟨Nat.zero_lt_succ _, of_decide_eq_true hk⟩
    · obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hlt, hk⟩ := ih j hj
      exact ⟨Nat.succ_lt_succ hlt, hk⟩

theorem builtinLookup_none (key : String × List String)
    (h : key ∉ NativeOp.all.map (rowKey ∘ NativeOp.row)) :
    NativeOp.all.find? (fun op => decide (rowKey op.row = key)) = none := by
  apply List.find?_eq_none.mpr
  intro op hop heq
  apply h
  exact List.mem_map.mpr ⟨op, hop, of_decide_eq_true heq⟩

/-- The first UTF-8 byte; no traversal of a `String` enters the proof graph. -/
def firstByte (s : String) : Option UInt8 := s.toByteArray.data.toList.head?

/-- The names in a row cannot capture a printed binder or a reserved program head. -/
def rowNamesSafe (row : Row) : Bool :=
  firstByte row.spelling != some 97 && !reserved.contains row.spelling &&
    row.trailing.all (fun name => firstByte name != some 97 && name != "undefined")

/-- The four table requirements: unique keys, no built-in collision, no dropped
trailing names on a value row, and names outside the reserved/binder alphabets. -/
def LawfulTable (table : RowTable) : Bool :=
  decide (table.map rowKey).Nodup &&
    table.all (fun row => !(NativeOp.all.map (rowKey ∘ NativeOp.row)).contains (rowKey row)) &&
    table.all (fun row => !decide (row.shape = .value) || row.trailing.isEmpty) &&
    table.all rowNamesSafe

/-- Built-ins are checked first; the external key identifies its position in the
supplied table. No external index is recovered by parsing an identifier. -/
def nativeSpell (table : RowTable := []) (s : String) (names : List String) : Option NativeOp :=
  match NativeOp.all.find? (fun op => decide (rowKey op.row = (s, names))) with
  | some op => some op
  | none => (table.findIdx? (fun row => decide (rowKey row = (s, names)))).map NativeOp.external

theorem name_notin (l : List String) (h : ∀ s ∈ l, s.toByteArray.data.toList.head? ≠ some 97)
    (i : Nat) : Var.name i ∉ l := fun hm => Var.name_ne (h _ hm) i rfl

theorem NativeOp.external_not_mem_all (i : Nat) : NativeOp.external i ∉ NativeOp.all := by
  simp [NativeOp.all, fnNames]

theorem NativeOp.all_complete (op : NativeOp) (h : ∀ i, op ≠ .external i) :
    op ∈ NativeOp.all := by
  cases op <;> first
    | decide
    | (rename_i f; cases f <;> decide)
    | exact (h _ rfl).elim

theorem nativeRowOf_mem_all (table : RowTable) (op : NativeOp) (h : op ∈ NativeOp.all) :
    nativeRowOf table op = op.row := by
  cases op <;> first | rfl | exact (NativeOp.external_not_mem_all _ h).elim

theorem nativeRowOf_external (table : RowTable) (i : Nat) (hi : i < table.length) :
    nativeRowOf table (.external i) = table[i] := by
  simp [nativeRowOf, List.getElem?_eq_getElem hi]

theorem lawfulTable_member (table : RowTable) (h : LawfulTable table = true)
    (row : Row) (hr : row ∈ table) :
    rowKey row ∉ NativeOp.all.map (rowKey ∘ NativeOp.row) ∧
    (row.shape = .value → row.trailing = []) ∧ rowNamesSafe row = true := by
  simp only [LawfulTable, Bool.and_eq_true] at h
  refine ⟨?_, ?_, List.all_eq_true.mp h.2 row hr⟩
  · have hc := List.all_eq_true.mp h.1.1.2 row hr
    simpa using hc
  · have hv := List.all_eq_true.mp h.1.2 row hr
    intro hs
    simpa [hs] using hv

theorem nativeRow_hygiene (table : RowTable) (h : LawfulTable table = true) (op : NativeOp) :
    ((nativeRowOf table op).shape = .value → (nativeRowOf table op).trailing = []) ∧
      rowNamesSafe (nativeRowOf table op) = true := by
  cases op with
  | external i =>
    by_cases hi : i < table.length
    · rw [nativeRowOf_external table i hi]
      exact (lawfulTable_member table h _ (List.getElem_mem hi)).2
    · simp only [nativeRowOf, List.getElem?_eq_none (Nat.le_of_not_gt hi), Option.getD_none]
      decide
  | _ => first
    | (simp only [nativeRowOf]; decide)
    | (rename_i f; cases f <;> simp only [nativeRowOf] <;> decide)

theorem nativeLawful (table : RowTable := []) (h : LawfulTable table = true := by decide) :
    LawfulSpelling (nativeSignature table) (nativeSpell table) where
  spell_row := by
    intro op hd
    cases op with
    | external i =>
      have hi : i < table.length := of_decide_eq_true hd
      change nativeSpell table (nativeRowOf table (.external i)).spelling
        (nativeRowOf table (.external i)).trailing = some (.external i)
      rw [nativeRowOf_external table i hi]
      have hn : (table.map rowKey).Nodup := by
        simp only [LawfulTable, Bool.and_eq_true, decide_eq_true_eq] at h
        exact h.1.1.1
      have hc := (lawfulTable_member table h _ (List.getElem_mem hi)).1
      have hb := builtinLookup_none (rowKey table[i]) hc
      have hf := rowIndex_roundTrip table hn i hi
      dsimp +instances only [rowKey] at hb hf
      unfold nativeSpell rowKey
      rw [hb, hf]
      rfl
    | _ => first
      | rfl
      | (rename_i f; cases f <;> rfl)
  row_of_spell := by
    intro s names op hs
    unfold nativeSpell at hs
    split at hs
    · rename_i found hfound
      have heq : found = op := Option.some.inj hs
      subst op
      have hm := List.mem_of_find?_eq_some hfound
      have hk := List.find?_some
        (p := fun op : NativeOp => decide (rowKey op.row = (s, names))) hfound
      change (nativeRowOf table found).spelling = s ∧ (nativeRowOf table found).trailing = names
      rw [nativeRowOf_mem_all table found hm]
      exact Prod.mk.inj (of_decide_eq_true hk)
    · obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hs
      obtain ⟨hlt, hk⟩ := rowIndex_exact table (s, names) i hi
      change (nativeRowOf table (.external i)).spelling = s ∧
        (nativeRowOf table (.external i)).trailing = names
      rw [nativeRowOf_external table i hlt]
      exact Prod.mk.inj hk
  value_trailing := fun op => (nativeRow_hygiene table h op).1
  spelling_ne_name := by
    intro op i
    have hn := (nativeRow_hygiene table h op).2
    simp only [rowNamesSafe, Bool.and_eq_true] at hn
    exact (Var.name_ne (by simpa [firstByte, nativeSignature] using hn.1.1) i).symm
  spelling_not_reserved := by
    intro op
    have hn := (nativeRow_hygiene table h op).2
    simp only [rowNamesSafe, Bool.and_eq_true] at hn
    simpa [nativeSignature] using hn.1.2
  trailing_ne_name := by
    intro op i
    have hn := (nativeRow_hygiene table h op).2
    simp only [rowNamesSafe, Bool.and_eq_true] at hn
    apply name_notin
    intro name hm
    have ht := List.all_eq_true.mp hn.2 name hm
    simpa [firstByte, nativeSignature] using (Bool.and_eq_true_iff.mp ht).1
  trailing_ne_undefined := by
    intro op hm
    have hn := (nativeRow_hygiene table h op).2
    simp only [rowNamesSafe, Bool.and_eq_true] at hn
    have ht := List.all_eq_true.mp hn.2 "undefined" hm
    simp at ht

 theorem read_print_native (table : RowTable := []) (h : LawfulTable table = true := by decide)
    {n : Nat} (e : NativeEff)
    (hr : readable (nativeSignature table) (nativeSpell table) n e = true) {x : Expr}
    (hp : print (nativeSignature table) n e = .ok x) :
    readEff (nativeSignature table) (nativeSpell table) n x = .ok e :=
  read_print (nativeLawful table h) e hr hp

/-- `read_print` as the round trip: a readable program that prints comes back as itself. -/
theorem roundTrip_eq {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} {e : Eff Op}
    (hr : readable sig spell n e = true) {x : Expr} (hp : print sig n e = .ok x) :
    roundTrip sig spell n e = .ok e := by
  unfold roundTrip; rw [hp]; exact read_print hl e hr hp

theorem read_exact_native (table : RowTable := []) (ht : LawfulTable table = true := by decide)
    {n : Nat} {x : Expr} {e : NativeEff}
    (h : readEff (nativeSignature table) (nativeSpell table) n x = .ok e) :
    print (nativeSignature table) n e = .ok x :=
  read_exact (nativeLawful table ht) h

/-! ## Compatibility with positional weakening -/

private theorem weaken_index_inj (cut i j : Nat) :
    Var.weaken cut i = Var.weaken cut j ↔ i = j := by
  constructor
  · intro h
    by_cases hi : i < cut <;> by_cases hj : j < cut <;>
      simp only [Var.weaken, hi, hj, if_true, if_false] at h <;> omega
  · intro h
    subst j
    rfl

private theorem weaken_name_eq (cut i j : Nat) :
    Var.name (Var.weaken cut i) = Var.name (Var.weaken cut j) ↔ Var.name i = Var.name j := by
  constructor
  · intro h
    exact congrArg Var.name ((weaken_index_inj cut i j).mp (Var.name_inj h))
  · intro h
    rw [Var.name_inj h]

mutual
  theorem Term.scoped_weaken {cut n : Nat} (hc : cut ≤ n) (term : Term) :
      (Term.weaken cut term).scoped (n + 1) = term.scoped n :=
    match term with
    | .var index => by
      simp only [Term.weaken, Term.scoped]
      have hi : Var.weaken cut index < n + 1 ↔ index < n := by
        by_cases h : index < cut
        · rw [Var.weaken, if_pos h]
          exact iff_of_true (Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le h hc))
            (Nat.lt_of_lt_of_le h hc)
        · rw [Var.weaken, if_neg h]
          exact Nat.add_lt_add_iff_right
      simp only [hi]
    | .lit _ => rfl
    | .app _ args => Terms.scoped_weaken hc args

  theorem Terms.scoped_weaken {cut n : Nat} (hc : cut ≤ n) (terms : Terms) :
      (Terms.weaken cut terms).scoped (n + 1) = terms.scoped n :=
    match terms with
    | .nil => rfl
    | .cons head tail => by
      simp only [Terms.weaken, Terms.scoped, Term.scoped_weaken hc head,
        Terms.scoped_weaken hc tail]
end

theorem CauseTerm.scoped_weaken {cut n : Nat} (hc : cut ≤ n) (cause : CauseTerm) :
    (CauseTerm.weaken cut cause).scoped (n + 1) = cause.scoped n := by
  induction cause with
  | fail _ | die _ => simp only [CauseTerm.weaken, CauseTerm.scoped, Term.scoped_weaken hc]
  | interrupt who => cases who <;> simp only [CauseTerm.weaken, CauseTerm.scoped,
      Option.map, Term.scoped_weaken hc]
  | both _ _ ihl ihr => simp only [CauseTerm.weaken, CauseTerm.scoped, ihl, ihr]

private theorem names_cons_spell_none {sig : Signature Op}
    {spell : String → List String → Option Op} (hl : LawfulSpelling sig spell)
    (atom : String) (head : Term) (tail : Terms) :
    ((Terms.names? (.cons head tail)).bind (spell atom)) = none := by
  have noHead (v : String) (hv : ∀ op, v ∉ (sig.rowOf op).trailing) (names : List String) :
      spell atom (v :: names) = none := by
    cases hs : spell atom (v :: names) with
    | none => rfl
    | some op =>
      have ht := (hl.row_of_spell atom (v :: names) op hs).2
      exact False.elim (hv op (by rw [ht]; simp))
  cases head with
  | var i =>
    cases ht : Terms.names? tail <;>
      simp [Terms.names?, ht, noHead (Var.name i) (fun op => hl.trailing_ne_name op i)]
  | lit value =>
    cases value <;> first
      | rfl
      | (cases ht : Terms.names? tail <;>
          simp [Terms.names?, ht, noHead "undefined" hl.trailing_ne_undefined])
  | app _ _ => rfl

private theorem names_spell_weaken {sig : Signature Op}
    {spell : String → List String → Option Op} (hl : LawfulSpelling sig spell)
    (cut : Nat) (atom : String) (args : Terms) :
    ((Terms.weaken cut args).names?).bind (spell atom) = (args.names?).bind (spell atom) := by
  cases args with
  | nil => rfl
  | cons _ _ => simp only [Terms.weaken, names_cons_spell_none hl]

private theorem noRow_weaken {sig : Signature Op}
    {spell : String → List String → Option Op} (hl : LawfulSpelling sig spell)
    (cut : Nat) (atom : String) (args : Terms) :
    noRow spell atom (Terms.weaken cut args) = noRow spell atom args := by
  cases args with
  | nil => rfl
  | cons head tail =>
    cases tail <;> simp only [Terms.weaken, noRow, names_cons_spell_none hl,
      names_spell_weaken hl]

private theorem savedVar_weaken (cut : Nat) (x y : Term) :
    (savedVar? (printTerm (Term.weaken cut x)) (printTerm (Term.weaken cut y))).isNone =
      (savedVar? (printTerm x) (printTerm y)).isNone := by
  cases x with
  | var _ => rfl
  | lit value => cases value <;> rfl
  | app f xs =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      cases x with
      | app _ _ => rfl
      | lit value =>
        cases value <;> try rfl
        cases xs with
        | cons _ _ => rfl
        | nil =>
          cases y with
          | var _ => rfl
          | lit value => cases value <;> rfl
          | app g ys =>
            cases ys with
            | nil => rfl
            | cons y ys =>
              cases y with
              | app _ _ => rfl
              | lit value =>
                cases value <;> try rfl
                cases ys with
                | cons _ _ => rfl
                | nil =>
                  simp only [Term.weaken, Terms.weaken, printTerm, printTerms, printLit, savedVar?]
                  all_goals first | rfl | (split <;> rfl)
              | var _ =>
                cases ys with
                | cons _ _ => rfl
                | nil =>
                  simp only [Term.weaken, Terms.weaken, printTerm, printTerms, printLit,
                    savedVar?, Ne.symm (Var.name_ne_undefined _)]
                  all_goals first | rfl | (split <;> rfl)
      | var _ =>
        cases xs with
        | cons _ _ => rfl
        | nil =>
          cases y with
          | var _ => rfl
          | lit value => cases value <;> rfl
          | app g ys =>
            cases ys with
            | nil => rfl
            | cons y ys =>
              cases y with
              | app _ _ => rfl
              | lit value =>
                cases value <;> try rfl
                cases ys with
                | cons _ _ => rfl
                | nil =>
                  simp only [Term.weaken, Terms.weaken, printTerm, printTerms, printLit,
                    savedVar?, Var.name_ne_undefined]
                  all_goals first | rfl | (split <;> rfl)
              | var _ =>
                cases ys with
                | cons _ _ => rfl
                | nil =>
                  simp only [Term.weaken, Terms.weaken, printTerm, printTerms, savedVar?, weaken_name_eq]
                  all_goals first | rfl | (split <;> rfl)

private theorem pairArgs_weaken (cut : Nat) (request : Term) :
    pairArgs? (Term.weaken cut request) =
      (pairArgs? request).map (fun (x, y) => (Term.weaken cut x, Term.weaken cut y)) := by
  cases request with
  | var _ | lit _ => rfl
  | app atom args =>
    cases args with
    | nil => rfl
    | cons x rest =>
      cases rest with
      | nil => rfl
      | cons y rest =>
        cases rest with
        | cons _ _ => rfl
        | nil => simp only [Term.weaken, Terms.weaken, pairArgs?]; split <;> rfl

private theorem weaken_eq_unit (cut : Nat) (request : Term) :
    Term.weaken cut request = .lit .unit ↔ request = .lit .unit := by
  cases request <;> simp only [Term.weaken, reduceCtorEq]

private theorem tupleRequestReadable_weaken {cut n : Nat} (hc : cut ≤ n) (request : Term) :
    tupleRequestReadable (n + 1) (Term.weaken cut request) = tupleRequestReadable n request := by
  simp only [tupleRequestReadable]
  rw [pairArgs_weaken]
  cases hp : pairArgs? request with
  | some xy =>
    obtain ⟨x, y⟩ := xy
    simp only [Option.map, Term.scoped_weaken hc, savedVar_weaken]
  | none =>
    cases request with
    | var index => exact Term.scoped_weaken hc (.var index)
    | lit value => cases value <;> rfl
    | app _ _ => rfl

private theorem requestReadable_weaken {cut n : Nat} (hc : cut ≤ n) (row : Row)
    (request : Term) :
    requestReadable row (n + 1) (Term.weaken cut request) = requestReadable row n request := by
  cases hs : row.shape with
  | value => simp only [requestReadable, hs, weaken_eq_unit]
  | call =>
    simp only [requestReadable, hs]
    split <;> simp only [weaken_eq_unit, Term.scoped_weaken hc]
  | tupleCall => simpa only [requestReadable, hs] using tupleRequestReadable_weaken hc request
  | method =>
    simp only [requestReadable, hs, pairArgs_weaken]
    cases hp : pairArgs? request with
    | none => rfl
    | some parts =>
      obtain ⟨receiver, args⟩ := parts
      simp only [Option.map, Term.scoped_weaken hc, tupleRequestReadable_weaken hc, weaken_eq_unit]

mutual
  /-- Inserting an unused environment slot retains exactly the readable domain. -/
  theorem readable_weaken {sig : Signature Op} {spell : String → List String → Option Op}
      (hl : LawfulSpelling sig spell) {cut n : Nat} (hc : cut ≤ n) (program : Eff Op) :
      readable sig spell (n + 1) (Eff.weaken cut program) = readable sig spell n program :=
    match program with
    | .yieldError error => by
      cases error with
      | var index => exact Term.scoped_weaken hc (.var index)
      | lit _ => rfl
      | app atom args => simp only [Eff.weaken, Term.weaken, readable,
          noRow_weaken hl, Terms.scoped_weaken hc]
    | .succeed _ | .fail _ | .failCause _ | .sync _ | .suspend _ | .perform _ _
    | .bind _ _ | .gen _ | .catchCause _ _ | .matchCause _ _ _ | .onExit _ _ | .exit _
    | .uninterruptible _ | .interruptible _ | .branch _ _ _ | .whileLoop _ _ _ _
    | .yieldNow _ | .callback _ _ | .awaitFiber _ _ | .withFiber _ | .scoped _
    | .acquireRelease _ _ | .choose _ _ _ | .provideLayer _ _ _ | .service _
    | .provideService _ _ _ => by
      have hc1 : cut ≤ n + 1 := Nat.le_trans hc (Nat.le_add_right n 1)
      have hc2 : cut ≤ n + 2 := Nat.le_trans hc (Nat.le_add_right n 2)
      simp only [Eff.weaken, readable, Term.scoped_weaken hc,
        CauseTerm.scoped_weaken hc, requestReadable_weaken hc,
        readable_weaken hl hc, readable_weaken hl hc1, readable_weaken hl hc2,
        readableStmts_weaken hl hc, readableAction_weaken hl hc,
        Term.scoped_weaken hc1, Nat.add_right_comm n 1 2, Term.scoped_weaken hc2]

  theorem readableStmts_weaken {sig : Signature Op} {spell : String → List String → Option Op}
      (hl : LawfulSpelling sig spell) {cut n : Nat} (hc : cut ≤ n) (stmts : Stmts Op) :
      readableStmts sig spell (n + 1) (Stmts.weaken cut stmts) = readableStmts sig spell n stmts :=
    match stmts with
    | .nil => rfl
    | .cons stmt rest => by
      have hc1 : cut ≤ n + 1 := Nat.le_trans hc (Nat.le_add_right n 1)
      cases stmt <;> simp only [Stmts.weaken, Stmt.weaken, readableStmts,
        Term.scoped_weaken hc, readable_weaken hl hc,
        readableStmts_weaken hl hc, readableStmts_weaken hl hc1]

  theorem readableEffs_weaken {sig : Signature Op} {spell : String → List String → Option Op}
      (hl : LawfulSpelling sig spell) {cut n : Nat} (hc : cut ≤ n) (effects : Effs Op) :
      readableEffs sig spell (n + 1) (Effs.weaken cut effects) = readableEffs sig spell n effects :=
    match effects with
    | .nil => rfl
    | .cons head tail => by
      simp only [Effs.weaken, readableEffs, readable_weaken hl hc, readableEffs_weaken hl hc]

  theorem readableAction_weaken {sig : Signature Op} {spell : String → List String → Option Op}
      (hl : LawfulSpelling sig spell) {cut n : Nat} (hc : cut ≤ n) (action : ActionTerm Op) :
      readableAction sig spell (n + 1) (ActionTerm.weaken cut action) = readableAction sig spell n action :=
    match action with
    | .interruptAll _ who => by
      cases who <;> simp only [ActionTerm.weaken, readableAction, Option.map, Term.scoped_weaken hc]
    | .fork _ _ | .forkIn _ _ _ | .forkScoped _ _ | .runIn _ _ | .interrupt _
    | .interruptScoped _ | .awaitAll _ | .awaitAllFailFast _ | .snapshotChildren
    | .awaitNewChildren _ | .raceAll _ | .setContext _ | .getContext | .getId
    | .closeScope _ _ => by
      simp only [ActionTerm.weaken, readableAction, Term.scoped_weaken hc,
        readable_weaken hl hc, readableEffs_weaken hl hc]
end

mutual
  /-- Every program in the readable domain has a printed expression. -/
  theorem print_readable (sig : Signature Op) (spell : String → List String → Option Op)
      (n : Nat) (program : Eff Op) (hr : readable sig spell n program = true) :
      ∃ x, print sig n program = .ok x :=
    match program with
    | .succeed _ | .fail _ | .failCause _ | .yieldError _ | .sync _ | .perform _ _
    | .yieldNow _ | .callback _ _ => ⟨_, rfl⟩
    | .suspend body | .exit body | .uninterruptible body | .interruptible body | .scoped body => by
      obtain ⟨b, hb⟩ := print_readable sig spell n body hr
      exact ⟨_, by simp only [print, hb] <;> rfl⟩
    | .bind first rest | .catchCause first rest | .onExit first rest => by
      have hs := Bool.and_eq_true_iff.mp hr
      obtain ⟨f, hf⟩ := print_readable sig spell n first hs.1
      obtain ⟨r, hrest⟩ := print_readable sig spell (n + 1) rest hs.2
      exact ⟨_, by simp only [print, hf, hrest] <;> rfl⟩
    | .gen body => by
      obtain ⟨b, hb⟩ := printStmts_readable sig spell n body hr
      exact ⟨_, by simp only [print, hb] <;> rfl⟩
    | .matchCause body onValue onCause => by
      have hs := Bool.and_eq_true_iff.mp hr
      have hbv := Bool.and_eq_true_iff.mp hs.1
      obtain ⟨b, hb⟩ := print_readable sig spell n body hbv.1
      obtain ⟨v, hv⟩ := print_readable sig spell (n + 1) onValue hbv.2
      obtain ⟨c, hc⟩ := print_readable sig spell (n + 1) onCause hs.2
      exact ⟨_, by simp only [print, hb, hv, hc] <;> rfl⟩
    | .branch _ thenB elseB => by
      have hs := Bool.and_eq_true_iff.mp hr
      obtain ⟨a, ha⟩ := print_readable sig spell n thenB (Bool.and_eq_true_iff.mp hs.1).2
      obtain ⟨b, hb⟩ := print_readable sig spell n elseB hs.2
      exact ⟨_, by simp only [print, ha, hb] <;> rfl⟩
    | .whileLoop _ _ _ body => by
      obtain ⟨b, hb⟩ := print_readable sig spell (n + 1) body (Bool.and_eq_true_iff.mp hr).2
      exact ⟨_, by simp only [print, hb] <;> rfl⟩
    | .awaitFiber _ mode => by cases mode <;> exact ⟨_, rfl⟩
    | .withFiber action => printAction_readable sig spell n action hr
    | .acquireRelease acquire release => by
      have hs := Bool.and_eq_true_iff.mp hr
      obtain ⟨a, ha⟩ := print_readable sig spell n acquire hs.1
      obtain ⟨r, hrel⟩ := print_readable sig spell (n + 2) release hs.2
      exact ⟨_, by simp only [print, ha, hrel] <;> rfl⟩
    | .choose _ _ _ => by cases hr
    | .service _ => ⟨_, rfl⟩
    | .provideLayer layer _ body => by
      have hs := Bool.and_eq_true_iff.mp hr
      obtain ⟨b, hb⟩ := print_readable sig spell n body hs.2
      obtain ⟨l, hlayer⟩ := printLayer_readable sig spell layer hs.1
      exact ⟨_, by simp only [print, hb, hlayer] <;> rfl⟩
    | .provideService _ _ body => by
      obtain ⟨b, hb⟩ := print_readable sig spell n body (Bool.and_eq_true_iff.mp hr).2
      exact ⟨_, by simp only [print, hb] <;> rfl⟩

  theorem printLayer_readable (sig : Signature Op) (spell : String → List String → Option Op)
      (layer : LayerTerm Op) (hr : readableLayer sig spell layer = true) :
      ∃ x, printLayer sig layer = .ok x :=
    match layer with
    | .succeed _ _ => ⟨_, rfl⟩
    | .effect _ body | .effectDiscard body => by
      obtain ⟨b, hb⟩ := print_readable sig spell 0 body hr
      exact ⟨_, by simp only [printLayer, hb] <;> rfl⟩
    | .provide self that | .provideMerge self that | .merge self that => by
      have hs := Bool.and_eq_true_iff.mp hr
      obtain ⟨a, ha⟩ := printLayer_readable sig spell self hs.1
      obtain ⟨b, hb⟩ := printLayer_readable sig spell that hs.2
      exact ⟨_, by simp only [printLayer, ha, hb] <;> rfl⟩
    | .fresh inner | .orDie inner => by
      obtain ⟨i, hi⟩ := printLayer_readable sig spell inner hr
      exact ⟨_, by simp only [printLayer, hi] <;> rfl⟩
    | .ref _ => ⟨_, rfl⟩
    | .mergeAll layers => by
      obtain ⟨items, hi⟩ := printLayers_readable sig spell layers hr
      exact ⟨_, by simp only [printLayer, hi] <;> rfl⟩

  theorem printLayers_readable (sig : Signature Op) (spell : String → List String → Option Op)
      (layers : LayerTerms Op) (hr : readableLayers sig spell layers = true) :
      ∃ x, printLayers sig layers = .ok x :=
    match layers with
    | .nil => ⟨_, rfl⟩
    | .cons head tail => by
      have hs := Bool.and_eq_true_iff.mp hr
      obtain ⟨h, hh⟩ := printLayer_readable sig spell head hs.1
      obtain ⟨t, ht⟩ := printLayers_readable sig spell tail hs.2
      exact ⟨_, by simp only [printLayers, hh, ht] <;> rfl⟩

  theorem printStmts_readable (sig : Signature Op) (spell : String → List String → Option Op)
      (n : Nat) (stmts : Stmts Op) (hr : readableStmts sig spell n stmts = true) :
      ∃ x, printStmts sig n stmts = .ok x :=
    match stmts with
    | .nil => ⟨_, rfl⟩
    | .cons (.bindYield effect) rest => by
      have hs := Bool.and_eq_true_iff.mp hr
      obtain ⟨e, he⟩ := print_readable sig spell n effect hs.1
      obtain ⟨r, hrest⟩ := printStmts_readable sig spell (n + 1) rest hs.2
      exact ⟨_, by simp only [printStmts, he, hrest] <;> rfl⟩
    | .cons (.yieldDiscard effect) rest => by
      have hs := Bool.and_eq_true_iff.mp hr
      obtain ⟨e, he⟩ := print_readable sig spell n effect hs.1
      obtain ⟨r, hrest⟩ := printStmts_readable sig spell n rest hs.2
      exact ⟨_, by simp only [printStmts, he, hrest] <;> rfl⟩
    | .cons (.ret _) rest => by
      obtain ⟨r, hrest⟩ := printStmts_readable sig spell n rest (Bool.and_eq_true_iff.mp hr).2
      exact ⟨_, by simp only [printStmts, hrest] <;> rfl⟩
    | .cons (.ifElse _ thenB elseB) rest => by
      have hs := Bool.and_eq_true_iff.mp hr
      have hab := Bool.and_eq_true_iff.mp hs.1
      obtain ⟨a, ha⟩ := printStmts_readable sig spell n thenB (Bool.and_eq_true_iff.mp hab.1).2
      obtain ⟨b, hb⟩ := printStmts_readable sig spell n elseB hab.2
      obtain ⟨r, hrest⟩ := printStmts_readable sig spell n rest hs.2
      exact ⟨_, by simp only [printStmts, ha, hb, hrest] <;> rfl⟩
    | .cons (.whileTrue body) rest => by
      have hs := Bool.and_eq_true_iff.mp hr
      obtain ⟨b, hb⟩ := printStmts_readable sig spell n body hs.1
      obtain ⟨r, hrest⟩ := printStmts_readable sig spell n rest hs.2
      exact ⟨_, by simp only [printStmts, hb, hrest] <;> rfl⟩
    | .cons .breakLoop rest => by
      obtain ⟨r, hrest⟩ := printStmts_readable sig spell n rest hr
      exact ⟨_, by simp only [printStmts, hrest] <;> rfl⟩

  theorem printEffs_readable (sig : Signature Op) (spell : String → List String → Option Op)
      (n : Nat) (effects : Effs Op) (hr : readableEffs sig spell n effects = true) :
      ∃ x, printEffs sig n effects = .ok x :=
    match effects with
    | .nil => ⟨_, rfl⟩
    | .cons head tail => by
      have hs := Bool.and_eq_true_iff.mp hr
      obtain ⟨h, hh⟩ := print_readable sig spell n head hs.1
      obtain ⟨t, ht⟩ := printEffs_readable sig spell n tail hs.2
      exact ⟨_, by simp only [printEffs, hh, ht] <;> rfl⟩

  theorem printAction_readable (sig : Signature Op) (spell : String → List String → Option Op)
      (n : Nat) (action : ActionTerm Op) (hr : readableAction sig spell n action = true) :
      ∃ x, printAction sig n action = .ok x :=
    match action with
    | .fork program _ => by
      obtain ⟨p, hp⟩ := print_readable sig spell n program hr
      exact ⟨_, by simp only [printAction, hp] <;> rfl⟩
    | .forkIn program _ _ => by
      obtain ⟨p, hp⟩ := print_readable sig spell n program (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hr).1).1
      exact ⟨_, by simp only [printAction, hp] <;> rfl⟩
    | .forkScoped program _ => by
      obtain ⟨p, hp⟩ := print_readable sig spell n program (Bool.and_eq_true_iff.mp hr).1
      exact ⟨_, by simp only [printAction, hp] <;> rfl⟩
    | .runIn _ _ | .interrupt _ | .awaitAll _ | .getContext | .getId | .closeScope _ _ => ⟨_, rfl⟩
    | .interruptAll _ who => by cases who <;> exact ⟨_, rfl⟩
    | .raceAll entrants => by
      obtain ⟨es, hes⟩ := printEffs_readable sig spell n entrants hr
      exact ⟨_, by simp only [printAction, hes] <;> rfl⟩
    | .interruptScoped _ | .awaitAllFailFast _ | .snapshotChildren | .awaitNewChildren _
    | .setContext _ => by cases hr
end

/-- A readable program shifted into an environment with one inserted slot prints
and reads back as exactly the shifted program. This is an AST round trip under
`LawfulSpelling`; it makes no claim about execution by a TypeScript host. -/
theorem roundTrip_weaken {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {cut n : Nat} (hc : cut ≤ n) (program : Eff Op)
    (hr : readable sig spell n program = true) :
    roundTrip sig spell (n + 1) (Eff.weaken cut program) = .ok (Eff.weaken cut program) := by
  have hw : readable sig spell (n + 1) (Eff.weaken cut program) = true := by
    rw [readable_weaken hl hc, hr]
  obtain ⟨x, hp⟩ := print_readable sig spell (n + 1) (Eff.weaken cut program) hw
  exact roundTrip_eq hl hw hp

end Effect4.Program
