import Effect4.Codegen.Read

/-!
# Codegen.Forms

The foreign spellings admitted in addition to the printed image. Templates are data,
relative to the environment at the head. `here k` means level `n + k`; an effect slot
records the insertion cut relative to n and the number of inserted binders. No template
stores an absolute variable position. Examples are checked by each row through the
existing printer and reader; these are finite syntax receipts, not host equivalence.
-/

namespace Effect4.Codegen.Forms

open Effect4 Effect4.Program Effect4.Machine Effect4.Supervision

inductive ArgClass
  | effect | continuation | thunk | literal | term | termArm | key | releaseOne | handlers
  deriving DecidableEq, BEq

inductive Arity
  | value | call (count : Nat) | dual (count : Nat)
  deriving DecidableEq, BEq

inductive TermTemplate
  | literal (value : Lit)
  | argument (slot : Nat)
  | here (binder : Nat)
  deriving DecidableEq, BEq

inductive Template
  | argument (slot cutOffset insertions : Nat)
  | succeed (value : TermTemplate)
  | die (value : TermTemplate)
  | bind (first rest : Template)
  | onExit (body finalizer : Template)
  | matchCause (body onValue onCause : Template)
  | service (keySlot : Nat)
  | yieldNow (priority : Nat)
  | fork (body : Template) (options : ForkOptions)
  | forkIn (body : Template) (scope : TermTemplate) (options : ForkOptions)
  | forkScoped (body : Template) (options : ForkOptions)
  | acquireRelease (acquire release : Template)
  deriving DecidableEq, BEq

structure Arguments where
  effects : List (Eff NativeOp) := []
  terms : List Term := []
  keys : List ServiceKey := []

def TermTemplate.expand (n : Nat) (args : Arguments) : TermTemplate → Option Term
  | .literal value => some (.lit value)
  | .argument slot => args.terms[slot]?
  | .here k => some (.var (n + k))

/-- Insert `count` unused slots at `cut`, visiting the argument's own local binders. -/
def insert (cut : Nat) : Nat → Eff NativeOp → Eff NativeOp
  | 0, p => p
  | count + 1, p => insert cut count (Eff.weaken cut p)

def Template.expand (n : Nat) (args : Arguments) : Template → Option (Eff NativeOp)
  | .argument slot offset count => (args.effects[slot]?).map (insert (n + offset) count)
  | .succeed t => (t.expand n args).map .succeed
  | .die t => (t.expand n args).map (fun v => .failCause (.die v))
  | .bind a b => return .bind (← a.expand n args) (← b.expand n args)
  | .onExit a b => return .onExit (← a.expand n args) (← b.expand n args)
  | .matchCause a b c => return .matchCause (← a.expand n args) (← b.expand n args) (← c.expand n args)
  | .service i => (args.keys[i]?).map .service
  | .yieldNow p => some (.yieldNow p)
  | .fork body options => return .withFiber (.fork (← body.expand n args) options)
  | .forkIn body scope options => return .withFiber (.forkIn (← body.expand n args) options (← scope.expand n args))
  | .forkScoped body options => return .withFiber (.forkScoped (← body.expand n args) options)
  | .acquireRelease a b => return .acquireRelease (← a.expand n args) (← b.expand n args)

structure Form where
  id : String
  head : String
  arity : Arity
  arguments : List ArgClass
  expansion : Template
  citation : String
  deriving DecidableEq, BEq

def defaults (daemon : Bool) : ForkOptions :=
  { startImmediately := false, daemon := daemon, maskMode := .inherit }

/-- Every admitted derived form and the option/handler/release shape relaxations.
Citations name the pinned host definitions, not an unversioned API reference. -/
def all : List Form :=
  [ ⟨"void", "Effect.void", .value, [], .succeed (.literal .unit), "internal/effect.ts:1024-1026"⟩
  , ⟨"die", "Effect.die", .call 1, [.literal], .die (.argument 0), "internal/effect.ts:1018"⟩
  , ⟨"yieldKey", "yield* Key", .call 1, [.key], .service 0, "internal/effect.ts:2059"⟩
  , ⟨"andThenEffect", "Effect.andThen", .dual 2, [.effect, .effect],
      .bind (.argument 0 0 0) (.argument 1 0 1), "internal/effect.ts:1417-1439"⟩
  , ⟨"andThenContinuation", "Effect.andThen", .dual 2, [.effect, .continuation],
      .bind (.argument 0 0 0) (.argument 1 0 0), "internal/effect.ts:1417-1439"⟩
  , ⟨"andThenThunk", "Effect.andThen", .dual 2, [.effect, .thunk],
      .bind (.argument 0 0 0) (.argument 1 0 1), "internal/effect.ts:1417-1439"⟩
  , ⟨"as", "Effect.as", .dual 2, [.effect, .literal],
      .bind (.argument 0 0 0) (.succeed (.argument 0)), "internal/effect.ts:1386-1414"⟩
  , ⟨"asVoid", "Effect.asVoid", .call 1, [.effect],
      .bind (.argument 0 0 0) (.succeed (.literal .unit)), "internal/effect.ts:1467"⟩
  , ⟨"tapContinuation", "Effect.tap", .dual 2, [.effect, .continuation],
      .bind (.argument 0 0 0) (.bind (.argument 1 0 0) (.succeed (.here 0))), "internal/effect.ts:1442-1464"⟩
  , ⟨"tapEffect", "Effect.tap", .dual 2, [.effect, .effect],
      .bind (.argument 0 0 0) (.bind (.argument 1 0 1) (.succeed (.here 0))), "internal/effect.ts:1442-1464"⟩
  , ⟨"ensuring", "Effect.ensuring", .dual 2, [.effect, .effect],
      .onExit (.argument 0 0 0) (.argument 1 0 1), "internal/effect.ts:4043-4057"⟩
  , ⟨"matchCause", "Effect.matchCause", .dual 2, [.effect, .termArm, .termArm],
      .matchCause (.argument 0 0 0) (.succeed (.argument 0)) (.succeed (.argument 1)), "internal/effect.ts:3468-3495"⟩
  , ⟨"matchCauseEffect", "Effect.matchCauseEffect", .dual 2, [.effect, .handlers],
      .matchCause (.argument 0 0 0) (.argument 1 0 0) (.argument 2 0 0), "internal/effect.ts:3427-3460"⟩
  , ⟨"yieldNow", "Effect.yieldNow", .value, [], .yieldNow 0, "internal/effect.ts:997"⟩
  , ⟨"forkChildDefault", "Effect.forkChild", .call 1, [.effect],
      .fork (.argument 0 0 0) (defaults false), "internal/effect.ts:5228-5284"⟩
  , ⟨"forkDetachDefault", "Effect.forkDetach", .call 1, [.effect],
      .fork (.argument 0 0 0) (defaults true), "internal/effect.ts:5287-5334"⟩
  , ⟨"forkInDefault", "Effect.forkIn", .call 2, [.effect, .term],
      .forkIn (.argument 0 0 0) (.argument 0) (defaults true), "internal/effect.ts:5337-5379"⟩
  , ⟨"forkScopedDefault", "Effect.forkScoped", .call 1, [.effect],
      .forkScoped (.argument 0 0 0) (defaults true), "internal/effect.ts:5382-5406"⟩
  , ⟨"releaseOne", "Effect.acquireRelease", .call 2, [.effect, .releaseOne],
      .acquireRelease (.argument 0 0 0) (.argument 1 1 1), "internal/effect.ts:3971-4000"⟩
  ]

/-- An injective shape alphabet; takeAndBump has no lambda spelling by owner ruling. -/
inductive LambdaShape
  | addOne | multiplyTwo | optionNone | positiveThenZero
  deriving DecidableEq, BEq

def lambdaShape : FnName → Option LambdaShape
  | .incr => some .addOne
  | .double => some .multiplyTwo
  | .noChange => some .optionNone
  | .zeroWhenPositive => some .positiveThenZero
  | .takeAndBump => none

def lambdaAtom : LambdaShape → FnName
  | .addOne => .incr
  | .multiplyTwo => .double
  | .optionNone => .noChange
  | .positiveThenZero => .zeroWhenPositive

theorem lambdaShape_atom (s : LambdaShape) : lambdaShape (lambdaAtom s) = some s := by
  cases s <;> rfl

theorem lambdaAtom_exact (f : FnName) (s : LambdaShape) (h : lambdaShape f = some s) :
    lambdaAtom s = f := by
  cases f <;> cases s <;> cases h <;> rfl

/-- The host's dual-call dispatch data. It records unsupported heads too; arity metadata
never admits a head without a profile row or an expansion in `all`. -/
inductive DualRule
  | fixed (arity : Nat) | effectFirst | provideService | functionSecond | effectSecond
  deriving DecidableEq, BEq

def duals : List (String × DualRule) :=
  (["flatMap", "catchCause", "matchCauseEffect", "onExit", "map", "andThen", "tap", "as",
    "timeout", "mapError", "delay", "ensuring", "catch", "tapError", "retry", "matchCause"].map
    fun name => ("Effect." ++ name, .fixed 2)) ++
  (["forkChild", "forkDetach", "forkIn", "forkScoped", "provide", "catchTag", "catchIf"].map
    fun name => ("Effect." ++ name, .effectFirst)) ++
  [("Effect.provideService", .provideService), ("Effect.forEach", .functionSecond),
   ("Effect.zip", .effectSecond), ("Effect.race", .effectSecond)]

def unaryRefs : List String :=
  ["Effect.exit", "Effect.uninterruptible", "Effect.interruptible", "Effect.scoped",
   "Effect.orDie", "Effect.asVoid", "Effect.ignore", "Layer.fresh", "Layer.orDie"]

/-- Form-local examples include nested argument binders so insertion must shift their
levels. Wrap `example n` in n outer binders before checking the closed round trip. -/
def Form.exampleArgs (f : Form) (n : Nat) : Arguments :=
  let continuation := f.arguments.contains .continuation || f.arguments.contains .releaseOne ||
    f.arguments.contains .handlers
  let second := if continuation then .succeed (.var n)
    else .bind (.succeed (.lit (.nat 22))) (.succeed (.var n))
  { effects := [.succeed (.lit (.nat 11)), second, .succeed (.var n)]
    terms := if f.arguments.contains .termArm then [.var n, .var n]
      else [.lit (.nat 7), .lit (.nat 8)]
    keys := [⟨⟨4⟩, ⟨4⟩⟩] }

def close (n : Nat) (p : Eff NativeOp) : Eff NativeOp :=
  match n with
  | 0 => p
  | n + 1 => .bind (.succeed (.lit (.nat 3))) (close n p)

def Form.example (f : Form) (n : Nat) : Option (Eff NativeOp) :=
  (f.expansion.expand n (f.exampleArgs n)).map fun p => close n
    (if f.id == "yieldKey" then .gen (.cons (.bindYield p) (.cons (.ret (.var n)) .nil)) else p)

def Form.checkExample (f : Form) (n : Nat) : Bool :=
  match f.example n with
  | none => false
  | some p => roundTrip nativeSignature nativeSpell 0 p == .ok p

#guard all.length == 19
#guard (all.map (·.id)).eraseDups.length == all.length
#guard all.all (fun f => [0, 1, 2, 5].all f.checkExample)
#guard lambdaShape .takeAndBump == none
#guard lambdaAtom .addOne == .incr

end Effect4.Codegen.Forms
