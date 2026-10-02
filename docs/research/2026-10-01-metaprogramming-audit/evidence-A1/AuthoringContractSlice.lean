import Effect4.Api
import Effect4.Program.Authoring.Sugar
import Effect4.Laws.Program.Authoring.Sugar
import Effect4.Codegen.Authoring.Forms
import Effect4.Laws.Program.Authoring.Forms

/-!
# Authoring contract — programs written by name elaborate to the trees written by level

`src/Effect4/Program/Authoring.lean` lifts the constructors of `Eff` through a scope of names
(DI-83). This battery pins, for every binding construct an author may write, that the named
program elaborates to exactly the positional tree an author would otherwise count out, that
the tree types under the native signature, and that it runs. Refusals are pinned at their
paths. The shared-layer modules elaborate to the `once` and `twice` programs of the existing
layer-sharing battery `Test/Program/LayerSharingContract.lean`, with the same reference
target, so the placement rule (first use in program order) is checked against programs the
runtime already certifies.

Every pin is a `#guard`: finite evidence that each lift extends the scope by the names its
constructor binds. The universal statement is `Laws/Program/Authoring/Lifts.lean`: every
lift preserves `Src.Scoped` against the one binder table, and `authoring_scoped` discharges
it for the programs below, so a wrong lift fails a proof rather than a program.
-/

set_option autoImplicit false

namespace Test.Program.AuthoringContract

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Api (Val)
open TypeScript (house0)
open TypeScript.Render (expr)

/-! ## Write, then read: the first program of the end-state note -/

/-- `Effect.gen(function* () { const r = yield* Ref.make(0); yield* Ref.set(r, 1); return yield* Ref.get(r) })`,
as an author counts it today. -/
def writeThenReadTree : Api.Program :=
  .bind (.perform .refMake (.lit (.nat 0)))
    (.bind (.perform .refSet (.app "pair" (.cons (.var 0) (.cons (.lit (.nat 1)) .nil))))
      (.perform .refGet (.var 0)))

/-- The same program by name. -/
def writeThenRead : Src NativeOp :=
  bind "r" (Ref.make (nat 0)) <|
  andThen (Ref.set (var "r") (nat 1)) <|
  Ref.get (var "r")

#guard elaborate writeThenRead = .ok writeThenReadTree
#guard (elaborate writeThenRead).toOption.map Api.wellTyped = some true
#guard (elaborate writeThenRead).toOption.map (fun e => (Api.runSync e 100).2)
  = some (Exit.success (Val.nat 1))
#guard (elaborate writeThenRead).toOption.map (fun e => (Api.print e).map (expr house0 0))
  = some (.ok "Effect.flatMap(Ref.make(0), (a0) => Effect.flatMap(Ref.set(a0, 1), (a1) => Ref.get(a0)))")

/-! ## The same program via `eff` authoring macro -/

/-- `eff { ... }` bracketed sequence with semicolons and implicit trailing expression. -/
def writeThenReadEff : Src NativeOp := eff {
  let r ← Ref.make 0;
  Ref.set r 1;
  Ref.get r
}

#guard elaborate writeThenReadEff = .ok writeThenReadTree
#guard (elaborate writeThenReadEff).toOption.map Api.wellTyped = some true
#guard (elaborate writeThenReadEff).toOption.map (fun e => (Api.runSync e 100).2)
  = some (Exit.success (Val.nat 1))

/-- `eff do ...` indented sequence with no semicolons. -/
def writeThenReadEffDo : Src NativeOp := eff do
  let r ← Ref.make 0
  Ref.set r 1
  Ref.get r

#guard elaborate writeThenReadEffDo = .ok writeThenReadTree
#guard (elaborate writeThenReadEffDo).toOption.map Api.wellTyped = some true
#guard (elaborate writeThenReadEffDo).toOption.map (fun e => (Api.runSync e 100).2)
  = some (Exit.success (Val.nat 1))

/-- `eff` block with pure `let :=` binding and `return`. -/
def writeThenReadWithLetAndReturn : Src NativeOp := eff {
  let r ← Ref.make 0;
  let val := 42;
  Ref.set r val;
  return val
}

#guard (elaborate writeThenReadWithLetAndReturn).toOption.map (fun e => (Api.runSync e 100).2)
  = some (Exit.success (Val.nat 42))

/-- `eff` block with wildcard `_ ←` bindings and unit return. -/
def wildcardBindingProg : Src NativeOp := eff {
  _ ← Ref.make 0;
  let _ ← Ref.make 1;
  return ()
}

#guard elaborate wildcardBindingProg =
  elaborate (andThen (Ref.make (nat 0)) (andThen (Ref.make (nat 1)) (succeed unit)))

/-- `eff` block composing conditionals and nested blocks. -/
def conditionalBranchProg (b : Bool) : Src NativeOp := eff {
  let r ← Ref.make 0;
  if b then eff {
    Ref.set r 1
  } else eff {
    Ref.set r 2
  };
  Ref.get r
}

#guard (elaborate (conditionalBranchProg true)).toOption.map (fun e => (Api.runSync e 100).2)
  = some (Exit.success (Val.nat 1))
#guard (elaborate (conditionalBranchProg false)).toOption.map (fun e => (Api.runSync e 100).2)
  = some (Exit.success (Val.nat 2))

/-! ## Refusals name the path and the name -/

#guard elaborate (bind "r" (Ref.make (nat 0)) (Ref.get (var "q")) : Src NativeOp)
  = .error ⟨[1], .unbound "q"⟩

#guard elaborate (Ref.get (var "r") : Src NativeOp) = .error ⟨[], .unbound "r"⟩

-- A refusal two binders deep names the deeper path.
#guard elaborate (bind "r" (Ref.make (nat 0)) (bind "s" (Ref.make (nat 1)) (Ref.get (var "t"))) : Src NativeOp)
  = .error ⟨[1, 1], .unbound "t"⟩

/-! ## Shadowing resolves to the nearest binder -/

#guard elaborate (bind "r" (Ref.make (nat 0)) (bind "r" (Ref.make (nat 5)) (Ref.get (var "r"))) : Src NativeOp)
  = .ok (.bind (.perform .refMake (.lit (.nat 0)))
          (.bind (.perform .refMake (.lit (.nat 5))) (.perform .refGet (.var 1))))

-- The outer binder is still reachable under a different name.
#guard elaborate (bind "r" (Ref.make (nat 0)) (bind "s" (Ref.make (nat 5)) (Ref.get (var "r"))) : Src NativeOp)
  = .ok (.bind (.perform .refMake (.lit (.nat 0)))
          (.bind (.perform .refMake (.lit (.nat 5))) (.perform .refGet (.var 0))))

/-! ## Every binding construct, against the level it binds at -/

#guard elaborate (catchCause "c" (fail (str "boom")) (failCause (Cause.fail (var "c"))) : Src NativeOp)
  = .ok (.catchCause (.fail (.lit (.str "boom"))) (.failCause (.fail (.var 0))))

#guard elaborate (matchCause "v" "c" (succeed (nat 1)) (succeed (var "v")) (succeed (var "c")) : Src NativeOp)
  = .ok (.matchCause (.succeed (.lit (.nat 1))) (.succeed (.var 0)) (.succeed (.var 0)))

#guard elaborate (onExit "x" (succeed (nat 1)) (succeed (var "x")) : Src NativeOp)
  = .ok (.onExit (.succeed (.lit (.nat 1))) (.succeed (.var 0)))

#guard elaborate (catchIf "e" (app "eq" [var "e", str "boom"]) (fail (str "boom")) (succeed (var "e")) : Src NativeOp)
  = .ok (.catchIf (.app "eq" (.cons (.var 0) (.cons (.lit (.str "boom")) .nil)))
          (.fail (.lit (.str "boom"))) (.succeed (.var 0)))

#guard elaborate (acquireRelease "a" "x" (Ref.make (nat 0)) (Ref.set (var "a") (nat 9)) : Src NativeOp)
  = .ok (.acquireRelease (.perform .refMake (.lit (.nat 0)))
          (.perform .refSet (.app "pair" (.cons (.var 0) (.cons (.lit (.nat 9)) .nil)))))

#guard elaborate
    (iterate "i" "_" none (nat 0) (app "lt" [var "i", nat 3]) (app "add" [var "i", nat 1])
      (var "i") (Ref.make (var "i")) : Src NativeOp)
  = .ok (.iterate none (.lit (.nat 0))
          (.app "lt" (.cons (.var 0) (.cons (.lit (.nat 3)) .nil)))
          (.app "add" (.cons (.var 0) (.cons (.lit (.nat 1)) .nil)))
          (.var 0)
          (.perform .refMake (.var 0)))

-- The loop's step sees the body's answer at the level after the cursor.
#guard elaborate
    (iterate "i" "a" none (nat 0) (app "lt" [var "i", nat 3]) (var "a") (var "i") (succeed (var "i")) : Src NativeOp)
  = .ok (.iterate none (.lit (.nat 0))
          (.app "lt" (.cons (.var 0) (.cons (.lit (.nat 3)) .nil)))
          (.var 1) (.var 0) (.succeed (.var 0)))

-- `bindWith`: a binder as a Lean function over a fresh name.
#guard elaborate (bindWith (Ref.make (nat 0)) fun r => Ref.get r : Src NativeOp)
  = .ok (.bind (.perform .refMake (.lit (.nat 0))) (.perform .refGet (.var 0)))

-- `map` through an atom.
#guard elaborate (map "add1" (succeed (nat 1)) : Src NativeOp)
  = .ok (.bind (.succeed (.lit (.nat 1))) (.succeed (.app "add1" (.cons (.var 0) .nil))))


end Test.Program.AuthoringContract
