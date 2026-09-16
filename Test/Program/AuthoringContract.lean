import Effect4.Api
import Effect4.Program.Authoring.Sugar
import Effect4.Laws.Program.Authoring.Sugar
import Effect4.Program.Authoring.Forms
import Effect4.Laws.Program.Authoring.Forms
import Test.Program.LayerSharingContract

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
    (whileLoop "i" "_" (nat 0) (app "lt" [var "i", nat 3]) (app "add" [var "i", nat 1])
      (Ref.make (var "i")) : Src NativeOp)
  = .ok (.whileLoop (.lit (.nat 0))
          (.app "lt" (.cons (.var 0) (.cons (.lit (.nat 3)) .nil)))
          (.app "add" (.cons (.var 0) (.cons (.lit (.nat 1)) .nil)))
          (.perform .refMake (.var 0)))

-- The loop's step sees the body's answer at the level after the cursor.
#guard elaborate
    (whileLoop "i" "a" (nat 0) (app "lt" [var "i", nat 3]) (var "a") (succeed (var "i")) : Src NativeOp)
  = .ok (.whileLoop (.lit (.nat 0))
          (.app "lt" (.cons (.var 0) (.cons (.lit (.nat 3)) .nil)))
          (.var 1) (.succeed (.var 0)))

-- `bindWith`: a binder as a Lean function over a fresh name.
#guard elaborate (bindWith (Ref.make (nat 0)) fun r => Ref.get r : Src NativeOp)
  = .ok (.bind (.perform .refMake (.lit (.nat 0))) (.perform .refGet (.var 0)))

-- `map` through an atom.
#guard elaborate (map "add1" (succeed (nat 1)) : Src NativeOp)
  = .ok (.bind (.succeed (.lit (.nat 1))) (.succeed (.app "add1" (.cons (.var 0) .nil))))

/-! ## A real service, a real layer, shared: the layer-sharing battery's `once` and `twice` by name -/

open Test.Program.LayerSharingContract (kA kRef once twice)

/-- A child started at once, not a daemon, inheriting the mask. -/
def immediateChild : Effect4.Supervision.ForkOptions :=
  { startImmediately := true, daemon := false, maskMode := .inherit }

/-- The counter layer: it takes the `Ref` service, increments it, and provides `kA` as 5. -/
def counter : LayerSrc NativeOp :=
  Layer.effect kA <|
    bind "ref" (service kRef) <|
    andThen (Ref.update .incr (var "ref")) <|
    succeed (nat 5)

/-- The main program provides the `Ref`, provides `Counter` once and again by reference,
reads the service, then reads the `Ref`. -/
def onceByName : Module NativeOp :=
  { layers := [("Counter", counter)]
    main :=
      bind "r" (Ref.make (nat 0)) <|
      provideService kRef (var "r") <|
      bind "n"
        (provideLayer (Layer.ref "Counter") false <|
          provideLayer (Layer.ref "Counter") false <|
          service kA) <|
      Ref.get (var "r") }

def twiceByName : Module NativeOp :=
  { layers := [("Counter", counter)]
    main :=
      bind "r" (Ref.make (nat 0)) <|
      provideService kRef (var "r") <|
      bind "n"
        (provideLayer (Layer.ref "Counter") false <|
          provideLayer (Layer.ref "Counter") false <|
          provideLayer (Layer.ref "Counter") false <|
          service kA) <|
      Ref.get (var "r") }

-- The first use in program order holds the term; every later use is a reference to that
-- path, which is exactly the battery's `refTarget`.
#guard elaborateModule onceByName = .ok once
#guard elaborateModule twiceByName = .ok twice
#guard (elaborateModule twiceByName).toOption.map Api.wellTyped = some true

-- A layer nobody declared refuses at the site that names it.
#guard elaborateModule
    ({ layers := [], main := provideLayer (Layer.ref "Counter") false (service kA) } : Module NativeOp)
  = .error ⟨[0], .unboundLayer "Counter"⟩

-- Two declarations under one name refuse.
#guard elaborateModule
    ({ layers := [("Counter", counter), ("Counter", counter)], main := succeed (nat 0) } : Module NativeOp)
  = .error ⟨[], .duplicateLayer "Counter"⟩

-- A declared layer nobody uses is dropped.
#guard elaborateModule ({ layers := [("Counter", counter)], main := succeed (nat 0) } : Module NativeOp)
  = .ok (.succeed (.lit (.nat 0)))

/-! ## A fork, a scope, and an asynchronous row through `perform` -/

/-- Fork a child that awaits a deferred, complete it, join the child. -/
def rendezvous : Src NativeOp :=
  bind "d" Authoring.Deferred.make <|
  bind "f" (withFiber (Action.fork (Authoring.Deferred.await (var "d")) immediateChild)) <|
  andThen (Authoring.Deferred.succeed (var "d") (nat 7)) <|
  awaitFiber (var "f") .joinEffect

#guard (elaborate rendezvous).toOption.map Api.wellTyped = some true

/-! ## The derived forms by name: `Effect.tap` and `Effect.ensuring` are what they print as -/

/-- `Effect.tap(Ref.make(0), (r) => Ref.set(r, 1))`, then `Effect.ensuring` a read. -/
def tapped : Src NativeOp :=
  Forms.ensuring
    (Forms.tapContinuation "r" (Ref.make (nat 0)) (Ref.set (var "r") (nat 1)))
    (succeed (nat 9))

#guard elaborate tapped
  = .ok (.onExit
      (.bind (.perform .refMake (.lit (.nat 0)))
        (.bind (.perform .refSet (.app "pair" (.cons (.var 0) (.cons (.lit (.nat 1)) .nil))))
          (.succeed (.var 0))))
      (.succeed (.lit (.nat 9))))
#guard (elaborate tapped).toOption.map Api.wellTyped = some true
-- The canonical image (`Api.print`) spells the constructors; the forms are what the styled
-- route recognizes them back into (`Codegen/Forms`), and the generated module pins each
-- form's reading against that expansion.
#guard (elaborate tapped).toOption.map (fun e => (Api.print e).map (expr house0 0))
  = some (.ok "Effect.onExit(Effect.flatMap(Ref.make(0), (a0) => Effect.flatMap(Ref.set(a0, 1), (a1) => Effect.succeed(a0))), (a0) => Effect.succeed(9))")

theorem tapped_scoped : Src.Scoped tapped := by
  unfold tapped; authoring_scoped

/-! ## Scope safety by construction: the named programs are scoped, and so are their trees -/

theorem writeThenRead_scoped : Src.Scoped writeThenRead := by
  unfold writeThenRead; authoring_scoped

theorem counter_scoped : LayerSrc.Scoped counter := by
  unfold counter; authoring_scoped

theorem rendezvous_scoped : Src.Scoped rendezvous := by
  unfold rendezvous; authoring_scoped

#guard (elaborate writeThenRead).toOption.map (Eff.scopedAt 0) = some true
#guard (elaborate rendezvous).toOption.map (Eff.scopedAt 0) = some true
#guard (elaborateModule twiceByName).toOption.map (Eff.scopedAt 0) = some true

#print axioms writeThenRead_scoped
#print axioms rendezvous_scoped
#print axioms Effect4.Program.Authoring.elaborate_scoped
#print axioms Effect4.Program.Authoring.Node.scopedAt_child
#print axioms Effect4.Program.Authoring.elaborate
#print axioms Effect4.Program.Authoring.elaborateModule
#print axioms Effect4.Program.Authoring.bind
#print axioms Effect4.Program.Authoring.var

end Test.Program.AuthoringContract
