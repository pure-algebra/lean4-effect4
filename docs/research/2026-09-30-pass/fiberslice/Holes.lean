import Research.Pass.FiberSlice.Core

/-! Task 4: once fiber declarations land, is refusing internal handle kinds in host rows still
needed for cells, deferreds, contexts and scopes? Each probe drives the live keyed session
twice: the production route (`submit`, `applyReply`) and the prototype (`submitD`,
`applyReplyD`), whose combined check falls back to `Val.hasTy` for every non-fiber type.
Finite checks, not proofs. Research evidence, outside the Test root. Base `be15b062`. -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Research.Pass.FiberSlice.Holes
open Effect4 Effect4.Machine Effect4.Program Research.Pass.FiberSlice
open Effect4.Api.HostSession (Session Header Call Reply Phase)

def hostRow (answer : Ty) : Row where
  name := "hostAnswer"
  spelling := "Host.answer"
  kind := .async
  registration := .external
  request := .unit
  answer := answer
  error := .never
  cite := "research probe"

/-- The live session: start, evaluate the root to its host call (token `token`), bind, submit
the answer, apply it, flush. The phases of submit, apply and flush, and the root's exit. -/
def live (program : Api.Program) (answer : Ty) (value : Val) (token : Nat) (useNew : Bool) :
    Option (List Phase × Option ExitV) :=
  let table := [hostRow answer]
  let header : Header := ⟨Api.HostSession.version, "holes", "holes", table⟩
  let call : Call := ⟨Api.HostSession.version, "holes", table, 0, Api.root, .external 0, .unit⟩
  let reply : Reply :=
    ⟨Api.HostSession.version, "holes", 0, ⟨Api.root, token⟩, .ofExit (.success value)⟩
  match Api.HostSession.start program table "holes" header 1000 with
  | .error _ => none
  | .ok s0 =>
    let s1 := (Api.HostSession.advance s0 1000 Api.evaluate).session
    let s2 := (Api.HostSession.bindCall s1 call token).session
    let r3 := if useNew then submitD s2 reply else Api.HostSession.submit s2 reply
    let r4 := if useNew then applyReplyD r3.session reply.key 1000
      else Api.HostSession.applyReply r3.session reply.key 1000
    let r5 := Api.HostSession.advance r4.session 1000 Api.flush
    some ([r3.phase, r4.phase, r5.phase], (r5.session.machine.fiber? Api.root).bind (·.exit))

def ask : Api.Program := .perform (.external 0) (.lit .unit)
def applied : List Phase := [.preflight, .applied, .progressed]

/-! ## Contexts: a live hole today, and no fiber declaration closes it

`Val.hasTy v Ty.context` only checks that the value reads back as a context
(`Program/Typed.lean:54`); the services inside are not checked against their keys' static types
(`nativeServiceTy`, decision row 90), which the typed world requires (`ServicesOk`,
`Laws/Program/Typed/Admission.lean:32-34`). A host answering a context can bind a key the
checker types `nat` to a string. -/

/-- A free key whose static type is `nat` (service type code 4, `Native.lean:277-294`). -/
def natKey : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩

def forgedContext : Val :=
  Val.context (Ctx.withServices ((Env.Context.empty : Env.Ctx).addV natKey (.str "forged")))
def honestContext : Val :=
  Val.context (Ctx.withServices ((Env.Context.empty : Env.Ctx).addV natKey (.nat 5)))

/-- Ask the host for a context, install it, read the `nat` service. -/
def contextProgram : Api.Program :=
  .bind ask (.bind (.withFiber (.setContext (.var 0))) (.service natKey))

#guard nativeServiceTy natKey = some .nat
#guard (Api.typeOf contextProgram [hostRow Ty.context]).map (·.answer) = some .nat
#guard Val.hasTy forgedContext Ty.context
-- production and prototype both apply the forged context; the `nat` program returns a string
#guard live contextProgram Ty.context forgedContext 0 false =
  some (applied, some (.success (.str "forged")))
#guard live contextProgram Ty.context forgedContext 0 true =
  some (applied, some (.success (.str "forged")))
#guard live contextProgram Ty.context honestContext 0 true =
  some (applied, some (.success (.nat 5)))

/-- A context clause needs no registry: the services' static types are the key's own data. -/
def servicesFit (v : Val) : Bool :=
  match Val.context? v with
  | none => false
  | some ctx => ctx.services.entries.all fun s =>
    match nativeServiceTy s.key with
    | some ty => Val.hasTy s.valueVal ty
    | none => false

#guard !servicesFit forgedContext
#guard servicesFit honestContext

/-! ## Cells and deferreds: no wrong read today, but the typed value is wrong

Every cell today is made by `refMake : nat → Ref<number>` and every deferred by
`deferredMake : unit → Deferred<number, number>` (`Native.lean:156-199`), so a cell or deferred
handle at its native spelling can only deliver a number. But `Val.hasTy` accepts any cell at
`refOf t` and any promise at `deferredOf a e` whatever `t`, `a`, `e` (`Program/Typed.lean:58-65`),
while the typed world requires the declared cell type (`HandlesFit`, `Admission.lean:41-42`).
No native operation reads `refOf`, so the wrong type is observed where the value leaves: the
program's own result, or a later host call. -/

/-- Make a cell holding 5, ask the host for a `Ref<string>`, return what the host named. -/
def cellProgram : Api.Program :=
  .bind (.perform .refMake (.lit (.nat 5))) (.bind ask (.succeed (.var 1)))

#guard (Api.typeOf cellProgram [hostRow (.refOf .string)]).map (·.answer) = some (.refOf .string)
-- the host names the program's own number cell; both routes apply it and the program's
-- certified `Ref<string>` result is a cell holding a number
#guard live cellProgram (.refOf .string) (Value.cell 0) 0 false =
  some (applied, some (.success (Value.cell 0)))
#guard live cellProgram (.refOf .string) (Value.cell 0) 0 true =
  some (applied, some (.success (Value.cell 0)))

/-- Make a deferred, ask the host for a `Deferred<string, never>`, return what it named. -/
def deferredProgram : Api.Program :=
  .bind (.perform .deferredMake (.lit .unit)) (.bind ask (.succeed (.var 1)))

#guard live deferredProgram (.deferredOf .string .never) (Value.promise 0) 0 false =
  some (applied, some (.success (Value.promise 0)))
#guard live deferredProgram (.deferredOf .string .never) (Value.promise 0) 0 true =
  some (applied, some (.success (Value.promise 0)))

/-- At the native spelling the host can hand back the program's own cell: an alias, not a
type error (every cell holds a number). The program sets the host's cell to 9, then reads its
own cell. -/
def aliasProgram : Api.Program :=
  .bind (.perform .refMake (.lit (.nat 5))) (.bind ask
    (.bind (.perform .refSet (.app "pair" (.cons (.var 1) (.cons (.lit (.nat 9)) .nil))))
      (.perform .refGet (.var 0))))

#guard (Api.typeOf aliasProgram [hostRow NativeOp.refTy]).map (·.answer) = some .nat
#guard live aliasProgram NativeOp.refTy (Value.cell 0) 0 true =
  some (applied, some (.success (.nat 9)))

/-! ### Not every deferred is a number deferred

`memoBuild` allocates a deferred for a layer's build and `memoComplete` completes it with the
build's exit (`Machine/Stores.lean:2003-2023`). So a promise handle at the native spelling
`Deferred<number, number>` can name a layer's deferred, and `deferredAwait`, typed to answer a
number, answers what the layer built. -/

def memoDeferredProgram : Api.Program :=
  .provideLayer (.effect natKey (.succeed (.lit (.nat 7)))) false
    (.bind ask (.perform .deferredAwait (.var 0)))

#guard (Api.typeOf memoDeferredProgram [hostRow NativeOp.deferredTy]).map (·.answer) = some .nat
/-- The root's exit is a success whose value is a service context spine (`ctor 5`), not a
number: the layer's built context. -/
def exitsWithSpine : Option (List Phase × Option ExitV) → Bool
  | some (phases, some (.success (.ctor 5 _))) => phases == applied
  | _ => false
#guard exitsWithSpine (live memoDeferredProgram NativeOp.deferredTy (Value.promise 0) 0 false)
#guard exitsWithSpine (live memoDeferredProgram NativeOp.deferredTy (Value.promise 0) 0 true)
-- the honest counterpart: the program's own number deferred, completed with 3, answers 3
def ownDeferredProgram : Api.Program :=
  .bind (.perform .deferredMake (.lit .unit))
    (.bind (.perform .deferredSucceed (.app "pair" (.cons (.var 0) (.cons (.lit (.nat 3)) .nil))))
      (.bind ask (.perform .deferredAwait (.var 2))))
#guard live ownDeferredProgram NativeOp.deferredTy (Value.promise 0) 0 true =
  some (applied, some (.success (.nat 3)))

/-! ## Scopes: no type parameter, so no typing hole

`Ty.scope` is one handle spelling with no parameter; `Val.hasTy` checks the kind and the
spelling exactly (`Program/Typed.lean:51`), and the typed world has no scope table. A host can
hand back the program's own scope; the program may close it or fork into it. That is authority
(which capabilities a host may pass), not typing. -/

def scopeProgram : Api.Program :=
  .bind (.perform (.scopeMake .sequential) (.lit .unit)) (.bind ask
    (.bind (.exit (.succeed (.lit .unit)))
      (.bind (.withFiber (.closeScope (.var 1) (.var 2))) (.succeed (.lit (.nat 3))))))

#guard (Api.typeOf scopeProgram [hostRow Ty.scope]).map (·.answer) = some .nat
#guard live scopeProgram Ty.scope (Value.scope 0) 0 true =
  some (applied, some (.success (.nat 3)))

/-! ## `unknown`: any handle passes, and no consumer can use it as one

`Val.hasTy v .unknown = true` for every value, handles included. No rule reads a handle at
`unknown`: `awaitFiber` needs `fiberOf` (`fiberTy`, `Typing/Rules.lean:184-186`), and nothing
casts. -/

def unknownAwait : Api.Program := .bind ask (.awaitFiber (.var 0) .joinEffect)

#guard Api.typeOf unknownAwait [hostRow .unknown] = none
#guard Val.hasTy (Value.fiber 0) .unknown && Val.hasTy (Value.memoMap 0) .unknown

/-! ## What the in-tree rows answer

Every in-tree host row answers data or an external handle (path probes, path A, 15 rows): no
row in the tree mentions a context, a cell, a deferred, a scope or a fiber in its answer. -/

end Research.Pass.FiberSlice.Holes
