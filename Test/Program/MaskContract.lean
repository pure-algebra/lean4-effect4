import Effect4.Api
import Effect4.Api.Author
import Effect4.Program.Authoring.Loops
import Effect4.Program.Authoring.Mask
import Effect4.Store.Domain.ProgramWire

/-!
# The mask that restores: the acceptance fixture (decisions rows 227, 239 and 244 to 246)

Finite controls. Each `#guard` checks one input on one schedule of the Lean machine, and no
guard is a law. The laws are in `src/Effect4/Laws/Program/Typed/Mask.lean`,
`src/Effect4/Laws/Codegen/Mask.lean` and the modules they name; `Test/Program/MaskClaims.lean`
prints their axioms and the standing of the five registry claims.

The scenarios are the host probe's
(`docs/research/2026-10-05-claude-lead/mask-probes/mask-form.ts`, the mask's second note, F6
and F7). Each answer here is the answer that the probe recorded on rc.112 and on 4.0.1, in
the machine's values. The probe reads a flag as a Boolean. The language has no bare read of
the flag, so a scenario reads it with the getter, and the answer is a saved image.

What this file holds:

- S1 to S10, on the machine, with the mask written by the surface's builders
  (`src/Effect4/Program/Authoring/Mask.lean`);
- S8, the operation counter of the plain forms, read off the root fiber;
- the two cuts of F6, as programs: a child whose operation budget parks it inside the getter,
  or between the getter and the body's mask;
- the control of F3 for the body's address: two bodies under each saved choice;
- the refusals: a Boolean as a saved value, a saved value as a Boolean, and the three refusals
  of the reserved target;
- a restore under a masked caller, which is the identity.

It establishes no agreement with a target. The truth lane runs two of the programs on the pin
(`harness/truth/Truth.lean`), and `Test/Program/MaskEngine.lean` binds the engine's fixture.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Test.Program.MaskContract

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring

/-! ## The run -/

def mk (src : Src NativeOp) : Module NativeOp := { main := src }

/-- The run's budget, and the engine fixture's. -/
def fuel : Nat := 20000

/-- The program that the one build admits: elaborated, typed and admitted. -/
def buildOf (m : Module NativeOp) : Option Api.Program :=
  (Effect4.Api.Author.build m).toOption.map (·.program)

/-- The root's exit on the ordinary run: the root evaluated, then every dispatcher flushed. -/
def exitOfModule (m : Module NativeOp) : Option ExitV :=
  (buildOf m).bind fun p => (Api.run p fuel).exit

def exitOf (src : Src NativeOp) : Option ExitV := exitOfModule (mk src)

/-- The build's verdict, by the refusal's kind and its reason's head. -/
def verdict (m : Module NativeOp) : String :=
  match Effect4.Api.Author.build m with
  | .ok _ => "built"
  | .error (.scope _) => "scope"
  | .error (.typing r) => "typing: " ++ r.reason.head
  | .error (.admission _) => "admission"
  | .error (.serviceCarrier _ _ _) => "serviceCarrier"

/-- The two images of the saved bit (`Val.savedMask`, `src/Effect4/Machine/Alphabets.lean`). -/
def open_ : Val := Val.savedMask true
def masked : Val := Val.savedMask false

/-! ## The scenarios' parts -/

/-- The getter: it answers the image of the fiber's flag at its entry. -/
def flag : Src NativeOp := withFiber Action.getInterruptible

/-- One mark of a run's log: the cell's number grows by `k`. -/
def mark (log k : TermSrc) : Src NativeOp :=
  Ref.update "l" (app "add" [var "l", k]) log

/-- A masked child that starts at once: the fork of S6. -/
def maskedChild : Effect4.Supervision.ForkOptions := ⟨true, false, .uninterruptible⟩

/-! ## S1: what the getter answers -/

def s1 : Src NativeOp := eff do
  let opened ← flag
  let closed ← uninterruptible flag
  return tuple [opened, closed]

#guard exitOf s1 = some (.success (.list [open_, masked]))
-- The image is the frame `ctor 7` over the bit, and it is no Boolean.
#guard open_ = .ctor 7 [.bool true] && masked = .ctor 7 [.bool false]
#guard open_ != .bool true && masked != .bool false

/-! ## S2: an interruptible caller is interrupted during a wait at a restore site

The fiber exits interrupted, and the body does not continue: the log holds the first mark
only. -/

def s2 : Src NativeOp := eff do
  let d ← Deferred.make .nat .never
  let log ← Ref.make (nat 0)
  let f ← fork (uninterruptibleMaskWith fun restore => eff do
    let _ ← mark log (nat 1)
    let _ ← restore (Deferred.await d)
    mark log (nat 10))
  let _ ← withFiber (Action.interrupt f)
  let e ← await f
  let l ← Ref.get log
  return tuple [app "causeIsInterrupt" [e], l]

#guard exitOf s2 = some (.success (.list [.bool true, .nat 1]))

/-! ## S3: a masked caller is interrupted during the same wait

The wait continues, the value arrives, and the fiber is interrupted when the outer mask ends.
The interruptor is a helper fiber, because an interrupt waits for its target. -/

def s3 : Src NativeOp := eff do
  let d ← Deferred.make .nat .never
  let log ← Ref.make (nat 0)
  let f ← fork (uninterruptible (uninterruptibleMaskWith fun restore => eff do
    let _ ← mark log (nat 1)
    let v ← restore (Deferred.await d)
    mark log (app "add" [nat 10, v])))
  let stop ← fork (withFiber (Action.interrupt f))
  let still ← Ref.get log
  let _ ← Deferred.succeed d (nat 7)
  let e ← await f
  let _ ← await stop
  let l ← Ref.get log
  return tuple [still, app "causeIsInterrupt" [e], l]

-- After the interrupt the log still holds the first mark; at the end it holds 1 + 10 + 7.
#guard exitOf s3 = some (.success (.list [.nat 1, .bool true, .nat 18]))

/-! ## S4: an interruptible caller is interrupted with no restore site

The body runs to its end, and the fiber is then interrupted. -/

def s4 : Src NativeOp := eff do
  let log ← Ref.make (nat 0)
  let f ← fork (uninterruptibleMaskWith fun _restore => eff do
    let _ ← mark log (nat 1)
    let _ ← yieldNow 0
    let _ ← mark log (nat 10)
    let _ ← yieldNow 0
    mark log (nat 100))
  let stop ← fork (withFiber (Action.interrupt f))
  let e ← await f
  let _ ← await stop
  let l ← Ref.get log
  return tuple [app "causeIsInterrupt" [e], l]

#guard exitOf s4 = some (.success (.list [.bool true, .nat 111]))

/-! ## S5: nested masks

A wait under the inner restore is not interruptible: the inner mask's caller is the outer
mask's body. A wait under the outer restore is. -/

def s5 (useOuter : Bool) : Src NativeOp := eff do
  let d ← Deferred.make .nat .never
  let log ← Ref.make (nat 0)
  let f ← fork (uninterruptibleMaskWith fun outer => uninterruptibleMaskWith fun inner => eff do
    let _ ← mark log (nat 1)
    let v ← (if useOuter then outer else inner) (Deferred.await d)
    mark log (app "add" [nat 10, v]))
  let stop ← fork (withFiber (Action.interrupt f))
  let still ← Ref.get log
  let _ ← Deferred.succeed d (nat 7)
  let e ← await f
  let _ ← await stop
  let l ← Ref.get log
  return tuple [still, app "causeIsInterrupt" [e], l]

#guard exitOf (s5 false) = some (.success (.list [.nat 1, .bool true, .nat 18]))
#guard exitOf (s5 true) = some (.success (.list [.nat 1, .bool true, .nat 1]))

/-! ## S6: a restore that leaves its mask and runs in a masked child

The mask answers its saved value. A masked child applies it after the mask ended, and the
child's wait is interruptible. -/

def s6 : Src NativeOp := eff do
  let d ← Deferred.make .nat .never
  let log ← Ref.make (nat 0)
  let kept ← uninterruptibleMask "r" (succeed (var "r"))
  let child ← fork (eff do
      let _ ← mark log (nat 1)
      let _ ← restore kept (Deferred.await d)
      mark log (nat 10))
    maskedChild
  let stop ← fork (withFiber (Action.interrupt child))
  let e ← await child
  let _ ← await stop
  let l ← Ref.get log
  return tuple [app "causeIsInterrupt" [e], l]

#guard exitOf s6 = some (.success (.list [.bool true, .nat 1]))

/-- S6's red control: the same child with no restore site. Its wait is masked, so the
interrupt does not end it, and the run does not finish. -/
def s6Masked : Src NativeOp := eff do
  let d ← Deferred.make .nat .never
  let log ← Ref.make (nat 0)
  let child ← fork (eff do
      let _ ← mark log (nat 1)
      let _ ← Deferred.await d
      mark log (nat 10))
    maskedChild
  let stop ← fork (withFiber (Action.interrupt child))
  let e ← await child
  let _ ← await stop
  let l ← Ref.get log
  return tuple [app "causeIsInterrupt" [e], l]

#guard verdict (mk s6Masked) = "built" && exitOf s6Masked = none

/-! ## S7: the caller's flag after each exit of the form

After a success, a failure and a defect under an interruptible caller, and after a success and
a failure under a masked caller, the flag is what it was. -/

def flagAfter (body : Src NativeOp) : Src NativeOp := eff do
  let _ ← exit (uninterruptibleMaskWith fun _ => body)
  flag

def s7 : Src NativeOp := eff do
  let a ← flagAfter (succeed (nat 1))
  let b ← flagAfter (fail (str "e"))
  let c ← flagAfter (failCause (Cause.die (str "d")))
  let d ← uninterruptible (flagAfter (succeed (nat 1)))
  let e ← uninterruptible (flagAfter (fail (str "e")))
  return tuple [a, b, c, d, e]

#guard exitOf s7 = some (.success (.list [open_, open_, open_, masked, masked]))

/-! ### S7, wider: a body that holds regions of its own

Under a masked caller the form changes no flag and pushes no frame, so its exit flag is what
its body left. No theorem states that flag yet: it is the open part of `saved-mask-restoration`
(`src/Effect4/Laws/Program/Typed/Mask.lean`). Each body below changes the flag inside, by an
`interruptible` region, a restore site or a nested mask, and ends by a success or a failure.
The last two readings are under an interruptible caller, where the form's own frame returns
the flag. -/

/-- The caller's flag after a form whose body takes the restore function. -/
def flagAfterWith (body : (Src NativeOp → Src NativeOp) → Src NativeOp) : Src NativeOp := eff do
  let _ ← exit (uninterruptibleMaskWith body)
  flag

def s7Regions : Src NativeOp := eff do
  let a ← uninterruptible (flagAfterWith fun _ => interruptible (succeed (nat 1)))
  let b ← uninterruptible (flagAfterWith fun r => r (interruptible (succeed (nat 1))))
  let c ← uninterruptible (flagAfterWith fun _ =>
    uninterruptibleMaskWith fun inner => inner (fail (str "e")))
  let d ← uninterruptible (flagAfterWith fun _ => interruptible (fail (str "e")))
  let e ← flagAfterWith fun r => r (uninterruptible (succeed (nat 1)))
  let f ← flagAfterWith fun r => r (uninterruptibleMaskWith fun inner => inner (fail (str "e")))
  return tuple [a, b, c, d, e, f]

#guard verdict (mk s7Regions) = "built"
#guard exitOf s7Regions = some (.success (.list [masked, masked, masked, masked, open_, open_]))

/-! ## S9: the flag at five places of a body

False in the body. True in an `interruptible` region of the body. True in a restore site.
False in an `uninterruptible` region inside that site. False in a restore site under a masked
caller. -/

def s9 : Src NativeOp := eff do
  let a ← uninterruptibleMaskWith fun _ => flag
  let b ← uninterruptibleMaskWith fun _ => interruptible flag
  let c ← uninterruptibleMaskWith fun r => r flag
  let d ← uninterruptibleMaskWith fun r => r (uninterruptible flag)
  let e ← uninterruptible (uninterruptibleMaskWith fun r => r flag)
  return tuple [a, b, c, d, e]

#guard exitOf s9 = some (.success (.list [masked, open_, open_, masked, masked]))

/-! ## S10: a saved value applied after its mask

A false choice leaves an interruptible fiber interruptible and a masked fiber masked. A true
choice makes a masked fiber's region interruptible. -/

def s10 : Src NativeOp := eff do
  let fromMasked ← uninterruptible (uninterruptibleMask "r" (succeed (var "r")))
  let fromOpen ← uninterruptibleMask "r" (succeed (var "r"))
  let a ← restore fromMasked flag
  let b ← uninterruptible (restore fromMasked flag)
  let c ← uninterruptible (restore fromOpen flag)
  return tuple [a, b, c]

#guard exitOf s10 = some (.success (.list [open_, masked, open_]))

/-! ## S8: the operation counter of the plain forms

The note's F6 reads the fiber's operation counter on the target. The machine counts the same
iterations (`RunFiber.currentOpCount`, `Machine/Fibers.lean`), read here off the root fiber
when the run has finished. Each number is the note's:

- the getter spends 2, under either caller;
- a restore site whose saved value is true spends 1, and its body's;
- a restore site whose saved value is false spends its body's, and none of its own;
- the printed form around `succeed` spends 5, where the native mask spends 2. -/

/-- The root fiber's operation counter at the end of the ordinary run. -/
def opsOf (src : Src NativeOp) : Option Nat :=
  (buildOf (mk src)).bind fun p =>
    ((Api.run p fuel).machine.fiber? Api.root).map (·.currentOpCount)

def zero : Src NativeOp := succeed (nat 0)

-- The base: a bare `succeed`, and `uninterruptible` over it.
#guard opsOf zero = some 1 && opsOf (uninterruptible zero) = some 2
-- The getter: 2, and 2 more under a masked caller's own step.
#guard opsOf flag = some 2 && opsOf (uninterruptible flag) = some 3
-- The printed form around `succeed`: 5. Under a masked caller: the caller's step, and 5.
#guard opsOf (uninterruptibleMaskWith fun _ => zero) = some 5
#guard opsOf (uninterruptible (uninterruptibleMaskWith fun _ => zero)) = some 6
-- A restore site at a true bit: 1 more than its body.
#guard opsOf (uninterruptibleMaskWith fun r => r zero) = some 6
-- A restore site at a false bit: no step of its own.
#guard opsOf (uninterruptible (uninterruptibleMaskWith fun r => r zero)) = some 6
-- Red control: the two sites differ from `interruptible` by nothing at a true bit, and by one
-- step at a false bit, where `interruptible` would push its own frame.
#guard opsOf (uninterruptibleMaskWith fun _ => interruptible zero) = some 6
#guard opsOf (uninterruptible (uninterruptibleMaskWith fun _ => interruptible zero)) = some 7

/-! ## The two cuts of F6: the entry's checkpoints

The printed form has checkpoints at its entry that the native mask does not have. A child
runs the form after a first mark, under an operation budget `k`: it parks before its
operation `k`, and a helper interrupts it there. The log then says where the cut fell:

- `0`: before the first mark;
- `100`: after the first mark and before the body, so the form ended before its body;
- `111`: the body ran to its end, and the fiber was interrupted after the mask.

**These programs are raw.** The budget is the reserved reference `MaxOpsBeforeYield`
(`Env.maxOpsKey`), which the signature types at no carrier, so the checker refuses its
provision (`serviceUnknown`). `Api.run` is the unchecked run, and it reads the budget off the
context as the machine does (`RunInterp.budgetOf`). No printed program sets this budget on a
target: the cuts on the pin are Codex's runs, with a dispatcher of their own (the note's F6). -/

/-- The elaborated program, not typed. -/
def rawOf (src : Src NativeOp) : Option Api.Program := (elaborateModule (mk src)).toOption

/-- A body under an operation budget: the fiber parks before its operation `k` of an entry. -/
def budgeted (k : Nat) (body : Src NativeOp) : Src NativeOp :=
  provideService Env.maxOpsKey (nat k) body

/-- The form after a first mark. Its body makes two marks and has no restore site. -/
def formAfterMark (log : TermSrc) : Src NativeOp := eff do
  let _ ← mark log (nat 100)
  uninterruptibleMaskWith fun _restore => eff do
    let _ ← mark log (nat 1)
    mark log (nat 10)

/-- The form in a child with budget `k`, under either caller; a helper interrupts the child
where it parks. -/
def cut (maskedCaller : Bool) (k : Nat) : Src NativeOp := eff do
  let log ← Ref.make (nat 0)
  let f ← fork (budgeted k ((if maskedCaller then uninterruptible else id) (formAfterMark log)))
  let stop ← fork (withFiber (Action.interrupt f))
  let e ← await f
  let _ ← await stop
  let l ← Ref.get log
  return tuple [app "causeIsInterrupt" [e], l]

/-- The log of a cut run whose child was interrupted. -/
def cutLog (src : Src NativeOp) : Option Nat :=
  match (rawOf src).bind fun p => (Api.run p fuel).exit with
  | some (.success (.list [.bool true, .nat l])) => some l
  | _ => none

-- The checker refuses the budget's provision, so the programs are raw.
#guard verdict (mk (cut false 12)) = "typing: serviceUnknown"

-- An interruptible caller. The child's operations 10 to 13 are the form's entry: the `bind`,
-- the getter, the getter's answer through its restoring frame, and the body's mask. A cut
-- before each of them ends the form before its body. Operation 12 is the first checkpoint of
-- F6, inside the getter: the fiber is masked there, the interrupt stays pending, and the
-- getter's restoring frame fails the fiber. Operation 13 is the second: between the getter
-- and the body's mask the fiber is interruptible again.
#guard (List.range 4).map (fun i => cutLog (cut false (10 + i))) =
  [some 100, some 100, some 100, some 100]
-- From operation 14 the body is masked: it runs to its end, and the fiber is interrupted after.
#guard (List.range 5).all fun i => cutLog (cut false (14 + i)) = some 111
-- A cut before the first mark is an interrupt before the form.
#guard (List.range 8).all fun i => cutLog (cut false (2 + i)) = some 0

-- A masked caller still enters the body, at every cut after its own mask: no log is `100`.
#guard (List.range 11).all fun i => cutLog (cut true (9 + i)) = some 111
#guard (List.range 7).all fun i => cutLog (cut true (2 + i)) = some 0

/-! ## The control of F3: the body's address

A restore site's body is child 0 of its node. A body that only succeeds hides a wrong address,
so each saved choice stands around a `bind` that reads an outer variable and then performs an
operation. A second body holds a fork and a layer used at two sites, because both resolve
program paths. Each site answers what the body answers alone. -/

/-- A restore site of an interruptible caller's mask: the saved choice is true. -/
def openSite (body : Src NativeOp) : Src NativeOp :=
  uninterruptibleMaskWith fun restore => restore body

/-- A restore site of a masked caller's mask: the saved choice is false. -/
def maskedSite (body : Src NativeOp) : Src NativeOp :=
  uninterruptible (uninterruptibleMaskWith fun restore => restore body)

/-- The first body: it reads an outer variable, then updates a cell and reads it. -/
def outerBody (outer cell : TermSrc) : Src NativeOp := eff do
  let y ← succeed (app "add" [outer, nat 1])
  let _ ← Ref.update "c" (app "add" [var "c", y]) cell
  Ref.get cell

def addressed (site : Src NativeOp → Src NativeOp) (outer : Nat := 41) : Src NativeOp := eff do
  let x ← succeed (nat outer)
  let cell ← Ref.make (nat 100)
  site (outerBody x cell)

#guard exitOf (addressed id) = some (.success (.nat 142))
#guard exitOf (addressed openSite) = some (.success (.nat 142))
#guard exitOf (addressed maskedSite) = some (.success (.nat 142))
-- Red control: the answer reads the outer variable, under each site.
#guard exitOf (addressed openSite 7) = some (.success (.nat 108))
#guard exitOf (addressed maskedSite 7) = some (.success (.nat 108))

/-- The counter service, the cell it counts in, and the layer that builds it: it bumps the
cell and provides `5` (`Test/Program/AuthorContract.lean`, E1). -/
def Counter : ServiceDef := { key := ⟨⟨4⟩, ⟨4⟩⟩, carrier := .nat }
def TheRef : ServiceDef := { key := ⟨⟨6⟩, ⟨7⟩⟩, carrier := .refOf .nat }
def counter : LayerSrc NativeOp := Counter.layer <| eff do
  let ref ← TheRef.use
  Ref.update "n" (app "succ" [var "n"]) ref
  return 5

/-- The second body: a fork that is joined, and the layer at two sites. The second site is a
reference to the first, by its path in the program. -/
def forkAndLayer : Src NativeOp := eff do
  let child ← fork (succeed (nat 2))
  let a ← join child
  let b ← provide (Layer.ref "Counter") (provide (Layer.ref "Counter") Counter.use)
  return app "add" [a, b]

def layered (site : Src NativeOp → Src NativeOp) : Module NativeOp :=
  { services := [Counter, TheRef]
    layers := [("Counter", counter)]
    main := eff do
      let r ← Ref.make 0
      TheRef.give r <| eff do
        let got ← site forkAndLayer
        let built ← Ref.get r
        return tuple [got, built] }

-- Each site answers `2 + 5`, and the layer is built once.
#guard exitOfModule (layered id) = some (.success (.list [.nat 7, .nat 1]))
#guard exitOfModule (layered openSite) = some (.success (.list [.nat 7, .nat 1]))
#guard exitOfModule (layered maskedSite) = some (.success (.list [.nat 7, .nat 1]))
-- The reference's target is the first site's path. Under a restore site both paths run through
-- the mask's `bind` at child 1, the body's mask at child 0 and the restore node at child 0.
#guard (buildOf (layered id)).map (·.refSites []) =
  some [([1, 0, 0, 1, 1, 0, 1, 0], [1, 0, 0, 1, 1, 0, 0])]
#guard (buildOf (layered openSite)).map (·.refSites []) =
  some [([1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0], [1, 0, 0, 1, 0, 0, 1, 1, 0, 0])]

/-! ## The refusals -/

-- A Boolean used as a saved value: refused at the restore node, by the checker's own reason.
#guard verdict (mk (restore (bool true) (succeed (nat 1)))) = "typing: maskRestoreExpected"
-- A saved value used as a Boolean: refused where a Boolean is asked.
#guard verdict (mk (eff do
  let saved ← flag
  ifElse saved (succeed (nat 1)) (succeed (nat 2)))) = "typing: predicateNotBool"
-- Red control: the same two programs with a value of the right type are built.
#guard verdict (mk (eff do
  let saved ← flag
  restore saved (succeed (nat 1)))) = "built"
#guard verdict (mk (ifElse (bool true) (succeed (nat 1)) (succeed (nat 2)))) = "built"

-- The image's two red controls, at the shape check: a Boolean does not fit the saved state's
-- type, and an image does not fit `bool`.
#guard Val.hasTy (.bool true) Ty.maskRestore [] = false
#guard Val.hasTy open_ .bool [] = false && Val.hasTy masked .bool [] = false
#guard Val.hasTy open_ Ty.maskRestore [] && Val.hasTy masked Ty.maskRestore []
-- No other frame under the image's index fits: a number in the frame, two bits, index 6.
#guard !Val.hasTy (.ctor 7 [.nat 1]) Ty.maskRestore [] &&
  !Val.hasTy (.ctor 7 [.bool true, .bool true]) Ty.maskRestore [] &&
  !Val.hasTy (.ctor 6 [.bool true]) Ty.maskRestore []

/-- A host row that answers at a given type (`E4-HOST-CE-007`'s row shape). -/
def answerRow (answer : Ty) : Row where
  name := "returnSaved"
  spelling := "Host.returnSaved"
  kind := .async
  registration := .external
  request := .unit
  answer := answer
  error := .never
  cite := "decisions row 244"

-- A host answer at the reserved target: the table is refused, at the column, at any depth.
#guard admitSig ⟨[answerRow Ty.maskRestore], []⟩ = .error (.row 0 (.internalHandle "answer"))
#guard admitSig ⟨[answerRow (.option Ty.maskRestore)], []⟩ =
  .error (.row 0 (.internalHandle "answer"))
#guard admitSig ⟨[{ answerRow .unit with error := .list Ty.maskRestore }], []⟩ =
  .error (.row 0 (.internalHandle "error"))
-- Red control: the same row at `nat` is admitted.
#guard admitSig ⟨[answerRow .nat], []⟩ = .ok ()

-- An external allocation may not take the target, and a host number is no saved value.
#guard !externalHandleTarget Ty.maskRestoreTarget
#guard externalValue Ty.maskRestore [] (.nat 0) = none
#guard externalValue Ty.maskRestore [] (.bool true) = none

-- A service may not carry the saved state in the first profile.
#guard admitSig ⟨[], [(⟨⟨40⟩, ⟨40⟩⟩, Ty.maskRestore)]⟩ = .error (.service 0 .nonFlatCarrier)
-- Red control: a scope handle is a flat carrier, at the same key.
#guard admitSig ⟨[], [(⟨⟨40⟩, ⟨40⟩⟩, Ty.scope)]⟩ = .ok ()

/-! ## A restore under a masked caller is the identity

The saved choice of a masked caller is false. Its restore site spends no operation of its own
(S8), it leaves the flag as it is (S9, the fifth reading), and its wait is not interrupted
(S3). One more control: the same site applied under an interruptible caller, after its mask,
leaves that caller interruptible (S10, the first reading). -/

#guard exitOf (uninterruptible (uninterruptibleMaskWith fun r => r flag)) = some (.success masked)
#guard exitOf (uninterruptible (uninterruptibleMaskWith fun r => r (r flag))) = some (.success masked)
#guard exitOf (eff do
  let saved ← uninterruptible flag
  restore saved flag) = some (.success open_)

/-! ## The engine's fixture

The runs that cross to the generated engine (`ocaml/engine/test/mask/`). The writer beside the
engine's test writes `fixtureText`, and `Test/Program/MaskEngine.lean` binds the committed file
to it. -/

/-- The runs of the engine's fixture, by name. -/
def engineRuns : List (String × Src NativeOp) :=
  [("s1", s1), ("s2", s2), ("s3", s3), ("s4", s4), ("s5inner", s5 false), ("s5outer", s5 true),
   ("s6", s6), ("s7", s7), ("s9", s9), ("s10", s10)]

/-- A Boolean, a number or a saved image in the spelling of the engine's `show_val`
(`ocaml/engine/e4_engine.ml`). -/
def showScalar : Val → Option String
  | .bool b => some (toString b)
  | .nat n => some (toString n)
  | .ctor index [.bool b] => some s!"ctor {index} [{b}]"
  | _ => none

/-- A value in the spelling of the engine's `show_val`. The runs answer scalars and flat lists
of them: any other value has no spelling here, and the writer refuses it. -/
def showVal : Val → Option String
  | .list xs => (xs.mapM showScalar).map fun parts => "list[" ++ ",".intercalate parts ++ "]"
  | v => showScalar v

/-- An exit in the spelling of the engine's `show_exit`. Only a success has a spelling here. -/
def showExit : ExitV → Option String
  | .success v => (showVal v).map ("success " ++ ·)
  | .failure _ => none

/-- One run of the fixture: its name, its fuel, its program's bytes and its exit. -/
def runText (name : String) (src : Src NativeOp) : Option String := do
  let program ← buildOf (mk src)
  let exit ← (Api.run program fuel).exit
  let shown ← showExit exit
  pure s!"run {name}\nfuel {fuel}\nprogram {Wire.hexOf program}\nexit {shown}\nend\n"

def fixtureHeader : String :=
  "# GENERATED by ocaml/engine/test/mask/write.lean; do not edit.\n" ++
  "# Write again: lake env lean --run ocaml/engine/test/mask/write.lean\n"

/-- The fixture's whole text. `none` when a run does not build, does not finish, or answers a
value with no spelling. -/
def fixtureText : Option String :=
  (engineRuns.mapM fun (name, src) => runText name src).map fun runs =>
    fixtureHeader ++ String.join runs

-- Every run has a text, and no run finishes at the engine test's small fuel.
#guard fixtureText.isSome
#guard engineRuns.all fun (_, src) =>
  (buildOf (mk src)).any fun p => (Api.run p 3).outcome != .finished && (Api.run p 3).exit.isNone

end Test.Program.MaskContract
