import Test.Program.MaskData
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
(`tools/Drivers/Truth.lean`), and `Test/Program/MaskEngine.lean` binds the engine's fixture.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Test.Program.MaskContract

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring

#guard exitOf s1 = some (.success (.list [open_, masked]))
-- The image is the frame `ctor 7` over the bit, and it is no Boolean.
#guard open_ = .ctor 7 [.bool true] && masked = .ctor 7 [.bool false]
#guard open_ != .bool true && masked != .bool false

#guard exitOf s2 = some (.success (.list [.bool true, .nat 1]))

-- After the interrupt the log still holds the first mark; at the end it holds 1 + 10 + 7.
#guard exitOf s3 = some (.success (.list [.nat 1, .bool true, .nat 18]))

#guard exitOf s4 = some (.success (.list [.bool true, .nat 111]))

#guard exitOf (s5 false) = some (.success (.list [.nat 1, .bool true, .nat 18]))
#guard exitOf (s5 true) = some (.success (.list [.nat 1, .bool true, .nat 1]))

#guard exitOf s6 = some (.success (.list [.bool true, .nat 1]))

#guard verdict (mk s6Masked) = "built" && exitOf s6Masked = none

#guard exitOf s7 = some (.success (.list [open_, open_, open_, masked, masked]))

#guard verdict (mk s7Regions) = "built"
#guard exitOf s7Regions = some (.success (.list [masked, masked, masked, masked, open_, open_]))

#guard exitOf s9 = some (.success (.list [masked, open_, open_, masked, masked]))

#guard exitOf s10 = some (.success (.list [open_, masked, open_]))

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

-- The checker refuses the budget's provision, so the programs are raw.
#guard verdict (mk (cut false 12)) = "typing: serviceUnknown"

-- The budget's provision enters through the masked provider region (decisions row 349). Its
-- entry is five operations longer than the unmasked one, so every cut below is five later.
-- An interruptible caller. The child's operations 15 to 18 are the form's entry: the `bind`,
-- the getter, the getter's answer through its restoring frame, and the body's mask. A cut
-- before each of them ends the form before its body. Operation 17 is the first checkpoint of
-- F6, inside the getter: the fiber is masked there, the interrupt stays pending, and the
-- getter's restoring frame fails the fiber. Operation 18 is the second: between the getter
-- and the body's mask the fiber is interruptible again.
#guard (List.range 4).map (fun i => cutLog (cut false (15 + i))) =
  [some 100, some 100, some 100, some 100]
-- From operation 19 the body is masked: it runs to its end, and the fiber is interrupted after.
#guard (List.range 5).all fun i => cutLog (cut false (19 + i)) = some 111
-- A cut before the first mark is an interrupt before the form.
#guard (List.range 12).all fun i => cutLog (cut false (3 + i)) = some 0

-- A masked caller still enters the body, at every cut after its own mask: no log is `100`.
#guard (List.range 11).all fun i => cutLog (cut true (14 + i)) = some 111
#guard (List.range 11).all fun i => cutLog (cut true (3 + i)) = some 0

-- Open (row 349): at budget 2 the park falls inside the provision's masked entry, and the run
-- reaches the command fuel; the unmasked entry reached the interrupt before the form there.
-- A live frontier, not a refusal.
#guard ((rawOf (cut false 2)).map fun p => (Api.run p fuel).outcome) = some .frontier

#guard exitOf (addressed id) = some (.success (.nat 142))
#guard exitOf (addressed openSite) = some (.success (.nat 142))
#guard exitOf (addressed maskedSite) = some (.success (.nat 142))
-- Red control: the answer reads the outer variable, under each site.
#guard exitOf (addressed openSite 7) = some (.success (.nat 108))
#guard exitOf (addressed maskedSite 7) = some (.success (.nat 108))

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

-- A host answer at the reserved target: the table is refused, at the column, at any depth.
#guard admitSig ⟨[answerRow Ty.maskRestore], [], []⟩ = .error (.row 0 (.internalHandle "answer"))
#guard admitSig ⟨[answerRow (.option Ty.maskRestore)], [], []⟩ =
  .error (.row 0 (.internalHandle "answer"))
#guard admitSig ⟨[{ answerRow .unit with error := .list Ty.maskRestore }], [], []⟩ =
  .error (.row 0 (.internalHandle "error"))
-- Red control: the same row at `nat` is admitted.
#guard admitSig ⟨[answerRow .nat], [], []⟩ = .ok ()

-- An external allocation may not take the target, and a host number is no saved value.
#guard !externalHandleTarget Ty.maskRestoreTarget
#guard externalValue [] Ty.maskRestore [] (.nat 0) = none
#guard externalValue [] Ty.maskRestore [] (.bool true) = none

-- A service may not carry the saved state in the first profile.
#guard admitSig ⟨[], [(⟨⟨40⟩, ⟨40⟩⟩, Ty.maskRestore)], []⟩ = .error (.service 0 .nonFlatCarrier)
-- Red control: a scope handle is a flat carrier, at the same key.
#guard admitSig ⟨[], [(⟨⟨40⟩, ⟨40⟩⟩, Ty.scope)], []⟩ = .ok ()

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

-- Every run has a text, and no run finishes at the engine test's small fuel.
#guard fixtureText.isSome
#guard engineRuns.all fun (_, src) =>
  (buildOf (mk src)).any fun p => (Api.run p 3).outcome != .finished && (Api.run p 3).exit.isNone

end Test.Program.MaskContract
