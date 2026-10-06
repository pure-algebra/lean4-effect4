# QINV progress and LIFT support

The main review cut is `00b160d25d6929ab7ba3aa19cc00fa6fdcfa9674`.
The comparison base is `38837c5fe083543f2ac9110ac3dfc8b38fda2bed`.
No repository changes or project execution occur in this review.

## QINV: adoption verified, proof work remains active

The tracked QINV brief adopts Message 45 in full.
`FirstRunInv` carries the profile, current `within`, `tidy`, and `quiet`, and both old flags.
The proposed step retains `firstOp` and `Requested`.
The run law asks for both premises at every prefix.
The brief separates close and shutdown fault controls from the first-profile theorem.

The seat is clean at `4bd063a2c5d805dd619af636351b23a3b87ba2a8`, on `seat/qinv`.
The planned production files, design note, and receipt do not exist in the retained snapshot.
The work is in scratch probes.
This is pending work, not a failed gate.

The retained base build succeeds: 996 jobs, exit 0.
Its fresh gate output checks 746 modules and 88410 declarations.
It reports 24 planned goals and 11 dependent declarations.
These are base results, not acceptance of QINV's new law.

Probe 3 has an actual successful ToolResult at transcript record 132, timestamp `2026-10-06T14:10:43.503Z`.
The exact preceding Write record supplies the checked source, retained as `probe3.checked.lean`.
The checked helpers are:

- `step_state`: the state projection ignores the run's history; axiom `propext`.
- `wake_again`: every wake signal asks the request to run again; axioms `propext`, `Quot.sound`.
- `quiet_iff_wake`: quietness means every wake identity already has a signal; the same two axioms.

The checked source's `FirstRunInv` has all six required fields.
The current scratch file subsequently grows, so its bytes differ from that checked source.
The packet retains both versions and does not transfer the earlier result to the later draft.

The later draft's `bump_inv` retains the whole old invariant.
It also requires the new profile, capacity bound, and a `Flags` certificate.
That certificate records new tidiness, accounted identities, and each wake's new or surviving old signal.
The old-signal case explicitly excludes the request that runs now.
This is useful shared proof structure, with no old-flag shortcut.
Its later bodies are outside this packet's checked result.
No step law or list-run law is accepted by this review.

## LIFT: one small connector, then both clearing command paths

The new brief already adopts the pre-clear condition.
The smallest useful connector belongs to its concrete frame instance.
It states the exact condition for `RunFiber.cleared`, without another run framework.
The candidate in `candidate.lean.txt` is **UNCOMPILED**.

The source definitions reduce its conclusion to the original flag equalling the fixed base:

```lean
MaskChain base (f.cleared interp).frame.interruptible
  (f.cleared interp).frame.stack ↔ f.frame.interruptible = base
```

`RunFiber.cleared` delegates to `frameCore.clearStack`, which empties the stack and keeps the flag.
`MaskChain` on an empty stack is equality with the base.
With an existing chain, the brief's alternative of an empty pre-clear stack supplies the same equality.
No condition about the post-clear stack supplies it.

Use this connector in the pending-command predicate `I` of `Machine.Lift.Guarded`.
Cover both command paths:

- `Cmd.exitDone`: directly calls `RunFiber.cleared`.
- `Cmd.finish`: calls `exitFiber`; its `exitStore` clears immediately when no observer remains.

When observers exist, `exitStore` schedules their commands before `exitDone`.
Preserve the latter's condition while those commands and their nested work run.
Checking the current command alone does not establish that pending condition remains true.
Likewise, a machine-only chain predicate does not discharge a condition on pending commands.

`Guarded` already separates the machine fact `J`, pending-command fact `I`, and drained-task fact `O`.
Its `StepKeeps` quantifies over the pending suffix and every carried task snapshot.
Reuse `driveState_lift` after this obligation, then the existing decision and replay lifts as their premises become available.
Keep `O` until proving it can be trivial for this invariant.
The local clear connector does not settle allocation's fixed-base bookkeeping or decision admission.
Those remain part B's explicit obligations and stop rule.

### Placement of the proposed connector

1. Concept: `scope-lifetime-finalization`, saved-mask restoration.
2. Question: the R11 open part lifting `saved-mask-pop-discipline` to runs.
   This is a helper of LIFT part B, not a separate completed claim.
3. Reach: the concrete `FrameFiber` instance, any interpreter and fiber, one fixed Boolean base.
   It states exact clearing, without assuming reachability.
4. Exclusions: no frame-step closure, command-condition preservation, allocation history, region bracket, delivery, cleanup, liveness, or host behavior.
5. Consumer: LIFT's per-command `StepKeeps` proof, then its reached-machine invariant, then a waiting wrapper under a masked caller.

## Requirement accounting

Every requirement title and exact open-parts list matches between `38837c5f` and `00b160d2`.
All thirteen also match their registry and generated-report copies.
No open part is added or closed by this packet.
QINV and LIFT still serve existing R12 and R11 questions, respectively.

`manifest.json` pins 31 retained source and evidence files.
`tool-evidence.json` keeps thirteen explicit transcript records, excluding hidden reasoning.
`result-lines.json` records exact result text and line hashes.
`receipt.json` records the final verification and the separation between checked and active scratch source.
