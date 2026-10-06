import Test.Program.MaskContract
import Test.Program.QueueMask

/-!
# The mask's stack discipline on finite runs (research probe, 2026-10-06)

Not part of the tree. Run it from the repository root:
`lake env lean docs/research/2026-10-05-claude-lead/mask-probes/MaskStack.lean`.
`MaskStack.out` beside this file is its output.

The question: what invariant of runs gives the open half of `saved-mask-restoration` (R11)? A
region that changes no flag pushes no frame, so its exit flag is what its body left.

The candidate, in two parts:

* **Alternation.** On each fiber's stack the mask frames (`Prim.setInterruptible g`) alternate
  from the top. The first saves the negation of the fiber's flag, and each next one saves the
  negation of the one above it. A region's entry pushes a frame exactly when it changes the
  flag, and a frame's pass returns its saved flag (`Prim.ensure`, `FrameFiber.uninterruptible`,
  `FrameFiber.interruptibleRegion`, `src/Effect4/Machine/Frames.lean`).
* **A constant base.** The flag under every mask frame is the same in every state of a fiber:
  the lowest saved flag, or the flag itself where no mask frame is on the stack.

Together they give the bracket: two states of one fiber with the same stack have the same flag.

What is checked: each scenario's machine, cut at each command budget from 0 to a bound and at
the full budget, on one tape. In each cut state, each fiber's flag and mask frames. A command
runs a fiber to its next scheduling point, so a cut falls between two commands and never inside
a fiber's entry. An operation budget on the root (`MaskContract.budgeted`) did not give finer
cuts: at the budgets 1 and 2 the runs made no progress on this tape.

`wrong reading` is the red control: the top frame saves the flag itself. It fails wherever a
mask frame is on a stack, and holds only for `s6Masked`, where no mask frame is ever pushed.

Every line is a finite check on one schedule. It proves nothing.
-/

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring

namespace MaskStackProbe

structure Seen where
  id : Nat
  flag : Bool
  frames : List Bool
  exited : Bool
deriving Repr, BEq

def seen (m : Api.Machine) : List Seen :=
  m.fibers.map fun f =>
    { id := f.id.value, flag := f.frame.interruptible,
      frames := f.frame.stack.filterMap
        (fun p => match p with | Prim.setInterruptible g => some g | _ => none),
      exited := f.exit.isSome }

/-- The saved flags, from the top: the first is the negation of the flag, and each next one is
the negation of the one above it. -/
def alternates : Bool → List Bool → Bool
  | _, [] => true
  | flag, g :: rest => (g == !flag) && alternates g rest

/-- A wrong reading, as a red control: the top frame saves the flag itself. -/
def wrong : Bool → List Bool → Bool
  | _, [] => true
  | flag, g :: rest => (g == flag) && wrong g rest

/-- The flag under every mask frame: the lowest saved flag, or the flag itself. -/
def baseOf (flag : Bool) (frames : List Bool) : Bool := frames.getLast?.getD flag

def tape : List Api.Decision := [Api.evaluate, Api.flush, Api.flush, Api.flush]

def statesOf (src : Src NativeOp) (upTo : Nat) : List (List Seen) :=
  match Test.Program.MaskContract.buildOf (Test.Program.MaskContract.mk src) with
  | none => []
  | some p => (List.range upTo ++ [20000]).map fun n => seen (Api.replay p n tape [] [] 20000).machine

def allOf (check : Bool → List Bool → Bool) (states : List (List Seen)) : Bool :=
  states.all fun fibers => fibers.all fun s => check s.flag s.frames

def basesOf (states : List (List Seen)) (id : Nat) : List Bool :=
  states.filterMap fun fibers =>
    (fibers.find? (·.id == id)).bind fun s => if s.exited then none else some (baseOf s.flag s.frames)

def baseConstant (states : List (List Seen)) : Bool :=
  let ids := (states.flatMap fun fibers => fibers.map (·.id)).eraseDups
  ids.all fun id => match basesOf states id with
    | [] => true
    | b :: rest => rest.all (· == b)

/-- A report: states, fibers, the deepest stack of mask frames, the count of states that differ
from the one before, whether the bound covers the run, and the three checks. -/
def report (name : String) (src : Src NativeOp) (upTo : Nat := 160) : String :=
  let states := statesOf src upTo
  let depth := (states.flatMap fun fibers => fibers.map (·.frames.length)).foldl max 0
  let fibers := (states.flatMap fun fibers => fibers.map (·.id)).eraseDups.length
  let moves := (states.zip (states.drop 1)).countP fun pair => pair.1 != pair.2
  let covered := match states.reverse with
    | last :: before :: _ => last == before
    | _ => false
  let masked := (states.flatMap id).countP fun s => !s.flag
  s!"{name}: states {states.length}, fibers {fibers}, depth {depth}, moves {moves}, masked {masked}, covered {covered}, alternates {allOf alternates states}, base constant {baseConstant states}, wrong reading {allOf wrong states}"

open Test.Program.MaskContract in
#eval IO.println (String.intercalate "\n"
  [ report "s1" s1, report "s2" s2, report "s3" s3, report "s4" s4, report "s5 outer" (s5 true),
    report "s5 inner" (s5 false), report "s6" s6, report "s6Masked" s6Masked, report "s7" s7,
    report "s7Regions" s7Regions, report "s9" s9, report "s10" s10 ])

open Test.Program.QueueMask in
#eval IO.println (String.intercalate "\n"
  [ report "queue r2" r2 400, report "queue r5" r5 400, report "queue r7" r7 400,
    report "queue maskedCaller" (maskedCaller take) 400 ])

end MaskStackProbe
