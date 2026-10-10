import ProbeView.Retained

open Effect4 Effect4.Program Tools.View Tools.View.Build

/-! ## The checks and the sizes -/

namespace Tools.View.RetainedCheck
open Tools.View.Retained

def later : Supervision.ForkOptions := ⟨false, false, .inherit⟩
def chain : Nat → Nat → NativeEff
  | 0, _ => .succeed (.lit (.nat 0))
  | n + 1, L =>
    .bind (.withFiber (.fork (.bind (.yieldNow 0) (.succeed (.lit (.nat n)))) later))
      (.bind (.awaitFiber (.var L) .awaitValue) (chain n (L + 2)))

def programs : List (String × NativeEff) :=
  Effect4.Program.Wire.Corpus.all ++ [("chain 6", chain 6 0), ("chain 12", chain 12 0)]

/-- The pictures of a program built by edits, at the page width the driver uses. -/
def picturesOf (p : NativeEff) : List (List (Keyed Call)) :=
  (((requests p).map (frames "t")).getD []).map fun f => pageCalls {} 1280 f.page

-- a picture read as objects and flattened is the picture
#guard programs.all fun (_, p) => (picturesOf p).all fun cs => (Scene.of cs).flatten == cs

-- the old picture, patched, is the new picture, at every step
#guard programs.all fun (_, p) =>
  let ps := picturesOf p
  (ps.zip (ps.drop 1)).all fun (a, b) =>
    let (sa, sb) := (Scene.of a, Scene.of b)
    (sa.apply (diff sa sb)).flatten == b

end Tools.View.RetainedCheck

open Tools.View.Retained Tools.View.RetainedCheck in
#eval show IO Unit from do
  for (name, p) in programs do
    let ps := picturesOf p
    let steps := ps.zip (ps.drop 1)
    let sizes := steps.map fun (a, b) => let (sa, sb) := (Scene.of a, Scene.of b); (diff sa sb).size sa
    let full := (ps.drop 1).foldl (· + ·.length) 0
    let objs := (ps.drop 1).foldl (fun n cs => n + (Scene.of cs).order.length) 0
    let sum (f : Size → Nat) := sizes.foldl (· + f ·) 0
    IO.println s!"{name}: {steps.length} steps; full pictures {full} calls in {objs} objects; patches: {sum (·.moves)} moves, {sum (·.putsNew)} new, {sum (·.putsChanged)} changed, {sum (·.drops)} dropped, {sum (·.calls)} calls carried, {sum (·.reordered)} reorders"
