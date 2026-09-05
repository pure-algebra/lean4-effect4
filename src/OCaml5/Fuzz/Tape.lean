import OCaml5.Avatar
import OCaml5.Fuzz.Gen

/-!
# OCaml5.Fuzz.Tape

**What it is.** Round three's `RunDecision` tapes (A0's request 4): a tape entry is generated once
and printed twice — as the OCaml literal the avatar matches on and as the wire line both sides
key on — from the same draw, so the two spellings cannot drift.

**Depends on.** `OCaml5.Fuzz.Gen`, `OCaml5.Avatar` (`Fibers.runDecision`, `Fibers.tapeModule`).

**Properties.**
* **The constructor names are the Lean ones** of `Avatar.Fibers.runDecision` — *by construction*.
* **Every generated tape is a well-typed `run_decision list`** — *tested* (`fuzz.sh tapes` compiles
  the module on three hosts).
-/

namespace OCaml5.Fuzz

/-! ## Round three: `RunDecision` tapes (A0's request 4)

A tape entry is generated once and printed twice — as the OCaml literal the avatar will match on
and as the wire line both sides key on — from the same draw, so the two spellings cannot drift.
The constructor names are the Lean ones, taken from `OCaml5.Avatar.Fibers.runDecision`. -/

structure TapeEntry where
  /-- The OCaml `run_decision` literal. -/
  expr : Ml.Expr
  /-- The wire spelling: the Lean constructor name and its arguments. -/
  wire : String

private def genFiber (n : Nat) : Gen Nat := do
  let i ← pick n
  return i

private def genAnswer : Gen (Ml.Expr × String) := do
  let k ← pick 3
  if k == 0 then
    let n ← pick 10
    return (.ctor "Aval" [.ctor "Vnat" [.int n]], s!"v{n}")
  else if k == 1 then
    return (.ctor "Aval" [.ctor "Vunit" []], "vunit")
  else
    let e ← pick 5
    return (.ctor "Acause" [Ml.Expr.call "cause_fail" [.int e]], s!"c{e}")

/-- One `RunDecision`, uniformly over the seven constructors of `Fibers.lean:362`. -/
def genDecision (nfibers : Nat) : Gen TapeEntry := do
  let k ← pick 7
  if k == 0 then
    let f ← genFiber nfibers
    return ⟨.ctor "Dfire" [.int f], s!"fire {f}"⟩
  else if k == 1 then
    return ⟨.ctor "Dflush" [], "flush"⟩
  else if k == 2 then
    let f ← genFiber nfibers
    return ⟨.ctor "Devaluate" [.int f], s!"evaluate {f}"⟩
  else if k == 3 then
    let f ← genFiber nfibers
    let b ← pick 2
    return ⟨.ctor "DyieldVerdict" [.int f, .bool (b == 1)],
            s!"yieldVerdict {f} {if b == 1 then "true" else "false"}"⟩
  else if k == 4 then
    let f ← genFiber nfibers
    let t ← pick 8
    let (ae, aw) ← genAnswer
    return ⟨.ctor "DanswerAsync" [.int f, .int t, ae], s!"answerAsync {f} {t} {aw}"⟩
  else if k == 5 then
    let who ← pick (nfibers + 1)
    let t ← genFiber nfibers
    let ann ← pick 3
    let anns : List String := (List.range ann).map fun i => s!"a{i}"
    let whoE : Ml.Expr :=
      if who == nfibers then .ctor "None" [] else .ctor "Some" [.int who]
    let whoW : String := if who == nfibers then "-" else toString who
    return ⟨.ctor "DinterruptFrom" [whoE, .listLit (anns.map (Ml.Expr.str ·)), .int t],
            s!"interruptFrom {whoW} {String.intercalate ";" anns} {t}"⟩
  else
    return ⟨.ctor "DinstallMiddleware" [], "installMiddleware"⟩

def genTape (len nfibers : Nat) : Gen (List TapeEntry) :=
  match len with
  | 0 => return []
  | n + 1 => do
      let e ← genDecision nfibers
      let rest ← genTape n nfibers
      return e :: rest

end OCaml5.Fuzz
