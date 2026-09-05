import OCaml5.Compile.Agreement
import OCaml5.Fuzz.Term

/-!
# Spike P4: the compiler on P5's generated corpus

Status: spike P4, 2026-09-04. Module `OCaml5.Compile.Fuzz`. Report:
`docs/research/2026-09-04-spike-p4-compile.md`.

`OCaml5.Fuzz` (spike P5) is a random `Term` generator over the effect fragment: deep handlers
in the three `Deep.match_with` / `Deep.try_with` styles, forwarding clauses, `Fun.protect`,
options, parked continuations, and `Shallow.fiber`. P5 runs each generated program on the three
real hosts and compares the rows with `Machine`'s. This module runs the *same* generator
through `compile` and compares three machines instead of three hosts.

`Fuzz.classify` is P5's filter: a term is kept only when `ocamlc` would compile it
(`Compiler.Admissible`), the machine finishes on it, it prints at least one row, and no row
carries a heap identity no host could print. A kept term is then classified here by whether it
is inside `compile`'s domain (§"Two gaps" of `OCaml5.Compile`) and whether the three runs agree.
-/

namespace OCaml5.Compile.Fuzz

open OCaml5 OCaml5.Compile.Agreement

/-- One of five verdicts on a seed. -/
inductive V where
  /-- P5's own filter rejected the term: inadmissible, stuck, out of fuel, no rows, or a row
  no host could print. -/
  | rejected
  /-- The term uses `Shallow` or `caml_drop_continuation`, which the O2 machine has no arm
  for. Counted, not checked. -/
  | outside
  /-- `Machine` = `Code.Machine ∘ compile` = `Code.Machine ∘ Cps.f ∘ compile`. -/
  | agree
  /-- The compiled program disagrees with the term. -/
  | disagreeCode
  /-- The compiled program agrees but its CPS transform does not. -/
  | disagreeCps
deriving DecidableEq, Repr

def verdictOf (seed size : Nat) : V :=
  let t := Fuzz.programOf seed size
  let c := Fuzz.classify t
  if !c.ok then .rejected
  else if !inDomain t then .outside
  else if !agreesWithTerm Fuzz.runFuel t then .disagreeCode
  else if !cpsAgrees t then .disagreeCps
  else .agree

/-- The verdicts of `count` consecutive seeds from `first`. -/
def verdicts (first count size : Nat) : List V :=
  (List.range count).map (fun i => verdictOf (first + i) size)

def tally (vs : List V) (v : V) : Nat := (vs.filter (· == v)).length

/-- `(rejected, outside, agree, disagreeCode, disagreeCps)`. -/
def counts (vs : List V) : Nat × Nat × Nat × Nat × Nat :=
  (tally vs .rejected, tally vs .outside, tally vs .agree,
   tally vs .disagreeCode, tally vs .disagreeCps)

/-! ## The runs

Four batches, two depths, so that the shallow shapes (`Fuzz.genShallow`, reachable only at the
larger size) are exercised too. -/

def batchA : List V := verdicts 1 120 4
def batchB : List V := verdicts 1000 120 5
def batchC : List V := verdicts 5000 120 6
def batchD : List V := verdicts 9000 140 3

def all : List V := batchA ++ batchB ++ batchC ++ batchD

/- 500 seeds, no disagreement of either kind. -/
#guard tally all .disagreeCode == 0
#guard tally all .disagreeCps == 0
#guard all.length == 500

/- …and the corpus is not vacuous: every seed survived P5's own filter, 455 of the 500 are
inside the domain, and every one of those agreed. -/
#guard tally all .rejected == 0
#guard tally all .outside == 45
#guard tally all .agree == 455

#eval (counts batchA, counts batchB, counts batchC, counts batchD, counts all)

/-! ## The seeds that are outside the domain

Every one of them is outside for the same single reason: `Shallow` needs
`caml_continuation_use_and_update_handler_noexc`, and `Fuzz.genPark`'s drop shape needs
`caml_drop_continuation`. Neither has an arm in `Code.Machine.purePrim`. -/

def outsideReason (seed size : Nat) : String :=
  match codeRun (Fuzz.programOf seed size) with
  | (.stuck why, _) => why
  | _ => "in domain"

def outsideSeeds (first count size : Nat) : List Nat :=
  (List.range count).filterMap (fun i =>
    if verdictOf (first + i) size == V.outside then Option.some (first + i) else Option.none)

#eval (outsideSeeds 1 120 4, outsideSeeds 1000 120 5, outsideSeeds 5000 120 6,
       outsideSeeds 9000 140 3)

end OCaml5.Compile.Fuzz
