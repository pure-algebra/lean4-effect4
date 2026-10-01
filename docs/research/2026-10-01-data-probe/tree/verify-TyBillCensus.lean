import Effect4
import Effect4.Laws
import Effect4.Laws.Auto.Exhaustive
import Test.Audit.ExhaustiveFixture
import Test.Counterexamples.Machine.Semantics.ValueMembership

/-! Verifier of seat TREE (2026-10-01): checks on the seat's bill instruments. Printed, plus
finite `#guard`s. Scratch, not in the tree.

1. `#exhaustive_gate Effect4.Program.Ty under Test`: the seat read `Test/` by hand because it
   took the `Test` oleans to be stale; the landing build of 01:15–01:22 built them, so the
   gate can run.
2. `#verify_ty_proof_census`: the seat's census counts a theorem only when its own term names a
   `Ty` eliminator. A proof by `fun_induction f` or `fun_cases f` names `f.induct` /
   `f.fun_cases` instead, so it is not counted although its case list is `f`'s arm list. This
   counts the authored theorems that use the induction or cases principle of a function whose
   principle mentions a `Ty` constructor, and how many of them the seat's census2 misses. It
   also lists the authored theorems the seat's name rule drops by the `"eq_"` prefix although
   they are not equation lemmas (`eq_<digits>`, `eq_def`).
3. `#private_gate F`: the seat's private-definition sweep, generalised to any family, run on
   the other alphabets the seat billed with the public gate only.
4. `#guard`s on the Schema bridge, the codec and product distribution. -/

open Lean Elab Command Meta
open Effect4.Laws.Auto (isCompilerHelper moduleOf)
open Effect4.Laws.Auto.Exhaustive (eliminatorsOf matchesOn matcherCatchAll)

-- 1. the gate over the `Test` library
#exhaustive_gate Effect4.Program.Ty under Test

namespace VerifyTree.Census

/-- census2's exclusion rule, copied verbatim from `TyBillPrivateProbe.lean`. -/
def seatGenerated (name : Name) : Bool :=
  isCompilerHelper name ||
  name.components.any (fun c =>
    let s := c.toString
    "match_".isPrefixOf s || "congr_eq".isPrefixOf s || "eq_".isPrefixOf s ||
      s == "eq_def" || "induct".isPrefixOf s || s == "splitter" || s == "fun_cases" ||
      "proof_".isPrefixOf s || "_unfold".isPrefixOf s || s == "eq_cata")

/-- An equation lemma the equation compiler names: `eq_<digits>` or `eq_def`. -/
def isEqnName (s : String) : Bool :=
  s == "eq_def" ||
    (("eq_".isPrefixOf s) && (s.toList.drop 3) != [] && (s.toList.drop 3).all Char.isDigit)

/-- The same rule with the `"eq_"` prefix narrowed to real equation lemmas. -/
def generatedNarrow (name : Name) : Bool :=
  isCompilerHelper name ||
  name.components.any (fun c =>
    let s := c.toString
    "match_".isPrefixOf s || "congr_eq".isPrefixOf s || isEqnName s ||
      "induct".isPrefixOf s || s == "splitter" || s == "fun_cases" ||
      "proof_".isPrefixOf s || "_unfold".isPrefixOf s || s == "eq_cata")

/-- Function induction and function cases principles. -/
def isFunPrinciple (s : String) : Bool :=
  s == "induct" || s == "induct_unfolding" || s == "fun_cases" || s == "fun_cases_unfolding" ||
    s == "mutual_induct"

elab "#verify_ty_proof_census" : command => do
  let env ← getEnv
  let tyName := ``Effect4.Program.Ty
  let family : Array Name := #[tyName]
  let elims := eliminatorsOf env family
  let ctors : List Name :=
    match env.find? tyName with
    | some (.inductInfo iv) => iv.ctors
    | _ => []
  let mut seat : Array Name := #[]
  let mut dropped : Array Name := #[]
  let mut funUsers : Array (Name × Name) := #[]
  for (name, info) in env.constants.map₁.toList do
    let .thmInfo t := info | continue
    if name.isInternalDetail && !isPrivateName name then continue
    let some mod := moduleOf env name | continue
    unless (`Effect4).isPrefixOf mod do continue
    let used := t.value.getUsedConstants
    let direct := used.any elims.contains
    if direct && !seatGenerated name then seat := seat.push name
    if direct && seatGenerated name && !generatedNarrow name then dropped := dropped.push name
    if !generatedNarrow name then
      for c in used do
        match c with
        | .str _ s =>
          if isFunPrinciple s then
            if let some ci := env.find? c then
              if ci.type.getUsedConstants.any ctors.contains then
                funUsers := funUsers.push (name, c)
        | _ => pure ()
  let users := funUsers.foldl (init := (#[] : Array Name)) fun acc (n, _) =>
    if acc.contains n then acc else acc.push n
  let missed := users.filter (!seat.contains ·)
  let mut report := m!"#verify_ty_proof_census: seat census2 = {seat.size}; dropped by the \
    \"eq_\" prefix although not an equation lemma and eliminating Ty directly = {dropped.size}; \
    authored theorems using a Ty-shaped induct/fun_cases principle = {users.size}, of which \
    {missed.size} are not in census2"
  report := report ++ m!"\n  dropped by the prefix rule:"
  for n in dropped.qsort (·.toString < ·.toString) do
    report := report ++ m!"\n    {(privateToUserName? n).getD n}"
  report := report ++ m!"\n  principle users not in census2 (theorem <- principle):"
  let rows := funUsers.filter (fun (n, _) => missed.contains n)
  for (n, c) in rows.qsort (fun a b => a.1.toString < b.1.toString) do
    report := report ++ m!"\n    {(privateToUserName? n).getD n} <- {c}"
  report := report ++ m!"\n  principle users also in census2:"
  let both := funUsers.filter (fun (n, _) => !missed.contains n)
  for (n, c) in both.qsort (fun a b => a.1.toString < b.1.toString) do
    report := report ++ m!"\n    {(privateToUserName? n).getD n} <- {c}"
  logInfo report

-- 2. the proof-side census check
#verify_ty_proof_census

syntax (name := privateGate) "#private_gate " ident : command

/-- The seat's `#ty_private_gate`, with the family as an argument. -/
@[command_elab privateGate] def elabPrivateGate : CommandElab := fun stx => do
  let root ← liftCoreM (realizeGlobalConstNoOverload stx[1])
  let env ← getEnv
  let family : Array Name := #[root]
  let elims := eliminatorsOf env family
  let mut rows : Array (String × String × String × Nat × Nat × Bool) := #[]
  for (name, info) in env.constants.map₁.toList do
    let .defnInfo d := info | continue
    unless isPrivateName name do continue
    if isMatcherCore env name || isAuxRecursor env name || isCompilerHelper name then continue
    let some mod := moduleOf env name | continue
    unless (`Effect4).isPrefixOf mod do continue
    unless d.value.getUsedConstants.any elims.contains do continue
    let hits ← liftTermElabM (matchesOn family name mod 200 d.value #[])
    let mut seen : Array (Name × Nat) := #[]
    for h in hits do
      if seen.contains (h.matcher, h.discr) then continue
      seen := seen.push (h.matcher, h.discr)
      let ca ← liftTermElabM (matcherCatchAll h.matcher h.info h.discr)
      rows := rows.push (mod.toString, (privateToUserName? name).getD name |>.toString,
        h.matcher.toString, h.discr, h.info.numAlts, ca)
  let exposed := rows.filter (!·.2.2.2.2.2)
  let mut report := m!"#private_gate {root}: {rows.size} match(es) in private definitions of \
    Effect4.* read it, {exposed.size} with no catch-all"
  for (m, n, mt, d, a, c) in rows do
    report := report ++ m!"\n  {n}\t{m}\t{mt}\tdiscr {d}\talts {a}\tcatchAll {c}"
  logInfo report

-- 3. private definitions of the other alphabets the seat billed
#private_gate Effect4.Machine.Err
#private_gate Effect4.Program.Lit
#private_gate Effect4.Program.NativeAtom
#private_gate Effect4.Store.Val
#private_gate Effect4.Program.Ty

end VerifyTree.Census

namespace VerifyTree.Facts

open Effect4 Effect4.Program Effect4.Schema

-- 4a. `schema (.var i)` is documented as "an opaque node `ofSchema` does not read back"
-- (`Bridge.lean:56-57`); it reads back as a handle, and `schema` identifies it with that handle.
#guard Bridge.ofSchema (Bridge.schema (.var 0)) = some (.handle "effect/schema/TypeParameter")
#guard Bridge.schema (.var 3) = Bridge.schema (.handle "effect/schema/TypeParameter")

-- 4b. the codec's object read refuses an extra field (`fields?`, `Codec.lean:73-81`): rc.112's
-- own decoder strips it by default (`SchemaAST.ts:445`, `onExcessProperty: "ignore"`).
#guard Effect4.Schema.decode (.option .nat)
  (.obj [("_tag", .str "Some"), ("value", Arch.Json.ofNat 1), ("extra", .bool true)]) = none
#guard Effect4.Schema.decode (.option .nat)
  (.obj [("_tag", .str "Some"), ("value", Arch.Json.ofNat 1)]) = some (.some (.nat 1))

-- 4c. the tree distributes a product over a union factor (two members after normalization):
-- the canonical tagged column of the 2026-09-10 boundary decisions (T3).
#guard (Ty.normalize (.prod (.union (.lit "A") (.lit "B")) .nat)).members.length = 2

-- 4d. DI-67's inhabitation invariant has a gap the record case repeats: a product with a `never`
-- column is canonical and is not `never` (no product-annihilation rule, `Ty.lean:563-564`).
#guard Ty.normalize (.prod .never .nat) = .prod .never .nat

end VerifyTree.Facts
