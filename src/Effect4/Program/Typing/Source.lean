import Effect4.Program.Typing.PartsTable

/-!
# Program.Typing.Source — a sketch checked through its layer references

**The question.** A layer reference (`LayerTerm.ref`) names another layer of the program by its
path. Program admission checks a program's **expansion**: every reference replaced by the term
at its target (`Eff.expandRefs`, `Program/Refs.lean`), after a test that the references are well
formed (`typeOfProgram`, `Program/Typing.lean`). A sketch's own check reads the program as
written (`Sketch.check`), and the checker refuses a reference there (`layerReference`). So the
edit session of a program with a reference showed a refusal that admission does not make.
Decisions row 373 (7) rules the route: the sketch checks the expansion, as admission does, and
shows the result at the **source's** addresses, the addresses of the sketch as written.
`LayerHasTy` gains no rule for a reference.

## The address map

The expansion replaces a reference, a leaf, by a term. So it keeps every address of the
program, in its order, and it adds addresses only strictly below a reference's site: the
addresses of the copy there. The address map from the source to the expansion is the identity,
and the source's addresses are the expansion's with the copies dropped
(`Eff.addresses_expandRefs`, `Laws/Program/SourceTable.lean`).

## The table at the source's addresses

| Definition | It answers |
| --- | --- |
| `Sketch.expand` | the expansion of a sketch: its program expanded, its hole table kept |
| `Sketch.sourceCheck` | the check through the references: the first ill-formed reference refused at its site, or else the expansion's check |
| `Sketch.sourceTable` | one entry for each source address: the root holds `sourceCheck`, any other address the expansion's entry there |
| `Table.atSource` | the entries of an expansion's table at the source's addresses, its root replaced by an ill-formed reference's refusal |
| `Sketch.sourceAnnotate` | `Table.atSource` of the expansion's table in one traversal |
| `Sketch.sourceRefusals` | the distinct refusals of `sourceTable`, in its order |

The check at the root is admission's typing (`Sketch.sourceCheck_toOption`). The one traversal
is the table (`Sketch.sourceAnnotate_eq_sourceTable`, the pointer of the proposed claim
`source-annotation-agrees`).

## What this module is not

- It is not a second checker. Each answer is `Checker.checkModule`'s on the expansion.
- A copy at a reference's site has no source address, so its entries are dropped. A refusal
  located inside a copy keeps the expansion's address, as admission's refusal (`Api.explain`).
- It runs nothing. The compile does not expand a reference: it redirects it to its target.

This module is not a Lean module (decisions row 200): it imports `Program/Sketch.lean`, which is
not one.
-/

set_option autoImplicit false

namespace Effect4.Program

/-- **Strictly below one of the sites**: one of the sites is a proper prefix of the address. -/
def Table.belowSite (sites : List (List Nat)) (a : List Nat) : Bool :=
  sites.any fun site => Path.properPrefix site a

/-- **The entries of an expansion's table at the source's addresses.** The entries strictly
below a site are dropped: they stand in a copy. Where a reference is ill formed (`fault`), the
root's entry holds that reference's refusal, located at its site. -/
def Table.atSource (sites : List (List Nat)) (fault : Option (List Nat × List Nat × RefFault))
    (t : List Table.Entry) : List Table.Entry :=
  match fault, t.filter fun e => !Table.belowSite sites e.path with
  | some (site, target, why), _ :: rest =>
    ⟨[], some (.env []), some (.error ⟨site, .referenceIllFormed target why⟩)⟩ :: rest
  | _, kept => kept

namespace Sketch

/-- **The expansion of a sketch**: its program with every layer reference replaced by the term
at its target (`Eff.expandRefs`). The hole table is kept. -/
def expand (s : Sketch) : Sketch := { s with program := s.program.expandRefs }

/-- The reference sites of a sketch's program, in program order. -/
def sites (s : Sketch) : List (List Nat) := (s.program.refSites []).map (·.1)

/-- **The check of a sketch through its layer references**, as program admission checks a
program. The first ill-formed reference is refused at its site (`Eff.firstRefFault`), as
`Api.explain` refuses it. Otherwise it is the check of the expansion. Its success is admission's
typing (`Sketch.sourceCheck_toOption`, `Laws/Program/SourceTable.lean`). -/
def sourceCheck (s : Sketch) (app : SigApp := {}) : Except TypeRefusal EffTy :=
  match s.program.firstRefFault with
  | some (site, target, why) => .error ⟨site, .referenceIllFormed target why⟩
  | none => s.expand.check app

/-- **One entry at a source address**: the root holds the check through the references, and any
other address holds the expansion's entry there (`Sketch.tableEntry`). -/
def sourceEntry (s : Sketch) (app : SigApp) : List Nat → Table.Entry
  | [] => ⟨[], some (.env []), some (s.sourceCheck app)⟩
  | a@(_ :: _) => s.expand.tableEntry app a

/-- **The address table of a sketch through its layer references**: one entry for each address
of the sketch as written, in its order (`sourceEntry`). It is a specification: each entry costs
up to one check of a part. -/
def sourceTable (s : Sketch) (app : SigApp := {}) : List Table.Entry :=
  (Node.addresses (.eff s.program)).map (s.sourceEntry app)

/-- **The table through the references in one traversal of the expansion**: its table, part by
part (`Sketch.annotate`), at the source's addresses (`Table.atSource`). It is the table
(`Sketch.sourceAnnotate_eq_sourceTable`, `Laws/Program/SourceTable.lean`). -/
def sourceAnnotate (s : Sketch) (app : SigApp := {}) : List Table.Entry :=
  Table.atSource s.sites s.program.firstRefFault (s.expand.annotate app)

/-- **The refusals of a sketch through its layer references**: the distinct refusals of its
table's entries, in the table's order. The head is the check's refusal, and the list is empty
exactly when the check succeeds (`Sketch.sourceRefusals_nil_iff`). -/
def sourceRefusals (s : Sketch) (app : SigApp := {}) : List TypeRefusal :=
  ((s.sourceTable app).filterMap fun e => e.result.bind Checker.refusal).eraseDups

end Sketch

end Effect4.Program
