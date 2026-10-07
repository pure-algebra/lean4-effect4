# 2026-10-06 slice ORDER: the coordinator's review at the landing

Status: a research note (history, not authority). It is written for the implementer of the next
slices. Decisions row 300. The slice's own notes are its receipt
(`docs/research/2026-10-06-seat-ORDER-receipt.md`) and its design note.

**Verdict: landed, with seven changes.** The slice's core holds as it came: the three equations
from core's classes, `AnswerOrder.ofCore`, `subN_iff_le`, `Eliminator.adjoint_le` and
`lift_unique_pair`. The design note came first, with a compiled probe, and no file of the
coordinator was edited.

## What the landing changed, and the rule behind each

1. **One claim of the receipt was false, and it is repaired.** The receipt says that the join
   law holds as an equation for pairs of types. Its theorem took antisymmetry of each part's
   order as a premise. The checker's order on raw types is not antisymmetric: `nat | nat` and
   `nat` are each below the other. So the theorem had no instance at `Ty × Ty`, the carrier of
   the fiber rule. Its only readers were instances at `CTy` that the battery declared. The
   landing proves the equation at a pair of raw types, through the normal forms
   (`lift_union_eq_pair`), and reads it at `Member.fiber`.
   - **Rule**: before a receipt says "holds at X", instantiate the theorem at X in the battery.
     A premise that X cannot meet makes the statement empty there.
2. **One case analysis stood twice.** `lift_union_eq_of_antisymm` copied the 25 lines of
   `lift_union_eq`. The landing states the analysis once (`lift_union_eq_of`), with a premise
   that says when two joins are equal. The three forms are one application each.
   - **Rule**: when a proof copies a proof, state the shared lemma first.
3. **Lemmas that restate core's.** `le_max_left` and `le_max_right` were `Std.left_le_max` and
   `Std.right_le_max`. The brief says to add none twice, so they are cut. `max_mono_left` and
   `max_mono_right` are cut too: `max_mono` gives both.
4. **Three global instances had no reader**: `Std.Commutative`, `Std.Associative` and
   `Std.IdempotentOp` of `max`, at every partial order. The brief asks what reads an instance.
   Nothing does, so they are cut, and the module's head says so.
   - **Rule**: no lemma and no instance without a consumer (`AGENTS.md`, Trust).
5. **The namespace.** `Effect4.Laws.Program.Order` followed the module's path. A law module
   keeps the namespace of what it is about (`Effect4.Program`, `Effect4.Slice`). The
   namespace is `Effect4.Order` now.
6. **Proof style.** Eight `dsimp [...]` calls had no `only`. Each is `dsimp only [...]` now, or
   it went with its proof. The ratchet reads `simp` alone, and the rule holds for both.
7. **Placement.** Two helper theorems had no placement tag, and their docstrings named no
   consumer. Each has both now.

## The battery, and the rule for every battery from now on

The battery held ten `#print axioms` lines and seven examples that restate a theorem. The axiom
gate reads every declaration of the tree, and the kernel holds each statement. So those lines
tested nothing, and they are cut. The owner asked for this cleanup on 2026-10-06.

A line of a battery is one of three things:

- **a reader**: a law applied at a real carrier or at a real rule of the checker;
- **a control**: a red case that shows why a premise stands, or where a law stops;
- **a finite evaluation** that no theorem covers.

Write no `#print axioms` line and no restated theorem. Put a battery in a namespace: the first
version declared two instances at the root.

## Process

- **The checkout.** The slice came as edits in the main working tree, with no commit. The
  owner allows that. So hand back with every touched file named, and start the next slice after
  the coordinator's commit.
- **The Lean slot.** The receipt's build ran as `lake build` with a thread bound. Run every
  Lean, Lake and `make` command through `scratch/lean-slot.sh` (the plan, section 5.13): the
  coordinator's gates share the machine.
- **Counts.** The receipt counts lines by file. Give the two statement lists too, as seat
  UNION's receipt does: they show that no existing statement changed.

## For the next slice, TABLE

- The plan's section 5.2 has the definitions, the statements and their placement.
- Its first step is a choice: `Node.foldList` stands in the law graph, and a core module
  cannot import it. Say which way you take in the design note.
- State `table_replace_outside` only if its proof is in reach. A planned goal that stays open
  adds to the count of goals.
- The battery follows the rule above. The probe's 15 guards are finite evaluations, and each
  stays: no theorem covers a table of a concrete program.
