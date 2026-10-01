# Addendum 6 to the slice 6 brief: G, H1 and H2 part one resume

Written 2026-10-01 by the coordinator, after Codex's receipt at `c42f4a46` (D and F merged at
`9ad8a7c0`; slice 6 is complete). Read it with the [brief](2026-09-30-codex-brief-slice6-and-fixes.md)
and addenda [1](2026-09-30-codex-brief-slice6-addendum-1.md)–[5](2026-09-30-codex-brief-slice6-addendum-5.md);
where they differ, this one wins. The owner ruled on 2026-10-01: "ratify as accepted", on the
coordinator's recommendations for the three checked stops.

**The one thing first.** All three stops are lifted by the amendments the receipt proposed: G's
fourth fixture is the fourth expected refusal; H1 has its ruling (row 133: a fiber with a queued
`finish` is typed by that finish, and its code slot is inert); H2 part one's two false test
statements are amended and the bounded migration is authorized under the same stop rule. The order
is G, H1, H2 part one. The next merge follows H2 part one, or earlier if the owner asks.

## Item G: the fourth fixture is expected

`Test/Codegen/TemplatesContract.lean`'s `layerSamples[1]` has a `nat`-typed service (name 7,
code 4) whose body returns `unit`; today's `checkLayer` accepts it and G's revised effect-leaf
equation refuses `valueNotSubtype key unit nat` at `[]` (`G/FourthFixtureProbe.lean`, ten
prints at the ceiling).
1. It joins the expected refusals (now four). Keep its shared definitions and its printer coverage;
   add the exact-source negative checker control and the neighbouring `nat`-valued `succeed`
   positive, as `G/candidate/rendered/PROPOSED-fourth-fixture.patch` has them.
2. Correct addendum 3's unchanged-leaf census in the receipt.
3. The two related cases stay as the receipt records them: Provision's failure-only docs layer
   remains accepted under `docsSig` (recorded, not counted); generator program 141 was already
   refused and now fails one leaf earlier (the corpus comparison reports the changed diagnostic;
   no acceptance bit changes).
4. Then G as addenda 2–4 state it. The stop rule stays: a fifth in-tree program or layer refused
   stops G again. `E4-PROV-CE-006` becomes REPAIRED at G's landing; row 105 is the coordinator's.

## Item H1: terminal delivery (row 133, ruled)

**The witness** (`H1/TerminalSavedWitness.candidate.lean`, fifteen prints at the ceiling): a typed
root whose current code returns `Nat 42` with one typed answer continuation returning `unit`.
Delivery removes the continuation and queues `finish(unit)`, but the fiber's code slot keeps
`Nat 42` with an empty saved stack and no exit, and every valid output world declares the root at
`unit`. The pending finish is correct; the stale code slot is the mismatch. So the proposed
`StepPreserves` for `deliver` is false as stated, before any proof.

**The ruling (owner, 2026-10-01).** A position is typed by what it will deliver, the principle
of row 106's observer clause: a fiber with a queued `finish` is typed by that finish, and its code
slot is inert; the boundary before `finish` sets the exit field is typed the same way. Not an
exited-fiber-only exception (a changing intermediate type is already legal), and not a
reachability premise on the frozen stack theorem.
1. Restate the typed state's code clause so that it applies to a fiber only while no `finish` for
   it is queued; when one is, the fiber's type is read from that command's exit (through `preds.exit`
   and so `RCmdOk`). Say in the receipt which conjunct of `TypedState` changes and why no other
   command needs the clause (read `loop`, `evaluate`, `exitDone`, `closeParAwait`, `afterInterrupt`
   and `raceCancel` for the same boundary; name any that does).
2. Land the witness as a positive control under the new clause (the state is typed and the step
   keeps it typed) beside the refutation of the old statement, in `M6Capstone.lean`.
3. Register `E4-SCHED-CE-019`, "a fiber is typed by its queued finish, not by its stale code slot",
   SEEDED by the witness, REPAIRED by H1 together with `E4-SCHED-CE-017` and `-018`.
4. Then H1 as addenda 3–5 state it: the generated command check on every queued command, the
   guard's conditions mirrored on the reference machine, `pending_below` as a law, the controls.
   Statements only; the 18 command proofs stay with the M5–M7 brief.

## Item H2 part one: the two test statements, and the bounded migration

The eight authorized repairs pass with seven local helpers, fifteen prints at the ceiling. Two
existing *test* statements are false under the repaired judgment (statement defects, refuted at the
ceiling): `Test.Program.TypedControl.cancel_typed` lets a clean cancellation die with `badName`;
`Test.Program.LoadedAdmission.lookup_typed`'s conditional service premise admits an undecodable
`unit` input whose result is `badName`.
1. Amend the two statements as the receipt proposes: an explicit shape exclusion for
   `cancel_typed`; an actual decoded-context witness for `lookup_typed`.
2. The bounded migration is authorized as measured: the 25 proposed existing test bodies across
   eight files in `H2/proposed-amendment.md`, the two premise changes, and the new local adapters
   and controls. Test bodies count like library bodies: any failure outside that inventory stops
   H2 again with a measured report. Nothing is repaired past the inventory.
3. Part one's clause stays as the owner clarified it (addendum 5's amendments): `badName` and
   `notImplemented` only; `missingService` is part two under row 117.
4. `E4-TYPED-CE-007` becomes REPAIRED at part one's landing; `E4-TYPED-CE-003`'s repair column is
   updated; `E4-TYPED-CE-008` is added SEEDED for part two from the audit's probe.

## After H2 part one, if no new brief has arrived: row 39

Row 39 (the Schema wipe) is ruled since 2026-09-18 and is deletion-only: `Schema/Check.lean`,
`Schema/EffectfulField.lean` with `Codegen/EffectfulField.lean`, `Schema/Image.lean` with
`Laws/Schema/Image.lean`, `Arch/Accepts.lean`, `Api.schemaOf`, `Annotations.lean` cut to its
carrier and two keys, the two harnesses, the tests the row names; then `Store.render` and
`ShapeDoc.document` out of `Store/Domain/Shape.lean`. Read the row for the exact list. Land it as
its own deletion series with narrow builds, the root imports and `Test/All.lean` edited at their
anchors, no generator unless a generated group reads a deleted module (then the fixed order). It
touches no file of G, H1 or H2. Stop if a deletion needs a change outside the row's list.

## Rules and receipt

Same rules as addenda 4 and 5. Update the receipt in place: "After addendum 6" at the top.
