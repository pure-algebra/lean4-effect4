# ST1b preparation

The pure transaction model compiles and passes its named axiom audit.
All five native suites pass against the actual regenerated goldens and facts.
The final packet includes the Lean-owned policy table and its native mutation control.
Production remains unchanged by this preparation.

The commit base is S0 receipt `489e127a8b94f4796ff40ef4200080b5e83a94f2`.
The patch base includes the coordinator's uncommitted ST1a integration and native G2 correction.
`manifest.json` pins those exact preimage bytes.
This preparation creates no commit.

## Prepared model

`Cas.lean` owns the single transaction event interpreter.
`CasOf replayEvents` admits only stores reached through that interpreter.
Accepted commit and interruption constructors extend their replay witnesses.

A transaction admits nodes once, then checks moves against the resulting table.
Conflicts become located node refusals.
A failed operation exposes no partial store or receipt.
A cut requires the whole transaction to pass first.
Node cuts count fresh insertions and retain the old roots.
Published cuts return the exact committed store.

`Root` holds `RootPolicy`, a fixed target kind, and the complete `Head`.
The patch deletes `RootKind`, `nextVersion`, `putRoot`, and `putRootOr`.
`Word.verifyRoots` reads `head.digest`.
`Cas.get` remains the typed reader.
The patch does not restore the retired `Store.get`.

## Proof placement and checked laws

`PLACEMENT.md` records the five placement facts before proof work.
The proposed registry properties serve exact-codecs and R13.
The coordinator registers them during the production landing.

| Declaration in `src/Effect4/Store/Domain/Cas.lean` | Role | Observation and hypotheses |
| --- | --- | --- |
| `advance_stale` | compatibility | A differing complete expected head refuses before target checks. |
| `advance_duplicate` | compatibility | An identical kind and digest retain the generation and exact store. |
| `advance_head` | compatibility | A changed accepted target increments the generation exactly once and installs that head. |
| `journal_ff` | preservation | A changed accepted journal target reaches the old head through designated parent fields. |
| `commit_grows`, `bytes_never_change` | preservation | Every accepted transaction retains each prior resident at the same digest. |
| `commit_reads` | compatibility | Every submitted node reads back after successful commit. A conflict is a refusal. |
| `interrupted_closed` | preservation | Every accepted cut from a closed store retains node closure. |
| `interrupted_roots` | compatibility | Every accepted cut has old roots or the exact published commit store. |
| `replay_append` | helper | Appending one event applies the canonical event step after the prior replay. |

These laws assume no hash injectivity.
They establish no filesystem theorem, host progress, or native translation theorem.
The reached-store package retains its explicit replay parameter for typed reading.

The final named audit reports:

```text
#axiom_audit: 1404 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals
```

The final audit includes checkpoint extraction and the complete transaction fixture.

## Finite model controls

`Test/Store/SeamsTransactions.lean` exercises the actual operations.
The final fixture passes after the checkpoint extraction addition.

| Plan requirement | Control |
| --- | --- |
| Ordinary rows 1–6 | Fresh nodes, duplicate nodes, creation, repeated creation, duplicate advance, stale-first wrong target. |
| A→B→A | Generations advance through the repeated digest; the original full expectation refuses. |
| Pin | An identical target duplicates; a changed target refuses. Staleness precedes pin checks. |
| Journal | Canonical parent fields permit advancement. An incidental edge refuses `fork`. A new name creates an independent fork. |
| Atomic rollback | A late missing root prevents commit and every interrupted cut. |
| Interrupted nodes | Existing duplicates consume no fresh-node count. A node depending on the first fresh node stays absent at cut one. |
| Interrupted publication | Published interruption returns the exact committed nodes and roots. |
| Retention | Cut zero keeps preexisting nodes. Large cuts retain all accepted nodes and old roots. |
| Conflict | An exhibited occupied-address conflict becomes `TxnRefusal.node`. |
| Names | Differently cased names remain distinct. |

Ordinary row 7 belongs to ST3's result envelope.
The damaged-segment row belongs to ST2's disk boundary.
This packet makes neither claim early.

## Corrections retained by controls

The duplicate branch is separate from `advance_head`'s changed-target law.
An unconditional generation-increase statement fails on ordinary row 5.
The fixture retains that control.

The old native root names fold case and reject spaces.
Lean root names compare exactly.
Version 2 keeps exact UTF-8 name bytes within its wire capacity.
The controls retain differently cased names and spaces as distinct observations.

Legacy root-plane bytes differ from the new policy alphabet.
The native reader maps version-1 bytes 0–5 to swap and byte 6 to pin.
The version-2 writer uses swap=0, journal=1, and pin=2.
The controls prevent legacy Journal byte 1 from becoming new journal policy accidentally.

Checkpoint publication already refuses a predecessor chain that misses the head.
New checkpoint head roots therefore use journal policy.
The canonical checkpoint constructor has seven fields; its fourth field contains the optional designated parent.
Lean and native extraction use that field only.
The existing checkpoint branch-refusal control remains.
Legacy checkpoint roots retain their version-1 swap mapping.

The previous Gallina printer refuses the polymorphic `Head` field as `type _uniq.9`.
`retained-controls/head-parameter-refusal.log` retains that result.
The preparation extends structure printing with explicit type parameters.
The actual regenerated Skeleton remains byte-identical to production.

## Native scope

The changed native library compiles in an isolated OCaml copy.
The root head generation uses `Z.t`.
Root moves use complete expectations, fixed policy and kind, and canonical designated parents.
The control-file wire still bounds encoded root generations and name lengths.
ST2 owns capacity and fault values around the writer.

The existing native disk operations retain their own APIs for node staging and publication.
This preparation does not claim that those operations implement atomic `Txn` or `Cut` yet.
ST2 owns the writer and crash comparison.

Native bytecode controls use actual library modules.
They pass legacy-policy mapping, new policy separation, staleness, pins, ancestry, exact names, and exact arithmetic.
The full native copy uses the coordinator's consistent S0 generated outputs.
The actual changed Lean producer emits the root goldens.
`test_control`, `test_cas`, `test_shared_facts`, `test_checkpoint`, and `test_crash` each exit zero.
The coordinator's updated `test_bytes` also exits zero in the isolated native copy.


## Legacy image boundary

The finite version-1 control retains generation two after decoding.
A new create followed by an identical duplicate retains generation one.
The same bytes therefore do not imply the same canonical event history.
ST2 must preserve legacy generations without fabricating a `Cas.reached` witness.
A verified import event or a separate checked-image boundary remains open.

## Retained corrections

Actual M2 admission goldens now agree with native `put` for the handle control.
The coordinator applies this correction in ST1a.
The ST1b native copy keeps those exact G2 bytes and requires every admission row to agree.
The initial final Rocq compile finds a type/projection collision at `root_policy`.
`retained-controls/root-policy-projection-collision.log` retains that failure.
The type uses `root_policy_kind`; the root field keeps `root_policy`.

## Commands and evidence

Run Lean only through the shared serialized wrapper from the production working directory.
The final combined command is:

```text
python3 /private/tmp/seams-lean-one.py lake env python3 /private/tmp/seams-st1b-sol/final-lean.py
```

`final-lean.log` records each fixture, audit, and actual producer exit.
`rocq-st1b.log` records actual Rocq compilation.
Each native suite has its own log and explicit exit status.
`manifest.json` records exact input and output hashes for every changed path.
`patch-check.log` records read-only application checking against the current ST1a production tree.

The native checks are finite host evidence.
The Lean laws are proofs under the named axiom ceiling.
Neither evidence establishes a native transaction writer theorem.
The coordinator owns registry placement, root imports, production gates, and the commit.


## Application packet

`st1b-all.patch` contains the complete change against the recorded ST1a preimages.
The component patches split core, export, native, fixtures, and generated goldens.
Apply either the combined patch or its components, never both.
Do not copy the isolated build libraries or intermediate assembly scripts into production.
The helper patch adds only the generated policy pair to `FILES`.
The coordinator's cross-artifact alias check remains unchanged.
No patch touches `scripts/generate.py`.

Transactions and HeadPrinter need the coordinator's `Test/All.lean` anchor.
The coordinator retains SeamsTransactionsAudit as a receipt audit input.
The registry placement in `PLACEMENT.md` needs the coordinator's semantics and registry anchors.
The production application needs its narrow build, named audit, reached generators, and relevant behaviour gate.
The packet contains no root-import or register edits.


## Canonical policy table

`RootPolicy.all`, `RootPolicy.byte`, and `RootPolicy.name` in `src/Effect4/Store/Domain/Transaction.lean` own policy data.
The existing Facts producer emits `e4_root_policy.ml` and its interface.
Native control re-exports that generated type and delegates its byte, inverse, and name functions.
The version-1 decoder keeps only its explicit legacy mapping.
The helper adds both outputs to publication and comparison using the existing alias guard.
The shared-facts fixture reads the actual generated map.
A disposable native copy changes journal byte decoding to swap.
The actual shared-facts fixture exits two with `Failure("policy byte round trip")`.
The unmodified generated map passes that same fixture.


## Final verification results

The combined Lean run exits zero after rebuilding the changed core modules, fixtures, printer, and facts producer.
Its named audit covers 1404 declarations within `[propext, Quot.sound]`, with no planned goals.
The actual producers emit the updated Rocq code, goldens, and all three native fact pairs.
The final golden run uses `RootPolicy.byte` directly, removing the temporary duplicated index map.
`generate-goldens.log` records its zero exit.

The actual Rocq output matches the separately tested naming correction byte for byte.
`Eff_types`, `StoreCode`, `StoreLaws`, `StoreGrammar`, and `StoreAssumptions` compile with exit zero.
The printed assumptions retain their existing primitive and codec premises.
This run adds no root or crash theorem to Rocq.

All five root-related native suites pass after installing the actual new policy fact pair.
`test_bytes` passes with the coordinator's current ST1a repair.
`policy-native-red.log` records the exact mutated source hash and the expected fixture failure.
The original policy-map output remains unchanged in the deliverable.

`patch-check.log` records successful read-only application checking.
`manifest.json` lists every changed path and pins its exact base and resulting bytes.
The source tree and generated pairs are ready for the coordinator's production application.
