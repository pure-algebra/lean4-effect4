# P2a type lane receipt — 2026-09-11

## Current landing status

| Slice | Commit | Acceptance |
| --- | --- | --- |
| 1 — absorption and product distribution | `5db3329` | Required gates accepted under the unchanged declared-red policy |
| 2 — canonical order and public boundaries | `73ae302` | Required gates accepted under the unchanged declared-red policy |
| 3 — integer admission and error carrier | This commit | Required gates accepted under the unchanged declared-red policy |

One checkout, the original branch, three sequential commits; no push. Exact
proof names, axiom output, generator paths and gate output are recorded per
slice below. The original stopped review is retained as historical evidence.

## Resumption under the owner's amendments

The owner accepted the three findings below and authorized resumption. The
historical review below records the initial stop, not the current implementation
status. The accepted amendments are recorded in `docs/DESIGN-ISSUES.md` and the
formal-foundations amendment in `Test/contracts/foundation-wave2.contract.md`:

- Distribution is confined to normalization. `Ty.sub` and `sub_union_right` stay
  unchanged; canonical order laws replace the removed two distribution laws and
  the removed two-way normalization law. The one-way implication is attempted
  separately.
- Error support becomes `rawSupportedErrTy` after normalization; admission keeps
  its existing composition.
- Integer schemas continue to parse. Only program admission refuses types that
  mention `int`, reporting their path. Both schema retractions remain unchanged.
- Parallel Lean compilation is explicitly permitted for this scope. Concurrent
  checks use separate outputs and bounded thread counts; generator writes remain
  coordinated.

The current implementation receipt follows the historical initial review. That
review describes the earlier stopped checkout only; its unimplemented proposals
are superseded by the owner amendments above.

## Historical initial statement review

Stopped before commit 1 under the dispatch's explicit rule: "If a theorem needs a
statement change to be true, stop and write the counterexample into the receipt
instead of weakening the law silently." No P2a implementation was landed. Lean
checked counterexamples to the error-support equality and contradictions between
the requested changes and two existing theorem statements. The proposed amendments
below are not rulings and have not been applied.

## Checkout and scope

- Main checkout: `/Users/pooks/Dev/lean4-effect4`; no new worktree or branch.
- Branch: `refactor/phase1-phase3`.
- Base and final HEAD: `2c234bc9d8ad546703939d9bcd38f795c874948d`.
- Inherited modifications: `ocaml/engine/api_engine.ml`, `ocaml/gen/api_gen.ml`.
  Both retain their entry SHA-256 values, listed below.
- Authored files: this receipt and
  `docs/research/2026-09-11-p2a-type-lane-evidence/StatementProbe.lean`.
  Command logs accompany the probe; `COORDINATION.md` records the check and release.
- No changes to `src/`, `Test/`, generators, generated files, truth tapes, wire
  constructors, ordinals, values, decision registers or frozen contracts.
- Nothing staged, committed or pushed. Research files and coordination are ignored
  by Git. No Lean lane remains held.

Finishing criteria were three separate commits, each with its requested proofs,
counterexample batteries, generated-output path inventory and every required gate
accepted under the unchanged declared-red policy. The statement check stopped
that sequence before implementation.

## 1. Distribution requires changing `Ty.sub_union_right`

The current theorem at `src/Effect4/Program/Ty.lean:511` states:

```lean
theorem sub_union_right (a b1 b2 : Ty) (ha : isMember a = true) :
    sub a (.union b1 b2) = (sub a b1 || sub a b2)
```

`isMember` permits a product whose child is a union. Take:

```lean
numberPair      := prod nat bool
stringPair      := prod string bool
factoredPair    := prod (union nat string) bool
distributedPair := union numberPair stringPair
```

At the unchanged checkout, `sub factoredPair distributedPair = false`, while
`sub numberPair distributedPair && sub stringPair distributedPair = true`.
That is a tested counterexample to `sub_prod_union_left` for the old `sub`; updating
`sub` is an intended part of P2a, so this finite observation alone is not the blocker.

The stronger, proved obstruction is
`P2aStatementCheck.distribution_conflicts_with_existing_union_right`.
For **any** proposed subtype function, the existing `sub_union_right` statement,
the requested `sub_prod_union_left` statement, reflexivity, and the existing refusal
of both `numberPair <: stringPair` and its reverse imply `False`.
Distribution makes the factored product fit the distributed union; the existing
right-union rule rejects it because it fits neither whole branch.

**Proposed amendment:** restrict `sub_union_right` to atomic canonical source types
(retain `isMember a = true` and add `Canonical a`), or an explicitly equivalent
condition excluding distributable products. Re-prove `hasTy_sub` with product
distribution handled separately. This changes an existing theorem's premise;
re-proving the unchanged statement cannot fix the contradiction. The proposed
replacement theorem has not been proved here.

## 2. The required `supportedErrTy_normalize` equality is false

The required statement from packet section 4 is:

```lean
supportedErrTy t = supportedErrTy t.normalize
```

The unchanged predicate at `src/Effect4/Program/Eff.lean:50` accepts a product
only when its first component passes `isTagTy` and its second component is
literally `.string`. Two checked witnesses are:

| `t` | `t.normalize` | `supportedErrTy t` | `supportedErrTy t.normalize` |
| --- | --- | --- | --- |
| `prod string (union string string)` | `prod string string` | `false` | `true` |
| `prod string (union string never)` | `prod string string` | `false` | `true` |

These witnesses contain no integer type. Both already pass `admittedErrTy`,
which deliberately normalizes before applying the raw predicate
(`src/Effect4/Program/Eff.lean:57–59`).

This is not an artifact of testing only the old normalizer.
`P2aStatementCheck.support_invariance_conflicts_with_duplicate_erasure` proves that
**any** replacement normalizer sending the first witness to `prod string string`
contradicts the requested equality if the raw support predicate stays unchanged.
The proposed normalization still erases that duplicate, whether it normalizes
the child first or distributes the product and then deduplicates.

**Proposed amendment:** retain the structural predicate under an explicit raw name
for its image proofs, and make the public `supportedErrTy` apply that predicate to
`normalize t`. This keeps the requested equality as written but explicitly changes
what its predicate means; its proof follows from normalization idempotence.
Existing admission decisions should remain unchanged because `admittedErrTy`
already uses this composition. That preservation and the image laws still require
proof and tests. No predicate was changed here.

## 3. Canonicality does not supply integer refusal

`CTy` at `src/Effect4/Program/Ty.lean:567` witnesses only
`normalize t = t`. `int` is canonical, so it is still a member of `CTy`.
`Ty.schema int` currently produces the integer-number representation, and
`Ty.ofSchema` currently reads it back as `some int`
(`src/Effect4/Schema/Bridge.lean:69`). Unlike the older packet's description,
the live single-`isInt` branch returns `int`, not `nat`.

The existing theorem at `src/Effect4/Schema/Bridge.lean:158` already quantifies
over `CTy`:

```lean
theorem ofSchema_schema_cty (t : CTy) :
    ofSchema (schema t.toRaw) = some t.toRaw
```

If `ofSchema (schema int) = none` as required by the integer refusal, its
instance at the canonical integer demands `none = some int`.
`P2aStatementCheck.int_refusal_conflicts_with_current_cty_retraction` proves this
contradiction for any replacement reader, conditional on retaining the existing
integer schema output. Moving a raw law to `CTy` alone cannot solve it.

**Proposed amendment:** retain total canonicalization and `CTy`, make schema import
refuse integers explicitly, and state the schema retraction on canonical types
with an explicit premise excluding `int` throughout the type. Apply the same
admission-domain distinction at other affected boundaries. Do not claim that
canonicality itself certifies admission. This restricts an existing theorem's
domain and therefore needs the owner's ruling under the dispatch stop rule.

## Checked commands and results

All Lean commands ran from the main checkout with `LEAN_NUM_THREADS=3`, sequentially
under `.lake/LANE.lock` acquired with `mkdir` and released with `rmdir`.

```sh
LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.TypeAlgebra Effect4.Schema.Bridge
LEAN_NUM_THREADS=3 lake env lean -M 3072 docs/research/2026-09-11-p2a-type-lane-evidence/StatementProbe.lean
git diff --check
```

- Dependency build: exit 0, `Build completed successfully (44 jobs).`
  Lake checked the target freshness and replayed cached module output; this was
  not a clean rebuild or the full repository gate. Existing lint warnings were
  replayed from Frames, Timer and TypeAlgebra. Log:
  [dependency-build.log](2026-09-11-p2a-type-lane-evidence/dependency-build.log).
- Final probe: exit 0; nine `#guard` checks and nine named proof declarations;
  no warnings or errors. Log:
  [statement-probe.log](2026-09-11-p2a-type-lane-evidence/statement-probe.log).
- `git diff --check`: exit 0.
- A first attempt at the added subtype proofs failed because `decide` could not
  unfold the well-founded subtype function and three Boolean calculations
  needed explicit reduction. Its compiler-generated `sorryAx` output is **not
  accepted evidence**. The failed log is retained as
  [statement-probe-first-subtype-attempt.log](2026-09-11-p2a-type-lane-evidence/statement-probe-first-subtype-attempt.log).
  The saved probe was repaired and rerun; the final log below has no `sorryAx`.

Exact final `#print axioms` output:

```text
'P2aStatementCheck.repeated_payload_normalizes' depends on axioms: [propext, Quot.sound]
'P2aStatementCheck.supportedErrTy_normalize_counterexample' depends on axioms: [propext, Quot.sound]
'P2aStatementCheck.supportedErrTy_normalize_bottom_counterexample' depends on axioms: [propext, Quot.sound]
'P2aStatementCheck.support_invariance_conflicts_with_duplicate_erasure' depends on axioms: [propext]
'P2aStatementCheck.int_is_canonical' depends on axioms: [propext, Quot.sound]
'P2aStatementCheck.int_schema_roundtrip_current' depends on axioms: [propext]
'P2aStatementCheck.int_refusal_conflicts_with_current_cty_retraction' depends on axioms: [propext, Quot.sound]
'P2aStatementCheck.current_sub_prod_union_left_counterexample' depends on axioms: [propext, Quot.sound]
'P2aStatementCheck.distribution_conflicts_with_existing_union_right' does not depend on any axioms
```

The concrete examples are finite checks with accompanying proofs. The three
conditional contradiction theorems quantify over replacement functions under
their written hypotheses. Neither kind is evidence of a P2a implementation or
of host behavior.

## Historical preflight commit and gate ledger

| Requested commit | Result | Moved `.ty` goldens and printed types |
| --- | --- | --- |
| 1 — absorption and distribution | Not started; stopped on the statement conflicts above | None |
| 2 — the order and canonical boundaries | Not started | None |
| 3 — integer refusal and error carrier | Not started | None |

No implementation theorem from the dispatch is claimed proved.
The full `lake build`, repository axiom/module-closure gate, `bash scripts/sweep.sh`,
31-program truth gate and OCaml layout differential were **not run**. The
37-type battery, planted implementation tests, generation/check-generated and
before/after compatibility comparisons were **not run**. The user required the
lane to stop on a false law, and there was no candidate commit to validate.
No declared-red policy, gate or golden was changed.

The packet's `scripts/check-compat.sh` pathname is absent from this checkout;
`scripts/check-compatibility.py` is present. Resolving its exact baseline/candidate
invocation remains work for the resumed lane, not a reported compatibility pass.

Inherited OCaml file SHA-256 values matched before and after the checks:

```text
c8674fd5344de239e5afb1e39d1ca10030bde816b1ee6576f7db36845b583128  ocaml/engine/api_engine.ml
6e999dbf0b67e174d2b535e637830b359fd32e882910acb8ed31fec03438100b  ocaml/gen/api_gen.ml
```

Resume after the owner accepts or replaces the three proposed amendments.
Then update the tracked ruling/contract as authorized, land P2a in the requested
three-commit order, and append each accepted gate receipt here.


## Commit 1 — absorption and product distribution

Candidate based on `2c234bc9d8ad546703939d9bcd38f795c874948d`, on the same
`refactor/phase1-phase3` branch and main checkout. No new worktree. This section
belongs to the commit containing it; commits 2 and 3 remain separate obligations.

### Changes and proof graph

`Row.antichain` filters strictly dominated elements, retaining input order. Its
membership and idempotence laws require no order assumptions; the coverage and
append laws explicitly require reflexivity and transitivity. Normalized type
unions first sort and deduplicate, then take this antichain. Products expand both
normalized factors; lists and all other constructors only normalize their children.
Explicit `never` product factors are retained. The subtype function and
`sub_union_right` have exactly their previous text; the definition moved earlier
so normalization can call it. Subtyping never calls normalization.

The proof graph is:

1. Generic antichain membership, coverage and idempotence.
2. Structural subtype transitivity (`sub_trans_core`, private in TypeAlgebra),
   supplying coverage for type rows; no distribution rule added to subtyping.
3. `Normal` requires maximal rows and product factors with no union at their head.
   `normal_normalize` and `Normal.fixed` give the unchanged `normalize_idem` law.
4. Existing `hasTy_sub` plus antichain coverage preserve the exact Boolean
   `Val.hasTy` judgment. Product membership gives `hasTy_normalize` for every
   value, type and fiber table under its unchanged statement.
5. Row coverage and maximality re-establish the existing join algebra and CTy laws.

The owner separately approved the necessary helper statement changes after the
second statement-check pause: `normalize_ofMembers_fixed` now requires maximality;
`join_eq_ofMembers` and `members_join` include the antichain. The checked witness
is `[string, lit "A"]`: sorted, individually fixed atoms normalize to `string`,
so the former equations are false. The repaired probe and exact output are in
`AbsorptionStatementProbe.lean` and `absorption-statement-probe-final.log` in the
local evidence directory (untracked working notes). The failed first probe is
retained and is not accepted evidence. The tracked DI and contract record the
approved amendment; no helper law was silently weakened.

The existing Row assurance census was extended from 72 to 87 owned declarations,
44 to 56 authored API names and 32 to 43 theorem receipts. No gate exemption was
added. Two existing host-session certificates now use kernel reduction (`cbv`)
because `decide` no longer unfolds the well-founded subtype computation there.
The handwritten OCaml typing mirror and its normalization tests were updated to
match the new normalizer.

### Batteries and exact proof output

The exact Seat A universe has 37 types. Its canonical images have zero mutual-
subtype/different-representative pairs and zero non-absorptions. Planted literal
and product absorption, distribution on both product sides, list non-distribution
and explicit `never` product factors all pass in `Test/Program/TypeAlgebraContract.lean`.
This is a finite battery, distinct from the universal Lean theorems.

Command: `LEAN_NUM_THREADS=2 lake env lean -M4096 Test/Program/TypeAlgebraAxiomReport.lean`.
Fresh output (all names, including retained regression laws):

```text
'Effect4.Row.antichain' does not depend on any axioms
'Effect4.Row.antichain_subset' depends on axioms: [propext]
'Effect4.Row.mem_antichain_iff' depends on axioms: [propext]
'Effect4.Row.antichain_idem' depends on axioms: [propext, Quot.sound]
'Effect4.Row.antichain_coverage' depends on axioms: [propext]
'Effect4.Row.antichain_append_left' depends on axioms: [propext, Quot.sound]
'Effect4.Row.antichain_append_right' depends on axioms: [propext, Quot.sound]
'Effect4.Row.antichain_sublist' depends on axioms: [propext]
'Effect4.Row.antichain_pairwise' depends on axioms: [propext]
'Effect4.Row.ascending_antichain' depends on axioms: [propext]
'Effect4.Row.antichain_eq_self_iff' depends on axioms: [propext, Quot.sound]
'Effect4.Row.antichain_singleton' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.factors_isFactor' depends on axioms: [propext]
'Effect4.Program.Ty.factors_singleton' depends on axioms: [propext]
'Effect4.Program.Ty.mem_normalizeRow' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.Normal.members' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.Normal.factors' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.normal_row' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.normal_normalize' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.normalize_ofMembers_fixed' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.Normal.fixed' depends on axioms: [propext, Quot.sound]
'Effect4.Program.hasTy_normalizeRow' depends on axioms: [propext, Quot.sound]
'Effect4.Program.hasTy_factors' depends on axioms: [propext]
'Effect4.Program.hasTy_productMembers' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.Normal.members_ascending' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.Normal.ofMembers_members' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.Normal.members_maximal' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.normalizeRow_congr' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.normalizeRow_append_comm' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.normalizeRow_coverage' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.normalizeRow_append_left' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.normalizeRow_append_right' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.normalizeRow_fixed' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.join_eq_ofMembers' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.normalize_join' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.members_join' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.key_injective' depends on axioms: [propext]
'Effect4.Program.Ty.ltKey_iff_lex' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.instIsLinearOrder' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.instLawfulOrderLT' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.normalize_idem' depends on axioms: [propext, Quot.sound]
'Effect4.Program.CTy.ofRaw' depends on axioms: [propext, Quot.sound]
'Effect4.Program.CTy.ofRaw_toRaw' depends on axioms: [propext, Quot.sound]
'Effect4.Program.hasTy_fibers' depends on axioms: [propext]
'Effect4.Program.hasTy_fibers_nil' depends on axioms: [propext]
'Effect4.Program.hasTy_normalize' depends on axioms: [propext, Quot.sound]
'Effect4.Program.hasTy_of_normalize_eq' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.join_comm' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.join_assoc' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.join_self' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.join_never' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.join_never_right' depends on axioms: [propext, Quot.sound]
'Effect4.Program.CTy.join_self' depends on axioms: [propext, Quot.sound]
'Effect4.Program.CTy.join_never' depends on axioms: [propext, Quot.sound]
'Effect4.Program.CTy.join_comm' depends on axioms: [propext, Quot.sound]
'Effect4.Program.CTy.join_assoc' depends on axioms: [propext, Quot.sound]
```

### Generated outputs

No `.ty` golden body or printed TypeScript type body moved. All generated files
were regenerated by their existing producers. Of 343 generated paths changed,
341 change provenance only; the two semantic bodies are
`ocaml/engine/api_engine.ml` and `ocaml/gen/api_gen.ml`. Their inherited entry
changes were provenance-only, and the current files are complete producer outputs.
Frozen `ocaml/gen/fibers_gen.ml` and `ocaml/gen/machine_gen.ml` remain untouched.
Truth tapes were regenerated through the existing recording command; only their
six provenance sidecars moved, not their tape bodies.

Producers (all final runs exit 0):

```sh
LEAN_NUM_THREADS=2 bash scripts/generate.sh
LEAN_NUM_THREADS=2 bash scripts/generate.sh --only lcnf
python3 scripts/generate-engine-structure.py
LEAN_NUM_THREADS=2 bash scripts/generate-host-protocol.sh
LEAN_NUM_THREADS=2 lake env lean -M4096 --run harness/truth/Truth.lean harness/truth/corpus.json --tapes harness/truth/tapes
bun run harness/truth/run-truth.ts --manifest harness/truth/corpus.json --out harness/truth --timeout 300 --tape-out harness/truth/tapes
```

The first generation run was interrupted at the helper-statement pause (exit 130),
then rerun after approval. A second complete generator pass refreshed derived
provenance after the direct tool import had been rebuilt. No generated file was
edited by hand. Every changed generated path follows (`body` marks the two
semantic changes; all others are provenance-only):

```text
harness/truth/corpus.json.cut-from
harness/truth/generated/p42.ts
harness/truth/generated/pAcquire.ts
harness/truth/generated/pAcquireClosed.ts
harness/truth/generated/pAcquireHandle.ts
harness/truth/generated/pAwait.ts
harness/truth/generated/pBind.ts
harness/truth/generated/pCatch.ts
harness/truth/generated/pCatchError.ts
harness/truth/generated/pCatchIfHit.ts
harness/truth/generated/pCatchIfMiss.ts
harness/truth/generated/pCatchIfRetained.ts
harness/truth/generated/pDiamond.ts
harness/truth/generated/pFailBoomText.ts
harness/truth/generated/pFailTagged.ts
harness/truth/generated/pFailText.ts
harness/truth/generated/pFork.ts
harness/truth/generated/pGen.ts
harness/truth/generated/pKv.ts
harness/truth/generated/pLoop.ts
harness/truth/generated/pMergeAll.ts
harness/truth/generated/pProvide.ts
harness/truth/generated/pProvideMerge.ts
harness/truth/generated/pProvideTwice.ts
harness/truth/generated/pScope.ts
harness/truth/generated/pSqlCatch.ts
harness/truth/generated/pSqlExit.ts
harness/truth/generated/pSqlFail.ts
harness/truth/generated/pSqlOrDie.ts
harness/truth/generated/pSqlite.ts
harness/truth/generated/pTextOrDie.ts
harness/truth/generated/pTwo.ts
harness/truth/result.json.cut-from
harness/truth/result.md
harness/truth/session/protocol.gen.ts
harness/truth/session/tape.schema.json.cut-from
harness/truth/tapes/pKv.jsonl.cut-from
harness/truth/tapes/pSqlCatch.jsonl.cut-from
harness/truth/tapes/pSqlExit.jsonl.cut-from
harness/truth/tapes/pSqlFail.jsonl.cut-from
harness/truth/tapes/pSqlOrDie.jsonl.cut-from
harness/truth/tapes/pSqlite.jsonl.cut-from
ocaml/eff/eff_json.ml
ocaml/eff/eff_layout.ml
ocaml/eff/eff_manifest.txt.cut-from
ocaml/eff/eff_native.ml
ocaml/eff/eff_types.ml
ocaml/eff/eff_wire.ml
ocaml/eff/goldens/corpus.txt.cut-from
ocaml/eff/goldens/coverage-metadata.txt.cut-from
ocaml/eff/goldens/coverage.txt.cut-from
ocaml/eff/goldens/metadata.tsv.cut-from
ocaml/eff/goldens/p42.bin.cut-from
ocaml/eff/goldens/p42.json.cut-from
ocaml/eff/goldens/p42.ty.cut-from
ocaml/eff/goldens/pAcquire.bin.cut-from
ocaml/eff/goldens/pAcquire.json.cut-from
ocaml/eff/goldens/pAcquire.ty.cut-from
ocaml/eff/goldens/pActions.bin.cut-from
ocaml/eff/goldens/pActions.json.cut-from
ocaml/eff/goldens/pActions.ty.cut-from
ocaml/eff/goldens/pAwait.bin.cut-from
ocaml/eff/goldens/pAwait.json.cut-from
ocaml/eff/goldens/pAwait.ty.cut-from
ocaml/eff/goldens/pBind.bin.cut-from
ocaml/eff/goldens/pBind.json.cut-from
ocaml/eff/goldens/pBind.ty.cut-from
ocaml/eff/goldens/pBranch.bin.cut-from
ocaml/eff/goldens/pBranch.json.cut-from
ocaml/eff/goldens/pBranch.ty.cut-from
ocaml/eff/goldens/pCallback.bin.cut-from
ocaml/eff/goldens/pCallback.json.cut-from
ocaml/eff/goldens/pCallback.ty.cut-from
ocaml/eff/goldens/pCatch.bin.cut-from
ocaml/eff/goldens/pCatch.json.cut-from
ocaml/eff/goldens/pCatch.ty.cut-from
ocaml/eff/goldens/pCatchError.bin.cut-from
ocaml/eff/goldens/pCatchError.json.cut-from
ocaml/eff/goldens/pCatchError.ty.cut-from
ocaml/eff/goldens/pCatchIf.bin.cut-from
ocaml/eff/goldens/pCatchIf.json.cut-from
ocaml/eff/goldens/pCatchIf.ty.cut-from
ocaml/eff/goldens/pDiamond.bin.cut-from
ocaml/eff/goldens/pDiamond.json.cut-from
ocaml/eff/goldens/pDiamond.ty.cut-from
ocaml/eff/goldens/pExit.bin.cut-from
ocaml/eff/goldens/pExit.json.cut-from
ocaml/eff/goldens/pExit.ty.cut-from
ocaml/eff/goldens/pExternal.bin.cut-from
ocaml/eff/goldens/pExternal.json.cut-from
ocaml/eff/goldens/pExternal.ty.cut-from
ocaml/eff/goldens/pFailCause.bin.cut-from
ocaml/eff/goldens/pFailCause.json.cut-from
ocaml/eff/goldens/pFailCause.ty.cut-from
ocaml/eff/goldens/pFailText.bin.cut-from
ocaml/eff/goldens/pFailText.json.cut-from
ocaml/eff/goldens/pFailText.ty.cut-from
ocaml/eff/goldens/pFork.bin.cut-from
ocaml/eff/goldens/pFork.json.cut-from
ocaml/eff/goldens/pFork.ty.cut-from
ocaml/eff/goldens/pGen.bin.cut-from
ocaml/eff/goldens/pGen.json.cut-from
ocaml/eff/goldens/pGen.ty.cut-from
ocaml/eff/goldens/pIll.bin.cut-from
ocaml/eff/goldens/pIll.json.cut-from
ocaml/eff/goldens/pIll.ty.cut-from
ocaml/eff/goldens/pIllBranch.bin.cut-from
ocaml/eff/goldens/pIllBranch.json.cut-from
ocaml/eff/goldens/pIllBranch.ty.cut-from
ocaml/eff/goldens/pIllBreak.bin.cut-from
ocaml/eff/goldens/pIllBreak.json.cut-from
ocaml/eff/goldens/pIllBreak.ty.cut-from
ocaml/eff/goldens/pIllCallback.bin.cut-from
ocaml/eff/goldens/pIllCallback.json.cut-from
ocaml/eff/goldens/pIllCallback.ty.cut-from
ocaml/eff/goldens/pIllCatchIf.bin.cut-from
ocaml/eff/goldens/pIllCatchIf.json.cut-from
ocaml/eff/goldens/pIllCatchIf.ty.cut-from
ocaml/eff/goldens/pIllCauseBool.bin.cut-from
ocaml/eff/goldens/pIllCauseBool.json.cut-from
ocaml/eff/goldens/pIllCauseBool.ty.cut-from
ocaml/eff/goldens/pIllExternalDomain.bin.cut-from
ocaml/eff/goldens/pIllExternalDomain.json.cut-from
ocaml/eff/goldens/pIllExternalDomain.ty.cut-from
ocaml/eff/goldens/pIllFailBool.bin.cut-from
ocaml/eff/goldens/pIllFailBool.json.cut-from
ocaml/eff/goldens/pIllFailBool.ty.cut-from
ocaml/eff/goldens/pIllInterruptor.bin.cut-from
ocaml/eff/goldens/pIllInterruptor.json.cut-from
ocaml/eff/goldens/pIllInterruptor.ty.cut-from
ocaml/eff/goldens/pIllJoin.bin.cut-from
ocaml/eff/goldens/pIllJoin.json.cut-from
ocaml/eff/goldens/pIllJoin.ty.cut-from
ocaml/eff/goldens/pIllReq.bin.cut-from
ocaml/eff/goldens/pIllReq.json.cut-from
ocaml/eff/goldens/pIllReq.ty.cut-from
ocaml/eff/goldens/pIllRet.bin.cut-from
ocaml/eff/goldens/pIllRet.json.cut-from
ocaml/eff/goldens/pIllRet.ty.cut-from
ocaml/eff/goldens/pIllStep.bin.cut-from
ocaml/eff/goldens/pIllStep.json.cut-from
ocaml/eff/goldens/pIllStep.ty.cut-from
ocaml/eff/goldens/pIllVar.bin.cut-from
ocaml/eff/goldens/pIllVar.json.cut-from
ocaml/eff/goldens/pIllVar.ty.cut-from
ocaml/eff/goldens/pJoin.bin.cut-from
ocaml/eff/goldens/pJoin.json.cut-from
ocaml/eff/goldens/pJoin.ty.cut-from
ocaml/eff/goldens/pMasks.bin.cut-from
ocaml/eff/goldens/pMasks.json.cut-from
ocaml/eff/goldens/pMasks.ty.cut-from
ocaml/eff/goldens/pMatch.bin.cut-from
ocaml/eff/goldens/pMatch.json.cut-from
ocaml/eff/goldens/pMatch.ty.cut-from
ocaml/eff/goldens/pMergeAll.bin.cut-from
ocaml/eff/goldens/pMergeAll.json.cut-from
ocaml/eff/goldens/pMergeAll.ty.cut-from
ocaml/eff/goldens/pOnExit.bin.cut-from
ocaml/eff/goldens/pOnExit.json.cut-from
ocaml/eff/goldens/pOnExit.ty.cut-from
ocaml/eff/goldens/pOps.bin.cut-from
ocaml/eff/goldens/pOps.json.cut-from
ocaml/eff/goldens/pOps.ty.cut-from
ocaml/eff/goldens/pPair.bin.cut-from
ocaml/eff/goldens/pPair.json.cut-from
ocaml/eff/goldens/pPair.ty.cut-from
ocaml/eff/goldens/pProvide.bin.cut-from
ocaml/eff/goldens/pProvide.json.cut-from
ocaml/eff/goldens/pProvide.ty.cut-from
ocaml/eff/goldens/pScoped.bin.cut-from
ocaml/eff/goldens/pScoped.json.cut-from
ocaml/eff/goldens/pScoped.ty.cut-from
ocaml/eff/goldens/pSleep.bin.cut-from
ocaml/eff/goldens/pSleep.json.cut-from
ocaml/eff/goldens/pSleep.ty.cut-from
ocaml/eff/goldens/pStmts.bin.cut-from
ocaml/eff/goldens/pStmts.json.cut-from
ocaml/eff/goldens/pStmts.ty.cut-from
ocaml/eff/goldens/pStr.bin.cut-from
ocaml/eff/goldens/pStr.json.cut-from
ocaml/eff/goldens/pStr.ty.cut-from
ocaml/eff/goldens/pSuspend.bin.cut-from
ocaml/eff/goldens/pSuspend.json.cut-from
ocaml/eff/goldens/pSuspend.ty.cut-from
ocaml/eff/goldens/pSync.bin.cut-from
ocaml/eff/goldens/pSync.json.cut-from
ocaml/eff/goldens/pSync.ty.cut-from
ocaml/eff/goldens/pTwo.bin.cut-from
ocaml/eff/goldens/pTwo.json.cut-from
ocaml/eff/goldens/pTwo.ty.cut-from
ocaml/eff/goldens/pWhile.bin.cut-from
ocaml/eff/goldens/pWhile.json.cut-from
ocaml/eff/goldens/pWhile.ty.cut-from
ocaml/eff/goldens/pYieldError.bin.cut-from
ocaml/eff/goldens/pYieldError.json.cut-from
ocaml/eff/goldens/pYieldError.ty.cut-from
ocaml/eff/program-structure.json.cut-from
ocaml/engine/api_engine.ml [body]
ocaml/engine/cas/goldens/cases.txt.cut-from
ocaml/engine/cas/goldens/digest-01.hex.cut-from
ocaml/engine/cas/goldens/digest-02.hex.cut-from
ocaml/engine/cas/goldens/digest-03.hex.cut-from
ocaml/engine/cas/goldens/digest-04.hex.cut-from
ocaml/engine/cas/goldens/digest-05.hex.cut-from
ocaml/engine/cas/goldens/digest-06.hex.cut-from
ocaml/engine/cas/goldens/digest-07.hex.cut-from
ocaml/engine/cas/goldens/digest-08.hex.cut-from
ocaml/engine/cas/goldens/digest-09.hex.cut-from
ocaml/engine/cas/goldens/digest-10.hex.cut-from
ocaml/engine/cas/goldens/digest-11.hex.cut-from
ocaml/engine/cas/goldens/digest-12.hex.cut-from
ocaml/engine/cas/goldens/digest-13.hex.cut-from
ocaml/engine/cas/goldens/digest-14.hex.cut-from
ocaml/engine/cas/goldens/digest-15.hex.cut-from
ocaml/engine/cas/goldens/digest-16.hex.cut-from
ocaml/engine/cas/goldens/digest-17.hex.cut-from
ocaml/engine/cas/goldens/digest-18.hex.cut-from
ocaml/engine/cas/goldens/digest-19.hex.cut-from
ocaml/engine/cas/goldens/digest-20.hex.cut-from
ocaml/engine/cas/goldens/g1-anyref-frame.hex.cut-from
ocaml/engine/cas/goldens/g1-canonical-digest-frame.hex.cut-from
ocaml/engine/cas/goldens/g1-censusEntry.hex.cut-from
ocaml/engine/cas/goldens/g1-censusSchema.hex.cut-from
ocaml/engine/cas/goldens/g1-genesisNode.hex.cut-from
ocaml/engine/cas/goldens/g1-kind-annotation.hex.cut-from
ocaml/engine/cas/goldens/g1-kind-chunk.hex.cut-from
ocaml/engine/cas/goldens/g1-kind-component.hex.cut-from
ocaml/engine/cas/goldens/g1-kind-entry.hex.cut-from
ocaml/engine/cas/goldens/g1-kind-export.hex.cut-from
ocaml/engine/cas/goldens/g1-kind-fiber.hex.cut-from
ocaml/engine/cas/goldens/g1-kind-manifest.hex.cut-from
ocaml/engine/cas/goldens/g1-kind-program.hex.cut-from
ocaml/engine/cas/goldens/g1-kind-query.hex.cut-from
ocaml/engine/cas/goldens/g1-kind-result.hex.cut-from
ocaml/engine/cas/goldens/g1-kind-schema.hex.cut-from
ocaml/engine/cas/goldens/g1-kind-source.hex.cut-from
ocaml/engine/cas/goldens/g1-kind-tree.hex.cut-from
ocaml/engine/cas/goldens/g1-kind-type.hex.cut-from
ocaml/engine/cas/goldens/g1-kind-vector.hex.cut-from
ocaml/engine/cas/goldens/g1-probeEntry.hex.cut-from
ocaml/engine/cas/goldens/g1-probeSchema.hex.cut-from
ocaml/engine/cas/goldens/g1-sampleEntry-payload.hex.cut-from
ocaml/engine/cas/goldens/g1-sampleNode.hex.cut-from
ocaml/engine/cas/goldens/g2-badVersion.hex.cut-from
ocaml/engine/cas/goldens/g2-conflict.hex.cut-from
ocaml/engine/cas/goldens/g2-dangling-spec.hex.cut-from
ocaml/engine/cas/goldens/g2-dangling-zero.hex.cut-from
ocaml/engine/cas/goldens/g2-entry-duplicate.hex.cut-from
ocaml/engine/cas/goldens/g2-entry-fresh.hex.cut-from
ocaml/engine/cas/goldens/g2-genesis-exempt.hex.cut-from
ocaml/engine/cas/goldens/g2-handle-in-content.hex.cut-from
ocaml/engine/cas/goldens/g2-malformedRef-kind.hex.cut-from
ocaml/engine/cas/goldens/g2-malformedRef-length.hex.cut-from
ocaml/engine/cas/goldens/g2-occupant.hex.cut-from
ocaml/engine/cas/goldens/g2-ref-fresh.hex.cut-from
ocaml/engine/cas/goldens/g2-schema-duplicate.hex.cut-from
ocaml/engine/cas/goldens/g2-wrongKind.hex.cut-from
ocaml/engine/cas/goldens/g3-advance-v2.hex.cut-from
ocaml/engine/cas/goldens/g3-dangling.hex.cut-from
ocaml/engine/cas/goldens/g3-roots-after-v1.hex.cut-from
ocaml/engine/cas/goldens/g3-roots-after-v2.hex.cut-from
ocaml/engine/cas/goldens/g3-stale.hex.cut-from
ocaml/engine/cas/goldens/g3-v1.hex.cut-from
ocaml/engine/cas/goldens/g3-wrongKind.hex.cut-from
ocaml/engine/cas/goldens/g4-after-delete-get.hex.cut-from
ocaml/engine/cas/goldens/g4-after-delete.hex.cut-from
ocaml/engine/cas/goldens/g4-after-insert-get.hex.cut-from
ocaml/engine/cas/goldens/g4-after-insert.hex.cut-from
ocaml/engine/cas/goldens/g4-after-update.hex.cut-from
ocaml/engine/cas/goldens/g4-entries-base.hex.cut-from
ocaml/engine/cas/goldens/g4-entries-deleted.hex.cut-from
ocaml/engine/cas/goldens/g4-entries-inserted.hex.cut-from
ocaml/engine/cas/goldens/g4-entries-updated.hex.cut-from
ocaml/engine/cas/goldens/g4-entryAt-nested-key.hex.cut-from
ocaml/engine/cas/goldens/g4-entryAt-own.hex.cut-from
ocaml/engine/cas/goldens/g4-entryAt-parent-miss.hex.cut-from
ocaml/engine/cas/goldens/g4-entryAt-root.hex.cut-from
ocaml/engine/cas/goldens/g4-get-cycle-own.hex.cut-from
ocaml/engine/cas/goldens/g4-get-cycle.hex.cut-from
ocaml/engine/cas/goldens/g4-get-grandparent-nested.hex.cut-from
ocaml/engine/cas/goldens/g4-get-grandparent.hex.cut-from
ocaml/engine/cas/goldens/g4-get-miss.hex.cut-from
ocaml/engine/cas/goldens/g4-get-own.hex.cut-from
ocaml/engine/cas/goldens/g4-get-parent.hex.cut-from
ocaml/engine/cas/goldens/g5-bytes-inside-list.hex.cut-from
ocaml/engine/cas/goldens/g5-bytes-is-a-leaf.hex.cut-from
ocaml/engine/cas/goldens/g5-ctor-seed.hex.cut-from
ocaml/engine/cas/goldens/g5-handle-is-a-leaf.hex.cut-from
ocaml/engine/cas/goldens/g5-malformed-kind.hex.cut-from
ocaml/engine/cas/goldens/g5-malformed-length.hex.cut-from
ocaml/engine/cas/goldens/g5-malformed-nested.hex.cut-from
ocaml/engine/cas/goldens/g5-nested.hex.cut-from
ocaml/engine/cas/goldens/g5-no-refs.hex.cut-from
ocaml/engine/cas/goldens/g5-order.hex.cut-from
ocaml/engine/cas/goldens/g6-closure-a.hex.cut-from
ocaml/engine/cas/goldens/g6-closure-b.hex.cut-from
ocaml/engine/cas/goldens/g6-closure-empty.hex.cut-from
ocaml/engine/cas/goldens/g6-closure-tree-a.hex.cut-from
ocaml/engine/cas/goldens/g6-closure-tree-b.hex.cut-from
ocaml/engine/cas/goldens/g6-nodes-a.hex.cut-from
ocaml/engine/cas/goldens/g6-nodes-b.hex.cut-from
ocaml/engine/cas/goldens/g6-probeWord-replayed.hex.cut-from
ocaml/engine/cas/goldens/g6-probeWord-reversed.hex.cut-from
ocaml/engine/cas/goldens/g6-probeWord.hex.cut-from
ocaml/engine/cas/goldens/g6-replay-a.hex.cut-from
ocaml/engine/cas/goldens/g6-replay-b.hex.cut-from
ocaml/engine/cas/goldens/g6-treeNode.hex.cut-from
ocaml/engine/cas/goldens/g7-dangling-edge.hex.cut-from
ocaml/engine/cas/goldens/g7-flipped-payload.hex.cut-from
ocaml/engine/cas/goldens/g7-good.hex.cut-from
ocaml/engine/cas/goldens/g7-replayed.hex.cut-from
ocaml/engine/cas/goldens/g7-root-ok.hex.cut-from
ocaml/engine/cas/goldens/g7-root-wrong-kind.hex.cut-from
ocaml/engine/cas/goldens/g7-wrong-key.hex.cut-from
ocaml/engine/cas/goldens/manifest.txt.cut-from
ocaml/engine/cas/goldens/val_handle.hex.cut-from
ocaml/engine/cas/goldens/val_ref.hex.cut-from
ocaml/engine/e4_program_layout.json.cut-from
ocaml/engine/e4_program_layout.ml
ocaml/gen/api_gen.ml [body]
ocaml/goldens/eff/manifest.txt.cut-from
ocaml/goldens/eff/p42.hex.cut-from
ocaml/goldens/eff/pAwait.hex.cut-from
ocaml/goldens/eff/pBind.hex.cut-from
ocaml/goldens/eff/pCatch.hex.cut-from
ocaml/goldens/eff/pFork.hex.cut-from
ocaml/goldens/eff/pGen.hex.cut-from
ocaml/goldens/eff/pLoop.hex.cut-from
ocaml/goldens/eff/pScope.hex.cut-from
ocaml/goldens/eff/same-programs.txt.cut-from
src/Effect4/Laws/Program/Typing/Specs.lean
src/Effect4/Program/Derived.lean
src/Effect4/Store/Derived/Json.lean
src/Effect4/Store/Derived/Schema.lean
src/Effect4/Store/PinDerived.lean
ts/eff/eff.gen.ts
ts/eff/forms.gen.ts
ts/eff/ingest/README.md
ts/eff/json.gen.ts
ts/eff/packages.gen.ts
ts/eff/profile.gen.ts
ts/eff/taxonomy.gen.ts
ts/eff/wire.gen.ts
```

### Gates and remaining limits

Final gate ledger is completed before this candidate is committed. Full logs are
under `docs/research/2026-09-11-p2a-type-lane-evidence/` (untracked working notes).
This receipt embeds the decisive outputs so the commit remains reviewable without
that directory.

- `LEAN_NUM_THREADS=2 lake build`: PASS, 311 jobs. The first attempt exposed two
  reduction certificates and the Row census; both were repaired and the full
  build rerun. `commit1-build-final.log` and `commit1-build-regenerated.log`.
- `bash scripts/check-library-roots.sh`: PASS, 92 API/utility and 53 Laws-only
  modules; the axiom audit checked 278 modules and 43,996 declarations. Semantic
  and test declarations stay at `[propext, Quot.sound]`; the unchanged explicit
  implementation boundary admits `Classical.choice` at 36 names in 7 modules.
  No new axiom or module exemption. `commit1-library-roots.log`.
- `bash scripts/check-truth.sh`: PASS, 31 programs; bounded exits and schedules
  agree with rc.112 and regenerated modules type-check. `commit1-truth-gate.log`.
- OCaml handwritten tests: PASS, including 864 normalization controls over the
  9-type grid. Engine tests: PASS, 107 checks. Generator check: PASS.
- Maintained OCaml layout differential: PASS, 32/32 declarations translated and
  20,387 structural cases, with zero refusal, counterexample or unresolved cases.
  Fresh `ocamlopt` compilation passed; 1,330 vectors with six observations each
  matched expected output byte-for-byte (`cmp` exit 0). Structural join audit:
  4/4 matches and 138/138 recovered layout entries. Commands use the maintained
  `Conform.Cli.LcnfMl` and `Conform.Effect4.OCamlJoin` tools, not the old research
  reproducer. Logs `commit1-layout-{emission,compile,audit}.log`.

The auxiliary historical compatibility snapshot script did not produce a verdict:
its current parser rejects the metadata form `let families : List Lean.Name := [`;
its HEAD-baseline path also compares against the older retained constructor list.
The independently emitted before/after reflections have 56 identical families.
This is evidence of those reflected family shapes only, not a compatibility-gate
pass. No frozen baseline or compatibility parser was changed.

`git diff --check` reports 11 whitespace-only lines emitted by the existing LCNF
producer in `ocaml/engine/api_engine.ml`. The generated output was left intact;
this formatting check is not reported as green. The required build, proof, module,
sweep, truth and layout gates are recorded separately.


The first full sweep reported a source-citation failure: the formal packet link in
DI-15 lacked its required `(untracked working note)` annotation. That annotation
was repaired, and `bash scripts/check-source-citations.sh` passed. The first red
sweep is retained in `commit1-sweep.log`; its final replacement appears below.
The declared-red rule remains exactly the two frozen flat-LCNF projections in the
existing generated-stale check. No gate was weakened or hidden.

The default sandbox prevented Git from creating `.git/index.lock` during staging.
The reviewed, explicit path inventory was then staged through the approved Git
write tool. No files outside that inventory were staged and nothing was pushed.


The first full sweep completed all 18 gates in 921 seconds: 17 accepted (including
one declared-red verdict), with only the repaired source-citation issue red. The
host protocol comparison covered 57 runs, 52 programs and 29 negative controls;
the ingestion gate compared 23,394 program decodings and passed its separate
original/reprinted fidelity controls. The full final sweep below reruns the sweep
script after the citation repair; unchanged successful gate stamps may be reused.

Maintained layout commands, all exit 0:

```sh
LEAN_NUM_THREADS=2 lake build Conform
LEAN_NUM_THREADS=2 lake env lean -M4096 --run tools/Conform/Cli/LcnfMl.lean --out docs/research/2026-09-11-p2a-type-lane-evidence/commit1-layout --emit-ml docs/research/2026-09-11-p2a-type-lane-evidence/commit1-layout/ty_gen.ml --emit-expected docs/research/2026-09-11-p2a-type-lane-evidence/commit1-layout/expected.txt
opam exec --switch=effect4 -- ocamlopt -w -a docs/research/2026-09-11-p2a-type-lane-evidence/commit1-layout/ty_gen.ml -o docs/research/2026-09-11-p2a-type-lane-evidence/commit1-layout/ty_gen
docs/research/2026-09-11-p2a-type-lane-evidence/commit1-layout/ty_gen > docs/research/2026-09-11-p2a-type-lane-evidence/commit1-layout/actual.txt
cmp docs/research/2026-09-11-p2a-type-lane-evidence/commit1-layout/expected.txt docs/research/2026-09-11-p2a-type-lane-evidence/commit1-layout/actual.txt
LEAN_NUM_THREADS=2 lake env lean -M4096 --run tools/Conform/Effect4/OCamlJoin.lean docs/research/2026-09-11-p2a-type-lane-evidence/commit1-layout ocaml/eff/eff_types.ml ocaml/gen/api_gen.ml docs/research/2026-09-11-p2a-type-lane-evidence/commit1-layout/ty_gen.ml ocaml/eff/eff_typing.ml ocaml/eff/eff_wire.ml ocaml/eff/eff_json.ml
```


Final full sweep: `LEAN_NUM_THREADS=2 bash scripts/sweep.sh`, exit 0.

```text
sweep: every gate, one process at a time
generated-stale          DECLARED    1s  miss
library-roots            PASS   24s  miss
source-citations         PASS    1s  miss
internal-citations       PASS   92s  miss
effect-runtime-census    PASS    0s  hit
ts-eff                   PASS    1s  hit
conform                  PASS   21s  miss
generated                PASS    2s  miss
schema-typescript        PASS   42s  miss
schema-codec             PASS    2s  miss
ts-eff-corpus            PASS    1s  hit
ingest                   PASS    2s  hit
host-protocol            PASS   65s  miss
truth                    PASS    0s  hit
streams                  PASS    5s  miss
gen-check                PASS    3s  hit
dune-tests               PASS    3s  hit
engine-tests             PASS    3s  hit
sweep: 18 gates, 8 hit, 10 miss, 268s total; table in .lake/sweep-summary.tsv
PASS every gate under the declared-red policy; declared failures are listed above
```

Commit 1 is accepted under the unchanged declared-red policy. The full build,
axiom and module-closure gates, truth gate and maintained OCaml layout differential
all passed. The auxiliary compatibility-snapshot and generated-whitespace limits
above remain explicitly unclaimed. Commits 2 and 3 are not part of this acceptance.


## Commit 2 — canonical order and boundaries

Commit 1 landed as `5db3329`. This second candidate is based on that commit in the
same checkout and branch. No push, worktree, or branch change.

### Changes and proof graph

The public `Ty.sub_trans` exposes the structural proof needed for commit 1.
`Ty.sub_normalize_of_sub` proves the owner's one-way implication for every raw
pair: true subtyping remains true after normalizing both operands. No converse,
raw normalization equality, or product-distribution rule for `sub` is asserted.
`Ty.sub` and `Ty.sub_union_right` retain their exact previous declaration text.

The graph proceeds from structural union-member coverage to matching maximal
canonical members, then recursively to antisymmetry. Product factor coverage
establishes the normalized product step, and structural induction gives the
one-way normalization theorem. The helpers' explicit transitivity parameter is
supplied by the proved `Ty.sub_trans` at every public theorem.

`Ty.sub_antisymm_canonical`, `Ty.sub_join_left`, `Ty.sub_join_right` and
`Ty.join_least` quantify over `CTy`. Its public `≤` is subtype truth, and `<` is
strict subtyping. `Std.IsPartialOrder` and `Std.LawfulOrderSup` instances expose
these laws to Lean's built-in order interface; `CTy.never_le` supplies bottom.
The raw type's structural-key order still owns sorting inside normalization.

`CTy.key` is exactly `Ty.key ∘ CTy.toRaw`; its injection law is on `CTy`.
`Ty.key_injective` remains unchanged on raw `Ty`. The store's type kind is
reserved in this checkout: there was no raw `Content Ty` type-key client to
retarget. The public canonical type-key function is now explicit; raw structural
wire encodings and their generated retractions remain unchanged.

`Ty.render` normalizes once before its structural renderer; `CTy.render_toRaw`
states its canonical observation. The Chunk target helper uses that entry point.
`Ty.schema` normalizes at entry, and effect, object and operation-row documents
normalize their type columns. `CTy.ofSchema_schema` states the public retraction.
`Bridge.ofSchema`, `Bridge.ofSchema_schema` and `Bridge.ofSchema_schema_cty`
retain their exact previous declaration text, including integer parsing.

`Schema.encode`, `Schema.decode` and `Codec.isValue` normalize their type at entry.
Their general codec laws now quantify over `CTy`, as authorized. Structural wire
interpreters and the layout function are unchanged. The value-image adapter's
existing `ProgramImage.decode_of_encode` statement is retained, deriving its
result from the canonical codec theorem at `CTy.ofRaw t` and `normalize_idem`.

The `.ty` producer (`src/OCaml5/Tools/EffGen.lean`) and its handwritten OCaml
`print_type` counterpart now print canonical answer/error columns. This changes
the reporting boundary only; answer joining and type inference are untouched.

### Tests and exact proof output

The 37-type battery and planted commit-1 controls still pass. Added controls check
that the public subtype order differs from raw key sorting, canonical key equality
for absorbed literals, normalized printing, schema absorption/distribution, and
codec normalization at each entry point. The schema test's reversed raw union now
expects canonical member order. An intentional codec test delta is recorded:
`union (causeOf never) (list bool)` now normalizes to the list-first spelling,
so an empty cause is refused under both raw orders; the decoder chooses the empty
list and exact admission forbids confusing the two values. This follows directly
from the requested canonical entry boundary.

The first focused schema build found that intended guard delta, the explicit CTy
arguments now required by the codec law, and a mistaken namespace in a new test.
All were repaired; `commit2-schema-tests-final2.log` is the successful rerun.
Failed elaboration outputs, including compiler-generated placeholders, are retained
as failed probes and are not proof evidence.

`LEAN_NUM_THREADS=2 lake build` passed (311 jobs), including 278 modules and
44,080 declarations under the unchanged axiom boundary. The independent fresh
proof-print commands and output follow:

```sh
LEAN_NUM_THREADS=2 lake env lean -M4096 Test/Program/TypeAlgebraAxiomReport.lean
LEAN_NUM_THREADS=2 lake env lean -M4096 src/Effect4/Laws/Schema/Codec.lean
LEAN_NUM_THREADS=2 lake env lean -M4096 docs/research/2026-09-11-p2a-type-lane-evidence/Commit2HelperAxioms.lean
```

The new public order/key/printing names (the type report also repeats the entire
commit-1 regression printout):

```text
'Effect4.Program.Ty.sub_trans' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.sub_normalize_of_sub' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.sub_antisymm_canonical' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.sub_join_left' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.sub_join_right' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.join_least' depends on axioms: [propext, Quot.sound]
'Effect4.Program.CTy.key' depends on axioms: [propext, Quot.sound]
'Effect4.Program.CTy.key_injective' depends on axioms: [propext, Quot.sound]
'Effect4.Program.CTy.render_toRaw' depends on axioms: [propext, Quot.sound]
'Effect4.Program.CTy.instIsPartialOrder' depends on axioms: [propext, Quot.sound]
'Effect4.Program.CTy.instLawfulOrderLT' depends on axioms: [propext, Quot.sound]
'Effect4.Program.CTy.instLawfulOrderSup' depends on axioms: [propext, Quot.sound]
'Effect4.Program.CTy.never_le' depends on axioms: [propext, Quot.sound]
```

Canonical codec laws and helpers:

```text
'Effect4.Schema.Codec.nat?' depends on axioms: [propext]
'Effect4.Schema.Codec.encodeRaw' depends on axioms: [propext]
'Effect4.Schema.Codec.decodeRaw' depends on axioms: [propext]
'Effect4.Schema.Codec.isValue' depends on axioms: [propext, Quot.sound]
'Effect4.Schema.encode' depends on axioms: [propext, Quot.sound]
'Effect4.Schema.decode' depends on axioms: [propext, Quot.sound]
'Effect4.Schema.encode_eq_some' depends on axioms: [propext, Quot.sound]
'Effect4.Schema.encode_isSome_iff' depends on axioms: [propext, Quot.sound]
'Effect4.Schema.encode_of_hasTy' depends on axioms: [propext, Quot.sound]
'Effect4.Schema.decode_of_encode' depends on axioms: [propext, Quot.sound]
'Effect4.Schema.decode_encode' depends on axioms: [propext, Quot.sound]
'Effect4.Schema.hasTy_decode' depends on axioms: [propext, Quot.sound]
'Effect4.Schema.encode_sub' depends on axioms: [propext, Quot.sound]
'Effect4.Schema.encode_injective' depends on axioms: [propext, Quot.sound]
'Effect4.Schema.encode_string' depends on axioms: [propext, Quot.sound]
'Effect4.Schema.encode_bool' depends on axioms: [propext, Quot.sound]
'Effect4.Schema.encode_unit' depends on axioms: [propext, Quot.sound]
```

Order proof helpers, public schema retraction and retained image adapter:

```text
'Effect4.Program.Ty.OrderProof.sub_never' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.OrderProof.member_sub_self' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.OrderProof.sub_member_right_iff' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.OrderProof.sub_iff_members' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.OrderProof.normal_members' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.OrderProof.normal_children' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.OrderProof.sizeOf_member_le' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.OrderProof.sizeOf_member_lt' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.OrderProof.sub_antisymm_normal' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.OrderProof.sub_antisymm_canonical' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.OrderProof.members_join' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.OrderProof.normalizeRow_coverage' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.OrderProof.sub_join_left' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.OrderProof.sub_join_right' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.OrderProof.join_least' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.OrderProof.sub_join_iff' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.OrderProof.members_normalize_union' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.OrderProof.sub_normalize_union_left' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.OrderProof.sub_normalize_union_right' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.OrderProof.sub_normalize_union_le' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.OrderProof.members_subset_factors' depends on axioms: [propext]
'Effect4.Program.Ty.OrderProof.normal_factors_nonempty' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.OrderProof.factors_coverage' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.OrderProof.sub_prod_mono' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.OrderProof.productMembers_isMember' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.OrderProof.members_normalize_prod' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.OrderProof.sub_normalize_prod_mono' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Ty.OrderProof.sub_normalize_of_sub' depends on axioms: [propext, Quot.sound]
'Effect4.Program.CTy.ofSchema_schema' depends on axioms: [propext, Quot.sound]
'Effect4.Schema.ProgramImage.decode_of_encode' depends on axioms: [propext, Quot.sound]
```

### Generated outputs and final gates

Generation and the required gates completed as recorded below. No gate policy
or truth tape was edited by hand.


Regeneration is complete. The same 343 generated paths enumerated in commit 1
changed in this commit, all provenance-only. **No `.ty` golden body, printed type
body, truth corpus body, tape body, or generated OCaml body moved.** The new printed
boundary behavior is exercised by the authored batteries rather than by inventing
new golden contents. No generated file or truth tape was edited by hand.

Producer commands, all exit 0 (logs prefixed `commit2-` in the local evidence directory):

```sh
LEAN_NUM_THREADS=2 lake build Tools.ProgramStructure Conform OCaml5.Tools.EffGen
LEAN_NUM_THREADS=2 bash scripts/generate.sh
LEAN_NUM_THREADS=2 bash scripts/generate.sh --only lcnf
python3 scripts/generate-engine-structure.py
LEAN_NUM_THREADS=2 bash scripts/generate-host-protocol.sh
LEAN_NUM_THREADS=2 lake env lean -M4096 --run harness/truth/Truth.lean harness/truth/corpus.json --tapes harness/truth/tapes
bun run harness/truth/run-truth.ts --manifest harness/truth/corpus.json --out harness/truth --timeout 300 --tape-out harness/truth/tapes
```

The full `lake build` passed again after regeneration (311 jobs). The independent
fresh `bash scripts/check-library-roots.sh` passed with 278 modules and 44,080
declarations; the existing 7-module/36-name implementation exception remains
unchanged. `git diff --check` is green for this commit's changes. The historical
compatibility-snapshot parser limitation described under commit 1 remains; no
new compatibility-snapshot pass is claimed.

The maintained OCaml layout commands are the commit-1 commands above with
`commit2-layout` as their output directory. The directory was created before the
successful run; an initial missing-directory attempt exited 1 and is retained in
`commit2-layout-emission.log`. The successful fresh output is:

```text
wrote docs/research/2026-09-11-p2a-type-lane-evidence/commit2-layout/ty_gen.ml
wrote docs/research/2026-09-11-p2a-type-lane-evidence/commit2-layout/expected.txt
translated declarations: 33, read: 33, reader refusals: 0
cases: 20387
pass 20387  refused 0  counterexample 0  unresolved 0
wrote docs/research/2026-09-11-p2a-type-lane-evidence/commit2-layout/target.json
PASS OCaml executable differential: 1330 vectors, byte-for-byte match
conform.layout.ocaml-type-decl: 4/4 subjects, 4 pass, 0 refused, 0 counterexample, 0 unresolved, exit 0
conform.layout.audit[ocaml-eff recovered]: 138/138 subjects, 138 pass, 0 refused, 0 counterexample, 0 unresolved, exit 0
```

The added translated declaration (33 instead of commit 1's 32) is the separate
structural renderer needed by the normalized public entry. `ocamlopt` compiled the
fresh generated module, its executable ran, and `cmp` returned 0 against the fresh
expected observations. The OCaml generator check also passed. The fresh truth
recording reports: `PASS: 31 programs, exits and schedules agree with rc.112`.
The final full sweep and standalone truth check are recorded below.


Standalone `bash scripts/check-truth.sh`: PASS, 31 programs, bounded exits and
schedules agree with rc.112, regenerated modules type-check. OCaml unit tests:
PASS, including 864 normalization/algebra/admission controls. Engine checks:
PASS under their existing policy.

For clarity about that last verdict, both commit 1 and commit 2's engine logs
also print two **non-gated** exploratory comparisons: `pAcquire` reports a missing
service in the engine, and `pProvide` reports six engine fibers against one in the
recorded Lean run. The two diagnostics are byte-identical across these runs;
9/11 exploratory truth comparisons agree. They are not a full engine-equivalence
pass, and this lane does not repair them or change their status. The required
31-program rc.112 truth gate and the maintained OCaml type/layout differential
are separate comparisons and passed as recorded above.


Final full sweep: `LEAN_NUM_THREADS=2 bash scripts/sweep.sh --keep-going`, exit 0.

```text
sweep: every gate, one process at a time
generated-stale          DECLARED    1s  miss
library-roots            PASS   25s  miss
source-citations         PASS    1s  miss
internal-citations       PASS   93s  miss
effect-runtime-census    PASS   10s  miss
ts-eff                   PASS   37s  miss
conform                  PASS   22s  miss
generated                PASS    2s  miss
schema-typescript        PASS   49s  miss
schema-codec             PASS    2s  miss
ts-eff-corpus            PASS   12s  miss
ingest                   PASS  406s  miss
host-protocol            PASS   68s  miss
truth                    PASS    0s  hit
streams                  PASS    5s  miss
gen-check                PASS    4s  hit
dune-tests               PASS    3s  hit
engine-tests             PASS    3s  hit
sweep: 18 gates, 4 hit, 14 miss, 743s total; table in .lake/sweep-summary.tsv
PASS every gate under the declared-red policy; declared failures are listed above
```

Commit 2 is accepted under the unchanged declared-red policy. The full build,
fresh axiom/module-closure audit, 31-program truth gate and maintained OCaml
layout differential passed. Its `git diff --check` is green. Commit 3 remains
separate and is not included in this acceptance.


## Commit 3 — integer admission and the error carrier

Base: `73ae302` (commit 2). This section records the final slice separately from
normalization (`5db3329`) and the canonical order (`73ae302`). All required gates passed
under the unchanged declared-red policy, as recorded below. No push.

### Changes and proof graph

`rawSupportedErrTy` is exactly the old structural predicate with its recursive
name changed. Public `supportedErrTy t` reads `rawSupportedErrTy t.normalize`.
`admittedErrTy_eq_raw` proves by `rfl` that failure introduction still computes
the same predicate as before this commit. `supportedErrTy_normalize` follows
from `Ty.normalize_idem`. `supportedErrTy_join` uses member coverage through the
normalized antichain and the unchanged structural profile.

`ErrTy` carries a canonical type and its supported-error proof. Its decidable
order and join are defined in the core. The Laws graph supplies
`Std.IsPartialOrder`, `Std.LawfulOrderSup`, the bottom law `never_le`, and the
commutative, associative, idempotent and bottom-unit join laws. These are the
built-in order classes; no Mathlib or new framework is introduced.

The error-value recovery proofs factor through private raw-profile lemmas and
`hasTy_normalize`. The statements of all 31 existing public declarations in
`Laws/Program/Admit.lean` remain unchanged, including allocation independence,
exact error recovery, exclusion of `boom`, and admitted error conversion.

`Api.findInt` traverses raw types and records their constructor path.
`findIntInTable` checks every supplied request, answer and error, including unused
rows, before inference or normalization. `findIntInEffTy` checks the inferred
answer and error columns. `admitProgram_table_int` and `admitProgram_type_int`
prove the corresponding path-bearing refusals. Successful `AdmittedProgram`
certificates retain the two negative scan results as proof fields, so constructing
a certificate directly cannot bypass the checks. The new refusal constructor is
appended after the existing three constructors.

Dependency path: unchanged raw type syntax → structural integer scan → admission
refusal/certificate; canonical normalization → raw supported members → error
support and join closure → `ErrTy` → public order/join laws. The existing error
recovery path additionally uses `hasTy_normalize`. All production dependencies
remain in the API-to-Laws direction; no Laws import enters the API graph.

### Controls and preserved surfaces

The exact 37-type battery remains in `Test/Program/TypeAlgebraContract.lean`.
It still requires zero mutual-subtype inequalities and zero non-absorptions.
New controls exercise the error carrier's least-upper-bound/bottom laws, the
normalized support boundary and the exact unchanged admission computation.
The historical raw `hiddenPair` negative now names `rawSupportedErrTy`; the
public predicate and admission both accept its canonical supported type.

`Test/Api/ApiContract.lean` checks all 13 nested constructor positions, a second
row index, an unused integer row, nested request and error paths, and an ordinary
natural-number program that still admits. The foreign integer schema parses to
`some .int`; a program using it refuses with `["table", "0", "answer"]`.
The same path is checked for a program inferred at `int`. `Ty.key .int = [3]`
remains a guard. A handle whose opaque name is `"int"` is not the integer type.

Source comparison against the original lane base confirms byte-identical
`Ty.sub`, `sub_union_right`, `Ty.key`, raw `key_injective`, the `Ty` constructor
block, `Bridge.ofSchema` and both existing schema retractions. The entire value,
typing and membership source files are unchanged, as are both protected roots,
the axiom gate and `lakefile.toml`. Inspection of the unchanged program syntax
found no embedded type annotations outside the checked table and inferred
columns. No change to answer joining, `catchIf`, `termTy`, literal synthesis,
wire layouts, existing ordinals or `Val`. `supportedErrTy_diffTag` remains P3.

The first focused integration build failed only because two new `ErrTy` examples
used `decide` on well-founded reduction. Replacing it with kernel-checked `cbv`
resolved that proof elaboration issue; no proposition or gate was weakened.
The failed output remains in `commit3-focused-build.log` in the local evidence
directory.

### Fresh theorem and axiom receipts

The production build passed (311 jobs), including the audit of 278 modules and
44,201 declarations, with the unchanged seven-module/36-name implementation
exception. The independent tools build passed (188 jobs). Fresh `lake env lean`
runs of `Test/Program/TypeAlgebraAxiomReport.lean`,
`Test/Api/ApiContract.lean`, and the error-recovery receipt all passed. Their
exact new/changed declaration outputs follow; all are within the required
semantic/test ceiling. The two private raw helpers were printed by exact
environment name in the local tooling receipt. Initial scratch attempts to
spell a numeric private name and invoke the command in a term context failed;
the corrected receipt passed, and none of that tooling enters production.

```text
'Effect4.Program.ErrTy.instIsPartialOrder' depends on axioms: [propext, Quot.sound]
'Effect4.Program.ErrTy.instLawfulOrderSup' depends on axioms: [propext, Quot.sound]
'Effect4.Program.ErrTy.never_le' depends on axioms: [propext, Quot.sound]
'Effect4.Program.ErrTy.le_join_left' depends on axioms: [propext, Quot.sound]
'Effect4.Program.ErrTy.le_join_right' depends on axioms: [propext, Quot.sound]
'Effect4.Program.ErrTy.join_least' depends on axioms: [propext, Quot.sound]
'Effect4.Program.ErrTy.join_comm' depends on axioms: [propext, Quot.sound]
'Effect4.Program.ErrTy.join_assoc' depends on axioms: [propext, Quot.sound]
'Effect4.Program.ErrTy.join_self' depends on axioms: [propext, Quot.sound]
'Effect4.Program.ErrTy.join_never' depends on axioms: [propext, Quot.sound]
'Effect4.Program.ErrTy.join_never_right' depends on axioms: [propext, Quot.sound]
'Effect4.Program.rawSupportedErrTy' depends on axioms: [propext]
'Effect4.Program.rawSupportedErrTy_iff_members' depends on axioms: [propext, Quot.sound]
'Effect4.Program.rawSupportedErrTy_ofMembers' depends on axioms: [propext]
'Effect4.Program.supportedErrTy' depends on axioms: [propext, Quot.sound]
'Effect4.Program.supportedErrTy_normalize' depends on axioms: [propext, Quot.sound]
'Effect4.Program.supportedErrTy_never' depends on axioms: [propext, Quot.sound]
'Effect4.Program.supportedErrTy_join' depends on axioms: [propext, Quot.sound]
'Effect4.Program.admittedErrTy_eq' depends on axioms: [propext, Quot.sound]
'Effect4.Program.admittedErrTy_eq_raw' depends on axioms: [propext, Quot.sound]
'Effect4.Program.ErrTy.canonical' depends on axioms: [propext, Quot.sound]
'Effect4.Program.ErrTy.supported' depends on axioms: [propext, Quot.sound]
'Effect4.Program.ErrTy.admitted' depends on axioms: [propext, Quot.sound]
'Effect4.Program.ErrTy.never' depends on axioms: [propext, Quot.sound]
'Effect4.Program.ErrTy.join' depends on axioms: [propext, Quot.sound]
'Effect4.Program.ErrTy.toRaw_never' depends on axioms: [propext, Quot.sound]
'Effect4.Program.ErrTy.toRaw_join' depends on axioms: [propext, Quot.sound]
'Effect4.Program.ErrTy.ext' depends on axioms: [propext, Quot.sound]
'Effect4.Api.findInt' does not depend on any axioms
'Effect4.Api.findIntInTable' does not depend on any axioms
'Effect4.Api.findIntInEffTy' does not depend on any axioms
'Effect4.Api.admitProgram' depends on axioms: [propext, Quot.sound]
'Effect4.Api.admitProgram_table_int' depends on axioms: [propext, Quot.sound]
'Effect4.Api.admitProgram_type_int' depends on axioms: [propext, Quot.sound]
'Effect4.Program.hasTy_supported_allocation' depends on axioms: [propext, Quot.sound]
'Effect4.Program.valOfErr_errOf_supported' depends on axioms: [propext, Quot.sound]
'Effect4.Program.errOf_ne_boom_of_supported' depends on axioms: [propext, Quot.sound]
'Effect4.Program.errAdmits_errOf' depends on axioms: [propext, Quot.sound]
'_private.Effect4.Laws.Program.Admit.0.Effect4.Program.hasTy_rawSupported_allocation' depends on axioms: [propext]
'_private.Effect4.Laws.Program.Admit.0.Effect4.Program.valOfErr_errOf_rawSupported' depends on axioms: [propext,
 Quot.sound]
'Effect4.Program.ErrTy.instLE' depends on axioms: [propext, Quot.sound]
'Effect4.Program.ErrTy.instDecidableLE' depends on axioms: [propext, Quot.sound]
'Effect4.Program.ErrTy.instMax' depends on axioms: [propext, Quot.sound]
```

### Generated outputs and final gates

The completed producer and final-gate ledger follows below. The maintained
OCaml type/layout comparison passed with fresh commit-3 output:

```text
wrote docs/research/2026-09-11-p2a-type-lane-evidence/commit3-layout/ty_gen.ml
wrote docs/research/2026-09-11-p2a-type-lane-evidence/commit3-layout/expected.txt
translated declarations: 33, read: 33, reader refusals: 0
cases: 20387
pass 20387  refused 0  counterexample 0  unresolved 0
wrote docs/research/2026-09-11-p2a-type-lane-evidence/commit3-layout/target.json
PASS ocamlopt compilation and executable run; cmp exit 0
PASS OCaml executable differential: 1330 vectors, six observations each, byte-for-byte match
conform.layout.ocaml-type-decl: 4/4 subjects, 4 pass, 0 refused, 0 counterexample, 0 unresolved, exit 0
conform.layout.audit[ocaml-eff recovered]: 138/138 subjects, 138 pass, 0 refused, 0 counterexample, 0 unresolved, exit 0
```

These are the same commands recorded for commit 2 with `commit3-layout` as the
output directory, created before emission. `ocamlopt` compiled the new output,
the executable ran, and `cmp` returned 0. This is a finite type/layout comparison,
not a general engine equivalence claim.


Regeneration finished using the existing producers only. The exact 343 changed
generated paths match the list under commit 1 and the commit-2 set; all 343
changes are provenance-only. **No `.ty` golden body, printed type body, generated
OCaml body, truth corpus body or tape body moved.** The per-path classification
is retained in `commit3-generated-changes.json` in the local evidence directory.

All producer commands below returned exit 0:

```sh
LEAN_NUM_THREADS=2 bash scripts/generate.sh
LEAN_NUM_THREADS=2 bash scripts/generate.sh --only lcnf
python3 scripts/generate-engine-structure.py
LEAN_NUM_THREADS=2 bash scripts/generate-host-protocol.sh
LEAN_NUM_THREADS=2 lake env lean -M4096 --run harness/truth/Truth.lean harness/truth/corpus.json --tapes harness/truth/tapes
bun run harness/truth/run-truth.ts --manifest harness/truth/corpus.json --out harness/truth --timeout 300 --tape-out harness/truth/tapes
```

Independent Lean processes used two threads; `generate.sh` retains its existing
three-thread setting. No compilation-policy file was changed. Builds that
shared fresh outputs were coordinated; independent proof, layout and host
checks were allowed to run in parallel under the owner's instruction.

Both builds after the Lean regeneration passed (311 jobs). The final fresh
`bash scripts/check-library-roots.sh` output is:

```text
Effect4 library-root gate: 92 API/utility modules, 53 Laws-only modules; every library source is reachable; Effect4 never reaches Laws
Effect4 module and axiom gate: checked 278 modules and 44201 declarations; semantic/test axioms are [propext,
 Quot.sound]; exact implementation boundary (7 module(s), 36 declaration(s)) additionally allows Classical.choice
PASS library-roots: fresh module, root-closure and axiom audit
```

The host producer freshly reported `PASS: 31 programs, exits and schedules
agree with rc.112`. Standalone OCaml `gen-check`, `dune-tests` and `engine-tests`
all returned exit 0. The unit-test output includes `test_eff: 760 checks, 0
failures`. Dune retains its normal dependency cache; this receipt does not
claim every unchanged internal test was rerun. The existing exploratory engine
comparison limitations and compatibility-snapshot limitation recorded under
commits 1 and 2 remain; no broader engine-equivalence or compatibility-snapshot
pass is claimed here. Integer-free admission is the concrete obligation in
this slice; no general inhabitation theorem is asserted.

Standalone `LEAN_NUM_THREADS=2 bash scripts/check-truth.sh` returned exit 0:

```text
PASS: 31 programs, exits and schedules agree with rc.112
PASS truth: pinned corpus and bounded exit/schedule differential agree; the regenerated modules type-check
```

The complete sweep result follows below.


Final `LEAN_NUM_THREADS=2 bash scripts/sweep.sh --keep-going`, exit 0:

```text
sweep: every gate, one process at a time
generated-stale          DECLARED    1s  miss
library-roots            PASS   24s  miss
source-citations         PASS    1s  miss
internal-citations       PASS   93s  miss
effect-runtime-census    PASS    9s  miss
ts-eff                   PASS   36s  miss
conform                  PASS   21s  miss
generated                PASS    1s  miss
schema-typescript        PASS   48s  miss
schema-codec             PASS    2s  miss
ts-eff-corpus            PASS   12s  miss
ingest                   PASS  390s  miss
host-protocol            PASS   69s  miss
truth                    PASS    0s  hit
streams                  PASS    5s  miss
gen-check                PASS    3s  hit
dune-tests               PASS    2s  hit
engine-tests             PASS    3s  hit
sweep: 18 gates, 4 hit, 14 miss, 720s total; table in .lake/sweep-summary.tsv
PASS every gate under the declared-red policy; declared failures are listed above
```

The declared result is unchanged and explicit:

```text
PASS generated-stale: 613 stamps checked in 0.621s; red as declared: the two flat LCNF outputs `ocaml/gen/fibers_gen.ml` and `machine_gen.ml` were cut before e2285a9; regenerating them at HEAD builds, but the hand-written `ocaml/gen/gen_check.ml` still tests the pre-timer machine shape (no Task_wake, no wake_list/clock_step/prepare_answer) and fails C2. Cleared when gen_check.ml is brought to the timer and external rows (DI-19's Phase 1)
LCNF: ocaml/gen/fibers_gen.ml, ocaml/gen/machine_gen.ml
the two flat LCNF outputs `ocaml/gen/fibers_gen.ml` and `machine_gen.ml` were cut before e2285a9; regenerating them at HEAD builds, but the hand-written `ocaml/gen/gen_check.ml` still tests the pre-timer machine shape (no Task_wake, no wake_list/clock_step/prepare_answer) and fails C2. Cleared when gen_check.ml is brought to the timer and external rows (DI-19's Phase 1)
Deferred by owner: generated/schema-structural-assurance.tsv
```

Commit 3 is accepted under the unchanged declared-red policy. The full build,
fresh axiom/module-closure audit, 31-program truth gate and maintained OCaml
layout differential passed. `git diff --check` is green. The final scope review
contains exactly 353 paths: nine authored source/test files, this receipt, and
343 producer-owned outputs. No gate script, declared-red policy or protected
root changed anywhere in the lane. The amended P2a obligations are complete;
the withdrawn statements and retained limits are recorded above. No push.
