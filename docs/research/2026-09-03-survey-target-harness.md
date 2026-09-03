# Survey: TypeScript target, harness, scripting, docs

Repo: `/Users/pooks/Dev/lean4-effect4` at `645067a` (main). Working tree at survey
time had 55 modified goldens (provenance rows only) — that dirt is itself finding 2.
Siblings read: `~/Dev/effect4-tools` (`3ff57b6`), `~/Dev/lean4-typescript` (`31665ff`,
tag v0.4.2, clean), `~/Dev/downstream` (`89ab4f9`).
Sweep timings quoted from
`/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/e9e3b20e-.../scratchpad/sweep/summary*.tsv`.

Nothing in this survey was edited. Every finding below was checked against the file.

---

## Ranked findings

### 1. Every golden run copies a 52 MB directory; ~5 minutes per host gate
**Category:** build

**Evidence.** `~/Dev/effect4-tools/packages/harness/trace.mjs:80`:
```js
cpSync(target, temporary, { recursive: true })
if (!existsSync(join(temporary, "node_modules"))) symlinkSync(nodeModules, join(temporary, "node_modules"), "dir")
```
`target` is `harness/trace`. Measured: `du -sh harness/trace` = **52M**, of which
`harness/trace/patched/_copy` = **51M** (a gitignored patched rc.112 tree written by
`harness/trace/patched/apply.mjs`; `harness/trace/patched/.gitignore` = `_copy/`).
A single `cp -R` of that tree measured **2.4 s** on this machine.

`scripts/check-trace-host.sh` invokes `trace.mjs` once per golden per yield setting:
5×2 straight-line + 12×3 flow/structured + 3×2 interrupt + 4×2 scope + 8×2 layer +
9×1 fiber + 6×2 job + 6×2 deferred + 7×2 ref = **123 node runs**. 123 × 2.4 s ≈ **5 min**
of pure directory copying, before Lean or node does any work.
`scripts/check-trace-patched.sh:24` adds 12 more; `scripts/test-trace-goldens-gate.sh`
adds 9. This matches the observed spread of `check-trace-host` (58 s … 374 s across
summary3/6/8) — the fast runs predate `_copy` existing.

**Why it matters.** The dominant cost of the two slowest sweep steps is copying a tree
the run does not read. It also means the tree's size silently gates the harness.

**Proposed change.** Give `cpSync` a `filter` that skips `patched/_copy`, `receipts/`
and `types/` (or move `_copy` to `.lake/effect4-patched/` and point
`apply.mjs --print` there). Better still: symlink the harness dir and copy only the
`.ts` files the tail imports.

**Effort:** S. **Risk:** low — a filter is local to `trace.mjs`; verify the patched
gate still finds its copy via `EFFECT4_EFFECT_NODE_MODULES`.

---

### 2. `check-trace-goldens.sh` is red at the tip of main: all 55 goldens carry stale provenance
**Category:** correctness

**Evidence.** Committed `generated/traces/incr.empty.tsv` at HEAD:
```
input	harness/trace/Generate.lean	sha256=dc6bd35cf0e6d3d534879cabee01b4c445267248a1222d9a41034e8c16a7f4f6
input	Effect4/Meta/Derive.lean	sha256=ecf64caa636a200917402b4eb5426d6d8c72e477ecd58b9403b65801d92e2275
pin	effects	2447edd76649f035e989914ac899831d66e7dad2
```
Actual at HEAD: `Generate.lean` = `265079340d0f…`, `Derive.lean` = `e859f89550bf…`,
`lake-manifest.json` effects rev = `a117157`. `git diff` over the working tree is
exactly 165 changed lines = 55 files × 3 provenance rows, no data rows.

`scripts/check-trace-goldens.sh:16-24` regenerates and `cmp`s byte for byte, so it fails
on 55 files at `645067a`. Nothing caught it: no CI step runs it (finding 5), and the
last two commits (`f13afac`, `645067a`) touched `Generate.lean` and `Derive.lean`
without regenerating.

**Why it matters.** The trace lane's own hermetic drift gate is red on the branch the
next agent will build from, and the failure is pure provenance noise, which trains
readers to ignore it.

**Proposed change.** Two parts. (a) Regenerate and commit. (b) Stop hashing inputs whose
edits cannot change a golden's rows: `Derive.lean` and `Generate.lean` change on every
DSL or program edit, so their digests dirty all 55 files for reasons unrelated to any
one golden. Either move the provenance block to a single `generated/traces/PROVENANCE.tsv`
that all goldens reference, or hash only the emitted rows.

**Effort:** S for (a), M for (b). **Risk:** (b) changes the golden format — coordinate
with `trace.mjs` `parseGolden` and `test-trace-goldens-gate.sh` mutant 3, which greps
`^pin\teffects\t`.

---

### 3. `generated/lowering-property.tsv` is stale in three of four inputs and its pin; 12 rules claim `covered` on it
**Category:** correctness

**Evidence.** `generated/lowering-property.tsv`:
```
input	harness/trace/property-tail.ts	sha256=cc900e11edfeb…      actual c057251a8214…
input	harness/trace/tracer.ts	        sha256=9f54ff61e4fe…      actual 4c3cb1ea339b…
input	Effect4/Target/TypeScript/FlowLower.lean sha256=fc517fbb3018…  actual 1aff0e083399…
pin	effects	c28833b3c14431ba2886a0fb66bcc688c86c2589                actual a117157
```
(`Property.lean` and the generator script still match.) The pin is a *third* distinct
effects revision — neither the goldens' `2447edd…` nor the manifest's `a117157`.

The join in `scripts/generate-lowering-coverage.sh` only checks existence:
```python
if prop == "1" and not os.path.exists("generated/lowering-property.tsv"): fail(...)
```
and `Effect4Test/Target/TypeScript/LoweringCoverage.lean:47` derives
`covered` from `row.property` alone. `generated/lowering-coverage.tsv` reports
`count covered 12`. So 12 of 29 rules sit at the ledger's top host state on a batch run
against a different tracer, a different property tail, a different `FlowLower.lean`, and
two effects pins ago — and `check-lowering-coverage.sh` passes (0 in every sweep summary).

There is no drift gate for this file at all: `scripts/generate-lowering-property.sh`
writes it, `scripts/check-lowering-property.sh` re-runs the corpus and prints a row, but
nothing `cmp`s the committed file against a fresh one.

**Why it matters.** This is the repository's only claim that the lowering is right on
*generated* programs rather than a hand-picked corpus, and it is the loudest word in the
ledger (`covered`).

**Proposed change.** Add `scripts/check-lowering-property-drift.sh` on the pattern of
`check-trace-goldens.sh`, and make the coverage join verify the recorded input digests
and pin against the current tree before honouring `property = 1`.

**Effort:** M. **Risk:** low; expect it to be red on first run, which is the point.

---

### 4. Seven harness roots are never typechecked — the whole Flow v3 job lane included
**Category:** correctness

**Evidence.** `harness/trace/tsconfig.json` `files` lists 17 entries. The directory holds
25 `.ts` files. `~/Dev/effect4-tools/packages/harness/check.mjs:39` runs
`tsc -p tsconfig.json`, so only `files` and their transitive imports are checked.
Import graph (measured):

| root | imported by a listed file? | checked |
| --- | --- | --- |
| `job-tail.ts` → `job-fixture.ts` | no | **no** |
| `layer-tail.ts` → `layer-fixture.ts` | no | **no** |
| `interrupt-tail.ts` | no | **no** |
| `property-tail.ts` | no | **no** |
| `property-structured-tail.ts` | no | **no** |
| `job-queue.ts` | yes, via `atoms.ts` | yes |

Commit `2b65e35` ("harness: type-check with the pinned node types (job-queue.ts imports
node:fs)") added `"types": ["node"]` — needed only because `atoms.ts` type-imports
`job-queue.ts`. The author plainly believed the job files were covered; they are not.

Consequences visible today: `harness/trace/types/` contains receipts only for
`{fallible,incr,probe,recover,twice}.empty` and `flow/*` — no `job/`, `layer/`,
`deferred/`, `ref/`, `scope/`, `fiber/`. `scripts/check-lowering-types.sh:17` compiles
the same `tsconfig.json`, so `job-fixture.d.ts` is never emitted and `perform-catch`,
`branch-if`, `perform-tuple` have `typeReceipt = 0` in the ledger. The `perform-catch`
lowering emits `Result.isSuccess(a4)` then `a4.success` / `a4.failure`
(`Effect4/Target/TypeScript/Skeleton.lean:413`, `Slot.name` lines 107-108) — narrowing
that *only* a typechecker can validate, and no typechecker sees it.

**Why it matters.** The newest and least-proved lowering rules are exactly the ones with
no type evidence, and the gap is invisible because the gate reports PASS.

**Proposed change.** Replace the hand-maintained `files` array with `include: ["*.ts"]`
(or add the 7 roots), then add a one-line check in `check-trace-host.sh` that every
`harness/trace/*.ts` appears in the tsgo `--list-files` output, so the next new tail
cannot be forgotten.

**Effort:** S to add the files; M to fix whatever errors surface. **Risk:** medium —
expect real diagnostics in the unchecked files.

---

### 5. No trace, lowering or coverage gate runs in CI
**Category:** correctness / build

**Evidence.** `.github/workflows/lean_action_ci.yml` runs exactly five steps:
`test-vendor-foldlab.sh`, `lake build Effect4`, `test-trust-gate.sh`,
`test-schema-structural-assurance-gate.sh`, `check-effect-runtime-census.sh`.
`check-trace-goldens.sh` needs no host at all (its header says "Hermetic drift gate …
Needs no host") and is not there. Neither is `check-lowering-coverage.sh`,
`test-trace-goldens-gate.sh`, `test-lowering-coverage-gate.sh`, nor `lake build
Effect4Test`.

**Why it matters.** Findings 2 and 3 are both "the drift gate is red on main and nobody
noticed". A hermetic gate that runs nowhere but a hand-driven local sweep will rot again.

**Proposed change.** Add the three host-free steps (`check-trace-goldens.sh`,
`check-lowering-coverage.sh`, `test-lowering-coverage-gate.sh`) to the workflow. Note
they are currently macOS-only (finding 36) — fix that first or gate on `macos-latest`.

**Effort:** S (after 36). **Risk:** low.

---

### 6. The coverage ledger's evidence columns are hand-declared booleans; green receipts on disk are reported as absent
**Category:** api

**Evidence.** `Effect4Test/Target/TypeScript/LoweringCoverage.lean:38-42` — `Row` carries
`host : Bool`, `property : Bool`, `typeReceipt : Bool` written by hand per rule.
`scripts/generate-lowering-coverage.sh` verifies a claim only when it is `1`:
`if host == "1": …check the receipt…`. Nothing looks at receipts a row does not claim.

`generated/lowering-coverage.tsv` therefore reports `perform-catch  pinned  …  0 0 0`,
while `harness/trace/receipts/job/jobRunner.retry.json` exists, is at the current pin
(`effectUpstreamCommit 2600f62f…`, `effectTreeSha256 aea8ac8a…` = `harness/trace/host-pin.json`),
lists `perform-catch` in its `rules` row, and reports `"results": {"outcome":"ok","m1":"ok","m2":"ok"}`.
The same holds for `branch-if`, `perform-tuple`, `interrupt-point` and `region-masked` —
all five `pinned` rules have green receipts under `receipts/job/` and
`receipts/flow/interrupt/`.

`docs/LOWERING-COVERAGE.md` says the gate fails on "a declared state above the derived
one". It cannot fail on a state *below* it, so under-claiming is permanent and silent.

**Why it matters.** The ledger is the repository's headline artefact for "what the
lowering actually has evidence for", and it is currently wrong in the conservative
direction for five rules — which reads as "Flow v3 is unverified on the host" when in
fact six job goldens pass at both yield settings.

**Proposed change.** Derive `host`, `property` and `typeReceipt` from disk: scan
`harness/trace/receipts/**` for receipts whose `rules` row names the rule and whose pin
matches, instead of trusting a Bool. Keep the Lean row for `state` and `proof` only, so
the gate still catches over-claims.

**Effort:** M. **Risk:** low; the state counts will move up, which needs a doc update
(finding 26).

---

### 7. Committed receipts declare a `foreign` atom list that is wrong for the job family
**Category:** correctness

**Evidence.** `harness/trace/job-tail.ts:241`:
```ts
foreign: ["succ@./atoms.ts", "dec@./atoms.ts", "snd@./atoms.ts"]
```
`harness/trace/job-fixture.ts:12` imports `{ succ, dec, snd, nonEmpty, positive }`; the
actual call sites are `succ` (2), `dec` (2), `nonEmpty` (lines 172, 437),
`positive` (lines 263, 528) — and `snd` is **never called**. So the six committed
receipts under `harness/trace/receipts/job/` name an atom the run does not use and omit
the two atoms whose values decide every branch in the job runner.

The field is hand-typed in each of 11 tails (`grep -n "foreign:" harness/trace/*.ts`)
and nothing compares it with the fixture's imports or `Atoms.rows`.
`harness/AGENTS.md` requires: "Runtime observations state their decision tape, scheduler
inputs, **foreign registrations**, and other ambient assumptions needed for replay."

**Why it matters.** It is a factual error in committed evidence, in the exact field the
harness's own routing document says exists for replay.

**Proposed change.** Emit `foreign` from the generated fixture — the Lean side already
knows the atom set (`Atoms.rows`, the `.named [...] "./atoms.ts"` import list in
`Generate.lean:1401`) — and export it as a `const` the tail re-exports. Separately, the
unused `snd` import in the *generated* `job-fixture.ts` means the atom-import emitter
over-imports; that is a second bug in the same place.

**Effort:** S. **Risk:** low.

---

### 8. The job scenario table is a hand-copied duplicate of Lean's, and the queue seed is in neither golden nor receipt
**Category:** correctness

**Evidence.** `harness/trace/job-tail.ts:178-205`:
```ts
/** The host copy of `jobEntries` in `harness/trace/Generate.lean`: which body
 * a golden runs, with which attempt budget, from which queue. */
const scenarios: Record<string, { body: string; input: number; seed: QueueState }> = {
  "jobRunner.retry": { body: "jobRunner", input: 2,
    seed: { pending: [1, 2], acked: [], requeued: [], failures: [[2, 1]] } }, …
```
Six scenarios, each duplicating a `jobEntries` row in `harness/trace/Generate.lean`
(driven by `run job-programs` in `scripts/generate-trace-goldens.sh`). Nothing compares
the two. The golden header (`Trace.golden`, `Effect4/Target/TypeScript/Trace.lean:113`)
carries `program`, `tape`, `rules`, `budget` — **not** the seed; the receipt written by
`trace.mjs:135` carries `program, tape, rules, host, patchedFrames, scheduler, foreign,
primitives, results` — also not the seed.

`job-tail.ts:227` even computes `released` (whether the queue directory was cleaned up)
and the comment says "Recorded, never compared" — but `trace.mjs` drops it: it is absent
from every `receipts/job/*.json`.

**Why it matters.** The seed is the run's whole initial state. A divergence introduced by
editing one face and not the other is only caught if it changes a compared row; and no
receipt can be replayed from what it records.

**Proposed change.** Emit the scenario table from `Generate.lean` into `job-fixture.ts`
as data (it already emits the flows), have `job-tail.ts` read it, and add `seed` to the
golden header so the receipt inherits it. Pass `released` through `trace.mjs` into the
receipt or delete it.

**Effort:** M. **Risk:** low; regenerates the six job goldens.

---

### 9. Rule identity is positional: four contract batteries pin `Rule.all` by index
**Category:** api

**Evidence.**
```
Effect4Test/Target/TypeScript/MultiArgContract.lean:194:  #guard (Rule.all.map Rule.id).drop 26 = ["perform-tuple", "perform-catch", "branch-if"]
Effect4Test/Target/TypeScript/FlowLowerContract.lean:28:  #guard ((Rule.all.map Rule.id).drop 8).take 8 = …
Effect4Test/Target/TypeScript/RegionLowerContract.lean:24: #guard ((Rule.all.map Rule.id).drop 17).take 3 = …
Effect4Test/Target/TypeScript/StructuredLowerContract.lean:26:#guard ((Rule.all.map Rule.id).drop 21).take 5 = …
```
plus `example : Rule.all.length = 29` in three of them. The consequence is written into
the source: `Effect4/Target/TypeScript/Lower.lean:101` —
```lean
   -- Flow v3 (lean4-effects v0.7.0): appended last so the positional windows of the
   -- lowering contracts keep their places.
   performCatch, branchIf ]
```
so `performTuple` sits between `dispatchFallback` and `performCatch` in `all` while the
inductive declares it last, and the enum order, the `all` order and the ledger order have
already diverged. `docs/LOWERING-COVERAGE.md:95` documents the workaround as if it were
a design ("which is why the positional pins in the contract batteries are windows rather
than tails").

**Why it matters.** Every future rule must be appended last regardless of where it
belongs, four batteries need edits for each addition, and two packets adding rules in
parallel conflict on the same indices. `Rule` already has `id : Rule → String` and
`ofId?` with `ofId?_id` proved — identity by id is available and unused.

**Proposed change.** Replace the windows with set/membership pins:
`#guard (Rule.all.map Rule.id).filter (· ∈ flowLowerIds) = flowLowerIds`, or simply
`#guard Rule.ofId? "perform-catch" = some .performCatch` plus one
`Rule.all.map Rule.id` equality in a single owning battery. Then order `all` to match
the inductive and let it be free.

**Effort:** S. **Risk:** low.

---

### 10. The effects pin is a 7-character abbreviation and propagates into every provenance block
**Category:** correctness / cleanup

**Evidence.** `lakefile.toml`:
```toml
[[require]]
name = "effects"
rev = "a117157"
```
Lake copies that verbatim: `lake-manifest.json` has `"rev": "a117157"` and
`"inputRev": "a117157"` for `effects`, while the `typescript` entry carries a full
40-character `rev` and `inputRev`. The resolved commit is
`a11715748b04f2369e5031e3350f30b99862a07f` (tag `v0.7.0` — checked in
`.lake/packages/effects`).

`scripts/generate-trace-goldens.sh:14` and `scripts/generate-lowering-coverage.sh` both
read `lake-manifest.json`'s `rev`, so `pin effects a117157` is now stamped into 55
goldens and the coverage ledger, replacing the previous full sha
`2447edd76649f035e989914ac899831d66e7dad2`. Three pin spellings now coexist in
`generated/` (finding 3).

Also stale: the lakefile comment says "the flow-v3 branch … **to be tagged** v0.7.0", but
the tag already exists on the resolved commit.

**Why it matters.** An abbreviated rev is not a durable identifier, and the provenance
format silently changed width mid-corpus, which is exactly the kind of thing a digest
block exists to prevent.

**Proposed change.** Put the full sha (or the tag) in `lakefile.toml`, re-resolve the
manifest, regenerate; and have both generators assert `len(rev) == 40` before printing.

**Effort:** S. **Risk:** low.

---

### 11. `generate-trace-goldens.sh` spawns one full Lean elaboration per golden
**Category:** build

**Evidence.** `scripts/generate-trace-goldens.sh:19`:
```bash
run() { lake env lean --run harness/trace/Generate.lean "$@" | grep -v '^warning: manifest out of date'; }
```
and then nine hand-written loops, each calling `run <family>-programs` once and `run
<family>-golden <name>` once **per golden**. With 61 projections that is ~70 separate
`lake env lean --run` processes, each re-elaborating the whole 1709-line `Generate.lean`
and everything it imports. Recorded cost: 86 s … 220 s (`generate-trace-goldens` row in
summary1/4/5/6/8/9).

`scripts/check-trace-goldens.sh:16` then calls the same script again into a temp dir, so
the sweep pays it **twice** back to back (`check-trace-goldens` 82 s … 233 s).
`scripts/check-trace-host.sh` adds 10 more `lake env lean --run` invocations
(one per fixture family), and `check-lowering-types.sh` two more.

**Why it matters.** Roughly half the sweep's wall time is Lean process startup and
re-elaboration of one module.

**Proposed change.** Give `Generate.lean` an `all <outdir>` command that writes every
projection in one process (it already knows every family list), and reduce the shell to
`run all "$out"` plus the provenance prologue. `check-trace-goldens.sh` can then run it
once into a temp dir and diff, halving the cost again.

**Effort:** M. **Risk:** low; the outputs are byte-comparable before and after.

---

### 12. `TapeValueMismatch` and `TapeSiteMismatch` are unexercised, and the claimed Lean parity is a divergence
**Category:** correctness

**Evidence.** `harness/trace/tracer.ts:309-312`:
```ts
/** The tape's answer at a value branch disagrees with the value the program
 * computed: the Lean runner refuses such a run (`RunResult.refused`), and the
 * host dies here, so the two faces diverge on the same row. */
export class TapeValueMismatch extends Error { readonly _tag = "TAPE_VALUE_MISMATCH" }
```
Lean side, `Effect4/Semantics/Runs.lean:184`:
```lean
| .mismatch expected actual => pure (.finished (.refused expected actual) tape)
```
— no `emit`, so the log ends with **no row at all**. Host side, `runTraced`
(`tracer.ts:440-455`) special-cases only `TapeExhausted`; a `TapeValueMismatch` die falls
through to `sink.push({ kind: "done", outcome: outcomeWire(exit) })`, which renders
`{"defect":"TAPE_VALUE_MISMATCH"}` (via the `value instanceof Error` branch of `wire`).
So on a value mismatch Lean writes nothing and the host writes a `done` row — the two
faces disagree under mask `outcome`, the coarsest one.

No golden, fixture, mutant or battery exercises either class: `grep -rn
"TapeValueMismatch\|TAPE_VALUE_MISMATCH"` finds only the declaration and its one throw
site. `TapeSiteMismatch` is the same, plus it is *redeclared* locally in
`harness/trace/fiber-tail.ts:93` rather than imported.

Related: `Runs.lean:157` reports a value mismatch as `.mismatch site site` — expected and
actual collapse to the same site, so the payload carries no information.

**Why it matters.** A refusal path with no witness on either face, described in a
docstring as if it were checked, in the newest lowering rule.

**Proposed change.** Add a `wire-tail.ts`-style planted case to
`scripts/test-trace-goldens-gate.sh` for each of the two errors and decide the intended
parity: either Lean emits a `refused` row (new alphabet arm) or the host suppresses
`done` for these two defects the way it does for `TapeExhausted`. Import
`TapeSiteMismatch` in `fiber-tail.ts` instead of redeclaring it.

**Effort:** M. **Risk:** medium — the parity decision touches the shared alphabet.

---

### 13. `effect_atoms` answers `Val.unit` when a request fails to decode or the atom is unknown
**Category:** correctness

**Evidence.** `Effect4/Meta/Derive.lean:441-447` (one-parameter branch) and 462-468
(two-parameter branch) both emit:
```lean
| Option.some argument => Effects.Trace.ToVal.toVal ($atomName argument)
| Option.none => Effects.Trace.Val.unit
```
and line 471 appends a catch-all `| _ => fun _ => Effects.Trace.Val.unit` for an unknown
atom name. So on the Lean face a wire value that does not decode at the atom's request
type, or a misspelled atom, silently produces `[]` — a legal `Val` that flows into the
golden. On the host the same call is a real TypeScript expression (or a `ReferenceError`,
which is what `E4-TARGET-CE-025` is about).

**Why it matters.** `Atoms.eval` is the Lean side of the atom dispatcher whose whole
purpose is that "no atom exists in one face only". A total-by-unit fallback turns a
mismatch into a plausible-looking row.

**Proposed change.** Make `Atoms.eval : String → Val → Option Val` and let the flow
runner treat `none` as a frontier (`stuck`), the same way `plan` handles an unreadable
slot. That is one signature change plus the two `Option.none` arms.

**Effort:** M. **Risk:** medium — `AtomTable`/`tableService` consumers must handle the
`Option`.

---

### 14. `dec` relies on an unchecked invariant that Nat truncation never fires
**Category:** correctness

**Evidence.** `harness/trace/Generate.lean:82-84`:
```lean
  -- The job runner's counter atom: naturals truncate at zero on the Lean side,
  -- and the flow never calls it at zero.
  | dec (n : Nat) : Nat ⟪ "n - 1" ⟫ := n - 1
```
Lean `0 - 1 = 0`; the emitted `harness/trace/atoms.ts` has
`export const dec = (n: number): number => n - 1`, giving `-1`. The two faces agree only
because of a claim in a comment. The same class covers `succ` (unbounded `Nat` vs a
JavaScript number capped at 2^53−1 — that one *is* guarded, by `wire`'s
`Number.isSafeInteger` refusal and `Generate.lean`'s `admitted`, row `E4-TARGET-CE-015`).

**Why it matters.** The whole point of `effect_atoms` is one declaration per atom; a body
whose two spellings are only extensionally equal on a sub-domain reintroduces the
divergence the DSL removed, with no gate.

**Proposed change.** Either declare `dec` over `Int` (both faces total and equal), or add
a `⟪ … ⟫` side condition the elaborator can check on the golden corpus. Minimum: a
counterexample-register row recording the sub-domain assumption.

**Effort:** S for the register row, M for `Int`. **Risk:** low.

---

### 15. `tupleArgs` silently emits the wrong argument count for a non-identifier request
**Category:** correctness

**Evidence.** `Effect4/Target/TypeScript/Skeleton.lean:341`:
```lean
def tupleArgs (request : Expr) (arity : Nat) : List Expr :=
  match request with
  | .ident name => tupleProjections name arity
  | _ => [request]
```
`callOf` (line 350) calls it whenever `spec.arity ≥ 2`. So a request expression that is
not a bare identifier lowers a 3-parameter operation to a **1-argument** call, with no
refusal. Today every caller passes a `Slot.expr` (always `.ident`), so it is unreachable —
but it is unreachable by accident, and `Slot.catchValue` already produces
`.ident "a4.success"` (finding 18), which is one refactor away from breaking the
invariant.

**Why it matters.** This is precisely the shape of `E4-TARGET-CE-022` (a two-parameter
row lowered to a one-argument call), which the register records as repaired.

**Proposed change.** Make it `tupleArgs : Expr → Nat → Option (List Expr)`, `none` on the
non-ident case, and let `callOf` propagate the refusal into `flowModules?`'s existing
`Option`. Or take a `String` (the slot name) rather than an `Expr`, making the bad case
unrepresentable.

**Effort:** S. **Risk:** low.

---

### 16. `OpSpec.params` defaults to `[]`, so an under-specified row silently reports arity 1
**Category:** api / correctness

**Evidence.** `Effect4/Target/TypeScript/ScriptFlow.lean:50-58`:
```lean
  /-- The parameters of a family operation, binder and TypeScript spelling
  each. Empty on the hand-written rows of a table, which are unary. -/
  params : List (String × String) := []
…
def OpSpec.arity (spec : OpSpec) : Nat := max 1 spec.params.length
```
A hand-written `OpSpec` for a two-parameter operation that omits `params` gets
`arity = 1` and `callOf` emits a single-argument call — the exact defect
`E4-TARGET-CE-022` records, re-openable by omission. `errorTy : String := "never"`
(line 49) has the same shape for `performCatch`: a fallible operation whose row forgets
`errorTy` lowers its failure edge at type `never`.

**Why it matters.** Defaults on a lowering spec convert "forgot a field" into "lowered
wrongly" rather than "did not compile".

**Proposed change.** Drop both defaults and make `params` and `errorTy` required; provide
`OpSpec.unary` / `OpSpec.infallible` smart constructors for the hand-written table rows
that genuinely are unary. Add `#guard` in `MultiArgContract.lean` that every row of every
shipped `ServiceRow` has `params.length = ` the family's declared arity.

**Effort:** S. **Risk:** low; the compiler finds every site.

---

### 17. `Slot.name` smuggles member access into an identifier
**Category:** api

**Evidence.** `Effect4/Target/TypeScript/Skeleton.lean:107-108`:
```lean
  | .catchValue block => "a" ++ toString block.value ++ ".success"
  | .catchError block => "a" ++ toString block.value ++ ".failure"
```
and line 113 `def expr (slot : Slot) : Expr := .ident slot.name`. So `a4.success` is
handed to the pinned lean4-typescript AST as an **identifier**. It prints correctly
because the renderer emits identifiers verbatim, but it defeats
`Effect4.Target.EffectV4.bindingName` / `TypeScript.targetIdentifier`
(`EffectV4.lean:146`), which every other name in the profile passes through.

**Why it matters.** The one place the target AST's typing could have caught a malformed
name is bypassed, and the two Flow v3 slots are the ones that do it.

**Proposed change.** Add `Expr.member : Expr → String → Expr` to lean4-typescript (the
pinned package is a sibling repo the plan already schedules one edit to), and have
`Slot.expr` build `.member (.ident ("a" ++ …)) "success"`. Keep `Slot.name` returning the
base identifier only.

**Effort:** M (crosses into `~/Dev/lean4-typescript`, needs a version bump).
**Risk:** low; the rendered bytes are unchanged, so every golden stays byte-identical.

---

### 18. `check-trace-host.sh` is eight copies of the same block, with a double `mktemp`, clobbering traps, and a stale success message
**Category:** cleanup

**Evidence.** Lines 114-115:
```bash
fiber_generated="$(mktemp)"; trap 'rm -f "$generated" "$atoms_generated" … "$fiber_generated"' EXIT
fiber_generated="$(mktemp)"; trap 'rm -f "$generated" "$flow_generated" … "$layer_generated" "$fiber_generated"' EXIT
```
Two `mktemp`s in a row for the same variable — the first temp file is leaked and its trap
overwritten. Each subsequent `trap` re-spells a growing list and drops entries: line 87
drops `$atoms_generated`; line 136 drops both `$atoms_generated` and `$layer_generated`.
So every run leaks temp files.

The eight families each repeat the identical five lines (`mktemp`, `lake env lean --run
… <family>-fixture`, optional `--update` copy, `cmp -s`, `echo PASS`), differing only in
the family name.

Line 182:
```bash
echo "PASS host traces agree with every golden under every mask (straight-line, dispatch, structured, scope, layer, interrupt and fiber forms)"
```
omits `job`, `deferred` and `ref`, all of which the script runs.

The structured form runs only at the default yield setting (line 68-72 has no
`EFFECT4_MAX_OPS=3` variant), while dispatch runs at both — an asymmetry the script does
not state, unlike the fiber one, which is explained at line 120.

**Proposed change.** One `regenerate <family> <file>` shell function and one `mktemp -d`
with a single trap; drive the family list from `Generate.lean`'s own command list.
Fix the message and either add the structured yield-3 run or document why not.

**Effort:** S. **Risk:** low.

---

### 19. `test-trace-goldens-gate.sh` counts nine mutants as eight and never asserts the total
**Category:** correctness

**Evidence.** Line 16 `caught=0; total=8`; `grep -c '^expect ' scripts/test-trace-goldens-gate.sh` = **9**. The final line is
```bash
echo "PASS trace gates react to $caught/$total planted defects"
```
so a green run prints `9/8`, and `caught` is compared to nothing — dropping a mutant
would still print PASS. `test/contracts/flow-runner.contract.md:62` and
`docs/TRACE-DAG.md:61` both still say "4/4 planted defects".

**Proposed change.** Replace the literal with `total=$(grep -c '^expect ' "$0")` and add
`[ "$caught" -eq "$total" ] || exit 1`.

**Effort:** S. **Risk:** none.

---

### 20. `docs/TYPESCRIPT-TARGET-DAG.md` contradicts the code it is the authority for
**Category:** cleanup

**Evidence.** Header: "Status: ported syntax and renderer; target cutover open,
2026-08-31". Edge ledger:
```
| bridges | required-open | no checked Effect4-to-TypeScript lowering or source-target simulation exists yet |
| targets | required-open | direct TypeScript, pinned Effect v4, and language-service harnesses are not part of this port |
```
Since then: `Effect4/Target/TypeScript/{Skeleton,FlowLower,RegionLower,StructuredLower}.lean`
implement 29 lowering rules, `Effect4/Target/TypeScript/Simulation.lean` exists,
`scripts/check-lowering-types.sh` runs the pinned unpatched `tsc.original` with
`--declaration` against the lowered modules, and `harness/trace/check.sh` runs
`@effect/tsgo` strict diagnostics over them. `AGENTS.md` names this file an authority
document ("If two files appear to own the same fact, stop and repair the ownership map").

**Proposed change.** Re-state the two edges against the current evidence, or explicitly
route the lowering to `docs/LOWERING-COVERAGE.md` and `docs/TRACE-DAG.md` and shrink this
file to the retained syntax/renderer port.

**Effort:** S. **Risk:** low.

---

### 21. `docs/LOWERING-COVERAGE.md` cites a file that does not exist and a rule list that never landed
**Category:** cleanup

**Evidence.** Line 33, the `golden` evidence class row: "Produced by
`harness/trace/Emit.lean` through the traced service". `harness/trace/Emit.lean` does not
exist (`find . -name "Emit*.lean"` returns four schema fixtures and
`Effect4/Meta/Emit.lean`); the goldens come from `harness/trace/Generate.lean`.
The same wrong path appears at `misty-frolicking-naur.md:188`.

Line 34-36: "Later: `choose`, `jump-dispatch`, `loop-labelled`, `merge-block`,
`dispatch-fallback`, `region-onExit`, `region-scoped`." Of those seven names only
`dispatch-fallback` exists; the rules that actually landed are `choose-if`,
`dispatch-loop`, `block-case`, `structured-merge`, `region-enter/acquire/leave`.

Line 54-58 says the gate fails on "a golden path … whose digest drifted", but
`generate-lowering-coverage.sh` *computes* the digest fresh
(`pinned.append(f"{g}:sha256={sha(path)}")`) — drift is caught only transitively by
`check-lowering-coverage.sh`'s whole-file `cmp`.

**Proposed change.** Fix the path, delete the "Later" list (the census is now the
authority), and re-word the gate description to match what the generator and the checker
each do.

**Effort:** S. **Risk:** none.

---

### 22. `docs/TRACE-DAG.md` and `README.md` carry stale counts and pins
**Category:** cleanup

**Evidence.**
- `docs/TRACE-DAG.md:61`: "`generated/lowering-coverage.tsv` (**twenty-seven** rules …
  planted mutants (**4/4**))" then, in the same cell, "Flow v3 adds `perform-catch` and
  `branch-if` (appended last, twenty-nine rules)". The per-state tallies in that cell are
  right (12/12/5); the headline is not, and the mutant count is 9 (finding 19).
- `README.md`: "The generic effect algebra is the Effects package, pinned at `v0.1.0`."
  `lakefile.toml` pins `a117157` = tag `v0.7.0`. Six minor versions stale.
- `README.md` never mentions the trace/lowering lane, the goldens, or the coverage
  ledger — the lane with the most machinery in the repo.

**Proposed change.** Have `scripts/generate-lowering-coverage.sh` also emit a one-line
`count` summary the DAG cell quotes verbatim (the `runtime-coverage` skill's pattern), and
read the README's pin line from `lakefile.toml` in a check.

**Effort:** S. **Risk:** none.

---

### 23. `COORDINATION.md` is 177 KB of archive that every agent is told to read first
**Category:** dx

**Evidence.** 2699 lines, 176 898 bytes, 76 `##` sections. Line 9: "Last updated:
2026-08-31" — while sections dated 2026-09-03 run to line 2673. Only lines 1-159 are
live (`Who is active`, `Current claims`, `What collisions have already cost`,
`Operational facts worth not rediscovering`, `Working rules that follow`); lines 160-2699
are append-only "X landed, <date>" records.

The live part is itself stale: the `Who is active` table has Codex on
`Effect4/Data/Row.lean` and the Schema payload lane; the `Current claims` table holds 40+
rows including `Effect4/Context/Key.lean` marked "**closed, green, do not edit**" and a
dozen packets that landed days ago. `AGENTS.md` says "every agent reads `COORDINATION.md`
before writing and records a file claim there" — so every agent pays the archive and
reads a claims table nobody releases rows from.

**Proposed change.** Split: keep `COORDINATION.md` at the five live sections (target
< 200 lines) and move everything from `## Completed trust-gate repair, 2026-09-01`
onward to `docs/COORDINATION-ARCHIVE.md`, linked from the top. Add a claim-release step
to the handoff checklist in `AGENTS.md`.

**Effort:** S. **Risk:** low (pure move; `check-internal-citations.sh` may need the new
path added).

---

### 24. Generated evidence is committed under `harness/`, contradicting the routing rule, and embeds machine identity
**Category:** cleanup

**Evidence.** `harness/AGENTS.md`: "Deterministic reports and coverage projections belong
under `generated/` and are regenerated by a recorded command. Caches, installed
dependencies, transient logs, and **machine-specific paths are not canonical evidence**."
`AGENTS.md` authority map: "`generated/` | deterministic projections only".

But `harness/trace/receipts/**` (35 JSON files, 548 KB) and `harness/trace/types/**`
(17 receipts) are committed, and each receipt records
`"node": "v22.23.2", "platform": "darwin-arm64"` plus `"primitives": 207` — all of which
change with the machine or the fixture. `git show --stat 2ea17e4` shows six receipts
added in the job-runner commit and `f13afac` shows all six rewritten (9 lines each) the
next day.

Nothing gates them: `check-trace-host.sh` writes receipts with `--receipt` and never
`cmp`s a committed one, so committing them buys no drift detection — only diff noise.

**Proposed change.** Either move `receipts/` and `types/` under `generated/` and add a
drift gate that compares the pin-bearing fields (not `node`/`platform`/`primitives`), or
gitignore them and let the ledger join read them from a run. Do not keep both properties.

**Effort:** M. **Risk:** low, but touches the coverage join's paths.

---

### 25. The counterexample register has no `REPAIRED` status and records repairs in two different columns
**Category:** api

**Evidence.** `test/counterexamples/REGISTER.md:6-11` defines four statuses: `PINNED`,
`SEEDED`, `RESERVED`, `MOVED`. A repaired row keeps `SEEDED` and appends prose:
- `E4-FLOW-CE-026` / `-027` (repaired in `645067a`) put
  "**Repaired 2026-09-03 (Flow v3, lean4-effects v0.7.0):** …" at the end of the
  **Forced repair** cell;
- `E4-TARGET-CE-022` (line 138) puts "**Repaired 2026-09-03**, by lifting the restriction
  rather than refusing the row: …" in the **Witness / evidence** cell.

So the same fact lives in two different columns depending on who wrote it, and the
`Status` column is uninformative for the rows that matter most. No script validates the
file: of the seven scripts that read `REGISTER.md`, all extract specific ids
(`check-live-stack.mjs:50-56` hashes three rows); none checks id uniqueness, status
vocabulary, column count, or that a cited witness path exists. Id collisions across
parallel packets are a live hazard (`645067a`'s message: "register rows 026/027
repaired").

**Proposed change.** Add a `REPAIRED` status and a `Repaired at` column (date + commit),
and a `scripts/check-counterexample-register.sh` that validates: unique ids, monotone
numbering per family, status in the vocabulary, six columns, every `` `path` `` in the
witness cell exists.

**Effort:** M. **Risk:** low.

---

### 26. Thirty-nine of sixty-one goldens are generated and host-run but joined to no rule
**Category:** cleanup / build

**Evidence.** `generated/lowering-coverage.tsv` cites 21 distinct golden names
(`grep -o '[a-zA-Z/.]*:sha256'` → 21 unique). `find generated/traces -name '*.tsv'` = 61
(60 + `masks.tsv`). The uncited 39 are the whole `deferred/`, `ref/`, `scope/`, `layer/`,
`fiber/` families plus `job/jobRunner.interrupt`, `job/jobRunnerMasked.masked`,
`flow/swap.budget`, `probe.empty`, `recover.empty`.

They are still fully paid for: `generate-trace-goldens.sh` writes them, `check-trace-goldens.sh`
regenerates and diffs them, and `check-trace-host.sh` runs each once or twice
(78 of the 123 node runs).

**Why it matters.** Two thirds of the corpus's sweep cost produces no ledger row, and the
ledger consequently reads as if the trace lane covers 21 goldens.

**Proposed change.** Decide per family: either add rules (the `Layers`, `Deferreds`,
`Refs`, `Scopes`, `Fibers` families are lowered by the *same* rules and their goldens
should be cited as extra evidence for them) or record in `docs/LOWERING-COVERAGE.md` that
these families are family-conformance evidence, not rule evidence, and say so in the
ledger's header.

**Effort:** M. **Risk:** low.

---

### 27. The three masks are nested, so "agreement under every mask" is one fact reported three times
**Category:** correctness (reporting)

**Evidence.** `generated/traces/masks.tsv`:
```
mask	outcome	0 0 0 0 0 1 1
mask	m1	    1 1 0 0 0 1 1
mask	m2	    1 1 1 1 1 1 1
```
Field order is ops, answers, decisions, regions, finalizers, outcome, frontier
(`Trace.maskRow`, `Effect4/Target/TypeScript/Trace.lean:91`). `m2` keeps every row, and
`m1 ⊂ m2`, `outcome ⊂ m1`. Since `project` is a filter, agreement under `m2` implies
agreement under the other two. Every receipt reports `"results": {"outcome":"ok",
"m1":"ok","m2":"ok"}` and `harness/README.md` says "the host traces agree with every
golden under **every mask**".

**Why it matters.** Three "ok"s read as three independent checks; they are one, plus two
thirds of the comparison work per run.

**Proposed change.** Either add a genuinely non-nested mask (e.g. decisions-only, or
regions+finalizers without ops) so "every mask" carries information, or state the nesting
in `docs/TRACE-DAG.md` and have `trace.mjs` report the maximal mask plus "implied".

**Effort:** S. **Risk:** low.

---

### 28. `Skeleton.lean` has a blanket `Classical.choice` exemption and declares two theorems
**Category:** correctness

**Evidence.** `Effect4Test/Audit/AxiomGate.lean:60-79` lists
`targetImplementationModules`, module-granular, ending:
```lean
  -- The control-skeleton IR (packet D3): its `render` traverses strings; the
  -- skeleton's laws are stated over the `String`-free IR, not over `render`.
  , `Effect4.Target.TypeScript.Skeleton ]
```
But `Effect4/Target/TypeScript/Skeleton.lean` declares `theorem emitNode_eq` (line 511)
and `theorem emitWith_eq` (line 526) — the theorems that pin agreement between the
dispatch and structured emitters, per the module docstring ("`Structure.emitNode_eq`
below pins the agreement at `Stmt` as a theorem rather than leaving it to the fixture
bytes"). The exemption is a *ceiling lift for the whole module*, so those two theorems
could reach `Classical.choice` and the gate would not object. The stated invariant ("the
laws are stated over the `String`-free IR") is a convention, not a gate.

**Why it matters.** The one place the axiom gate is load-bearing for the lowering is the
one place its granularity is coarsest.

**Proposed change.** Split the module: move `render` and the string-facing code to
`Effect4/Target/TypeScript/SkeletonRender.lean` and exempt only that, leaving `Skeleton`
at the `propext`/`Quot.sound` ceiling. Alternatively use the existing
`choiceImplementationDeclarations` (exact-declaration) mechanism, which the gate already
supports and already staleness-checks (lines 320-326).

**Effort:** M. **Risk:** medium — an import-graph change; coordinate with whoever owns
`SkeletonSemantics.lean` (155 KB).

---

### 29. `tracer.ts` exports a dead `Decisions` service that duplicates a generated Context tag
**Category:** cleanup

**Evidence.** `harness/trace/tracer.ts:301-304`:
```ts
export class Decisions extends Context.Service<Decisions, {
  readonly choose: (site: number) => Effect.Effect<boolean>
}>()("Decisions") {}
```
Every tail imports `Decisions` from its *generated fixture* instead
(`flow-tail.ts:2` and `structured-tail.ts:2` from their fixtures,
`interrupt-tail.ts:24` from `flow-fixture.ts`, `job-tail.ts:32` from `job-fixture.ts`).
Nothing imports the tracer's. Worse, the generated one carries two methods —
`job-fixture.ts:16-19` declares `choose` **and** `report` — while the tracer's declares
only `choose`, and both use the tag string `"Decisions"`. Two classes with one Context
key is a runtime-unifies / type-splits hazard.

**Proposed change.** Delete `tracer.ts`'s `Decisions`. `decisionsFromTape` already returns
a plain `{ choose, report, consumed }` object that the fixtures' own service accepts.

**Effort:** S. **Risk:** none.

---

### 30. Half of `tracer.ts`'s exported surface is unused by anything
**Category:** cleanup / api

**Evidence.** Of 26 exported names, these are referenced by no other file in
`harness/trace`: `Wire`, `Rows`, `TracerDefect`, `HandleBrand`, `handleIndex`,
`wireArgs`, `Spelling`, `parseSpelling`, `wireTyped`, `FrameSnapshot`, `RunReport`,
`TapeValueMismatch`, and `Decisions` (finding 29). `wire-tail.ts` — the module that
exists to probe the wire encoding — imports none of the spelling machinery.

`harness/README.md` calls `tracer.ts` part of the checked file set and
`tsconfig.json` lists it, so the exports typecheck; nothing exercises them.

**Proposed change.** Un-export the internals (`wireArgs`, `wireTyped`, `parseSpelling`,
`handleIndex`, `wireTuple` already private) and either delete the unused types or add a
`spelling-tail.ts` that exercises `parseSpelling`/`wireTyped` against the depth-three
profile the answer-profile contract froze — that grammar currently has no direct test.

**Effort:** S to un-export, M to add the probe. **Risk:** low.

---

### 31. `fiber-tail.ts` reimplements the tape reader instead of importing it
**Category:** cleanup

**Evidence.** `harness/trace/fiber-tail.ts:83-104` re-declares `TapeExhausted`,
`TapeSiteMismatch` and a local `decide()` that duplicates `decisionsFromTape`'s cursor
logic — including the same `sink.push({ kind: "decide", … })` row and the same
`entry[0] !== cursor` check, except it compares against the *cursor* rather than the site:
```ts
if (entry[0] !== cursor) throw new TapeSiteMismatch(`wanted site ${cursor}, tape has ${entry[0]}`)
```
whereas `tracer.ts:319` compares against the caller-supplied `site`. The two readers can
therefore disagree about what a site is.

**Proposed change.** Export a `tapeReader(tape, sink)` from `tracer.ts` that both the
Effect-valued `decisionsFromTape` and the synchronous fiber path build on.

**Effort:** S. **Risk:** low; the fiber goldens pin the behaviour.

---

### 32. `effect_atoms` supports exactly one and two parameters, with the failure showing as `throwUnsupportedSyntax`
**Category:** api

**Evidence.** `Effect4/Meta/Derive.lean:108-111`:
```lean
declare_syntax_cat atomOp
syntax "| " ident effectParam " : " term " ⟪ " str " ⟫ " " := " term : atomOp
/-- A two-parameter atom: the flow face sees its request as the pair. -/
syntax "| " ident effectParam effectParam " : " term " ⟪ " str " ⟫ " " := " term : atomOp
```
and the elaborator (lines 428-469) has two near-identical ~25-line branches followed by
`| _ => throwUnsupportedSyntax`. A three-parameter atom fails at the parser with no
guidance, in contrast to the elaborator's own good messages
(`"effect_atoms: `{atomName.getId}` is not a legal target identifier"`).

The two branches differ only in how they build `request`/`tsRequest` (a `×` and a
`readonly [A, B]`) and the `OfVal` pattern — the same right-nesting `tupleProjections`
and `Effects.Trace.ToVal` already implement generically.

Note the corpus already has both spellings for a pair-taking atom:
`snd (ticket : Handle "JobQueue" × Nat)` (one parameter, product type) and
`addNat (left : Nat) (right : Nat)` (two parameters) — two ways to say the same thing.

**Proposed change.** One production `syntax "| " ident effectParam+ …` and one branch that
folds the parameter list into the right-nested product, mirroring `effect_signature`,
which already handles `effectParam*`. Add an explicit `throwErrorAt` for the empty case.

**Effort:** M. **Risk:** low; the emitted rows for arity 1 and 2 must stay byte-identical
so the goldens do not move.

---

### 33. `harness/effect-v4-family/atoms.ts` is hand-written, which `E4-TARGET-CE-025` forbids
**Category:** cleanup

**Evidence.** `harness/effect-v4-family/atoms.ts` is two lines with a hand-written
docstring ("its Lean model is `succ` **in Generate.lean**") and none of the generated
header block that `harness/trace/atoms.ts` carries ("Generated by Effect4 (Effect v4
profile) … Do not edit."). `harness/effect-v4-family/Generate.lean:15` declares the atom
in a plain docstring (`/-- A pure atom; `atoms.ts` carries its host body. -/`) rather than
with `effect_atoms`, and `harness/effect-v4-family/check.sh` byte-compares only
`fixture.ts` — never `atoms.ts`.

`test/counterexamples/REGISTER.md:140` (`E4-TARGET-CE-025`) states the forced repair:
"declare an atom once with `effect_atoms` … and derive every face from the row list … 
byte-compared by `scripts/check-trace-host.sh`". This harness is a live instance of the
attacked shape.

**Proposed change.** Move `effect-v4-family` onto `effect_atoms` and byte-compare its
`atoms.ts` in `check.sh`, exactly as `check-trace-host.sh:20-22` does.

**Effort:** S. **Risk:** low.

---

### 34. Fifteen of fifty-seven scripts are in the sweep; one has no inbound reference at all
**Category:** dx

**Evidence.** The sweep summaries name 15 steps. `scripts/` holds 57 files (8372 lines).
Not run by any sweep: `check-live-stack.mjs`, `test-live-stack-mutations.mjs`,
`check-fiber-supervision-host.sh`, seven `check-schema-*.sh`, their `test-*-gate.sh`
partners, `check-corpus-sources.sh`, `check-data-row-assurance.sh`,
`check-environment-context-key-evidence.sh`, `report-effect-runtime-coverage.sh`,
`test-source-trust-tokenizer.sh` (that one runs *inside* `test-trust-gate.sh:164`).

`scripts/test-corpus-sources-gate.sh` has **zero** inbound references anywhere in the
repo — no doc, no contract, no COORDINATION row, no other script.

There is no entry point: no `Makefile`, `justfile`, `package.json`, or `scripts/all.sh`.
`harness/README.md` names five entry points; `README.md` names one (`test-trust-gate.sh`).
The sweep exists only as a scratchpad of `.log` files.

**Proposed change.** Add a `justfile` (or `scripts/sweep.sh`) with named targets —
`just hermetic` (host-free: goldens, coverage, citations), `just host` (trace host, types,
patched, property), `just gates` (the mutation self-tests), `just all` — that writes the
same `summary.tsv` the ad-hoc sweep produces. Reference it from `README.md` and
`harness/README.md`. Retire or route `test-corpus-sources-gate.sh`.

**Effort:** M. **Risk:** low.

---

### 35. Adding one program family costs 27 files
**Category:** dx

**Evidence.** `git show --stat 2ea17e4` ("JobRunner: the first real program"): 27 files,
3203 insertions. The mandatory ones, by kind:

| kind | files | what |
| --- | --- | --- |
| Lean generator | 1 | `harness/trace/Generate.lean` (+400 lines: family, rows, programs, entries, **six** new `main` commands) |
| Lean batteries | 3 | contract + two counterexample modules, plus an `Effect4Test.lean` import line |
| host TS | 3 | `job-fixture.ts` (generated), `job-tail.ts`, `job-queue.ts` (hand-written) |
| goldens | 6 | `generated/traces/job/*.tsv` |
| receipts | 6 | `harness/trace/receipts/job/*.json` |
| scripts | 2 | a new loop in `check-trace-host.sh` **and** in `generate-trace-goldens.sh` |
| ledger | 1 | `LoweringCoverage.lean` rows (in the follow-up commit) |
| docs/records | 4 | `COORDINATION.md`, `docs/TRACE-DAG.md`, `docs/research/…`, `REGISTER.md` |
| **missed** | 1 | `harness/trace/tsconfig.json` — see finding 4 |

Six of the eight steps are mechanical: the `main` command arms, the shell loop in each of
the two scripts, the receipt directory, the tsconfig entry.

**Proposed change.** Make a family a *row*: one `FamilySpec` in `Generate.lean` (name,
programs, tail file, whether it runs at both yield settings) that drives (a) a single
`all` generator command, (b) a single loop in `check-trace-host.sh` reading
`run families`, and (c) the tsconfig `files` list. That collapses the 27 to roughly 12 and
makes the tsconfig omission impossible.

**Effort:** L. **Risk:** medium; it is the natural home for findings 11, 18 and 4.

---

### 36. Several scripts are macOS-only, while CI is Ubuntu
**Category:** build

**Evidence.** `scripts/test-trace-goldens-gate.sh:45,52` uses BSD `sed -i ''` (GNU sed
reads `''` as the next file). Fifteen scripts use `shasum -a 256`
(`generate-trace-goldens.sh:11`, `generate-lowering-coverage.sh`, `check-lowering-types.sh`,
`check-lowering-property.sh`, …) rather than `sha256sum`. `.github/workflows/lean_action_ci.yml`
runs on `ubuntu-latest` — which is why none of these are in CI today, and why finding 5
cannot be fixed without fixing this first.

**Proposed change.** A tiny `scripts/lib/portable.sh` with `sha256()` and `sed_inplace()`
sourced by the rest, or standardise on `python3 -c` (already a dependency of three
generators).

**Effort:** S. **Risk:** low.

---

### 37. `generate-lowering-coverage.sh`'s self-test overrides leave no mark on the output
**Category:** api

**Evidence.** Lines 14-22 accept `--sources`, `--traces` and `--receipts` "self-test
only", and lines 23-26 explicitly refuse two environment-variable overrides:
```bash
for variable in EFFECT4_LOWERING_COVERAGE_SOURCE EFFECT4_LOWERING_COVERAGE_CANDIDATE; do
  [ -z "${!variable:-}" ] || { echo "FAIL $variable is not an admitted override" >&2; exit 2; }
done
```
But the printed header block hard-codes the real paths, so a ledger generated with
`--receipts /tmp/anything` is byte-identical to a genuine one. The env-var refusal shows
the risk was recognised; the flag path reopens it.

**Proposed change.** Print the three roots into the header (`source`, `traces`,
`receipts` rows) so a self-test ledger is visibly not a real one, and have
`check-lowering-coverage.sh` require them to be the defaults.

**Effort:** S. **Risk:** none.

---

### 38. `docs/research/*.md` files are cited as evidence but are not authority documents
**Category:** cleanup

**Evidence.** `docs/research/2026-09-03-job-runner.md:190` is cited for the
`perform-tuple` rule-count claim; `docs/research/2026-09-02-schema-consumer-survey.md:121`
cites `Lower.lean:21–63` by line number. `AGENTS.md`'s authority map does not list
`docs/research/`, and `scripts/check-internal-citations.sh` (per COORDINATION.md's
operational facts) rejects line-numbered citations only into six named files — so the
research directory can drift freely while being cited by the DAG documents.
`misty-frolicking-naur.md` (27 KB, "Plan: trace-driven lowering …") sits at the repository
root, is cited from `COORDINATION.md` and `test/contracts/flow-runner.contract.md:53`,
and contains the same stale `harness/trace/Emit.lean` reference as finding 21.

**Proposed change.** Add `docs/research/` to the authority map as "dated, immutable
research records — never cited as the owner of a live fact", move
`misty-frolicking-naur.md` into it under a dated name, and extend
`check-internal-citations.sh`'s line-citation refusal to `Lower.lean` and the other
census sources.

**Effort:** S. **Risk:** low.

---

### 39. The structured form is checked at one yield setting and the fiber family at one, without symmetric documentation
**Category:** correctness

**Evidence.** `scripts/check-trace-host.sh:68-72` runs `structured-tail.ts` once, at the
default budget, inside the flow loop that runs `flow-tail.ts` twice. The fiber loop
(lines 120-131) also runs once, but with eleven lines of comment explaining exactly why
(`counterexample: E4-SEM-CE-011`). The structured omission has no comment.
`docs/LOWERING-COVERAGE.md` says "The structured module … is checked against the same
goldens as the dispatch module, so a rule's host and property evidence covers both forms"
— which is true for the default setting only.

**Proposed change.** Add the `EFFECT4_MAX_OPS=3` structured run (it is a two-line change
and the property loop already runs `property-structured-tail.ts`), or record the refusal
beside the fiber one.

**Effort:** S. **Risk:** low; if it diverges, that is a finding in itself.

---

### 40. Region and interrupt rules are `pinned` while their goldens are host-green — the same bookkeeping gap as finding 6, at a different level
**Category:** correctness

**Evidence.** `generated/lowering-coverage.tsv` gives `region-enter`, `region-acquire`,
`region-leave` state `checked` with `typeReceipt = 1`, and `harness/trace/types/flow/`
does hold `regionNested.empty.receipt` etc. But `region-masked` and `interrupt-point` are
`pinned 0 0 0`, while `harness/trace/receipts/flow/interrupt/interruptMasked.json` exists
and `check-trace-host.sh:101-112` runs the interrupt goldens at **both** yield settings —
more thoroughly than the region goldens, which the ledger rates higher. The ledger's
ordering of confidence is inverted relative to the evidence actually collected.

**Proposed change.** Folded into finding 6 — deriving the columns from disk fixes this
row too. Listed separately because it is the one place the ledger's *ranking* misleads,
not just its counts.

**Effort:** (part of 6). **Risk:** low.

---

## Quick wins (under an hour each)

1. **Regenerate and commit the 55 goldens** so `check-trace-goldens.sh` is green on main
   (finding 2a).
2. **`total=$(grep -c '^expect ' "$0")` plus an equality assert** in
   `test-trace-goldens-gate.sh` (finding 19).
3. **Fix the final PASS message** in `check-trace-host.sh:182` to name job, deferred and
   ref; delete the duplicate `fiber_generated` line and collapse the traps to one
   `mktemp -d` (finding 18).
4. **Delete `tracer.ts`'s `Decisions` class** (finding 29).
5. **Add the seven missing roots to `harness/trace/tsconfig.json`** and see what tsc says
   (finding 4, first half).
6. **Add a `cpSync` filter for `patched/_copy`** in `effect4-tools/packages/harness/trace.mjs`
   — biggest speedup per line changed in the whole survey (finding 1).
7. **Fix `docs/LOWERING-COVERAGE.md:33`** (`Emit.lean` → `Generate.lean`) and delete the
   stale "Later:" rule list (finding 21).
8. **Fix `README.md`'s Effects pin** `v0.1.0` → `v0.7.0` (finding 22).
9. **Fix `docs/TRACE-DAG.md:61`**: twenty-seven → twenty-nine, 4/4 → 9/9 (finding 22).
10. **Put the full 40-character sha in `lakefile.toml`** and drop the "to be tagged"
    comment (finding 10).
11. **Emit `foreign` from the fixture** or at minimum correct the three job-tail entries
    to `succ, dec, nonEmpty, positive` (finding 7).
12. **Retire or route `scripts/test-corpus-sources-gate.sh`** (finding 34).

---

## Packets

Ordered; packets A and B are independent and can run in parallel.

### Packet A — "The sweep is red and slow" (findings 1, 2, 11, 5, 36)
Make the gates green, fast and CI-able, changing no semantics.
1. `trace.mjs` copy filter (1).
2. Portability shim, `shasum`/`sed -i` (36).
3. `Generate.lean all <dir>`, one process for the whole corpus (11).
4. Regenerate + commit goldens (2a).
5. Add the three host-free gates to `.github/workflows/lean_action_ci.yml` (5).
**Exit:** `check-trace-goldens.sh` green in CI on Ubuntu; sweep host step under two
minutes. **Effort:** M. **Owner note:** touches `~/Dev/effect4-tools`, so bump and
re-pin `EFFECT4_TOOLS` consumers.

### Packet B — "The ledger tells the truth" (findings 3, 6, 40, 26, 22, 21)
1. Drift gate for `generated/lowering-property.tsv`; re-run the corpus at the current pin (3).
2. Derive `host`/`property`/`typeReceipt` from disk in `generate-lowering-coverage.sh`;
   keep the Lean row for `state` and `proof` (6, 40).
3. Decide the 39 uncited goldens: cite or classify (26).
4. Regenerate the ledger and update the two doc cells from its `count` rows (22, 21).
**Exit:** every rule's state derived from files on disk; no doc quotes a hand-copied
count. **Effort:** M–L.

### Packet C — "Type the Flow v3 lane" (findings 4, 17, 15, 16)
1. tsconfig covers every `harness/trace/*.ts`; fix the diagnostics that surface (4).
2. `Expr.member` in lean4-typescript; `Slot.expr` stops forging identifiers (17).
3. `tupleArgs` returns `Option`; `callOf` propagates (15).
4. `OpSpec.params`/`errorTy` lose their defaults; smart constructors for unary rows (16).
5. Type receipts for `job-fixture.d.ts` join the ledger.
**Exit:** `perform-catch`, `branch-if`, `perform-tuple` reach `checked` with a real type
receipt. **Effort:** L (crosses a package boundary). **Prerequisite:** packet B step 2,
so the ledger reflects the new receipts.

### Packet D — "Faces cannot drift silently" (findings 7, 8, 12, 13, 14)
1. Emit `foreign` and the job scenario table from Lean; add `seed` to the golden header (7, 8).
2. Plant `TapeSiteMismatch` and `TapeValueMismatch` mutants and settle the Lean/host
   parity for a refused run (12).
3. `Atoms.eval : String → Val → Option Val`; frontier on a decode failure (13).
4. `dec` over `Int`, or a register row for its sub-domain (14).
**Exit:** no hand-copied constant crosses the Lean/host boundary in `harness/trace`;
both tape-refusal paths have witnesses. **Effort:** L. **Risk:** touches the shared
alphabet — needs the trace-lane owner.

### Packet E — "Rule identity, not rule position" (findings 9, 28, 37)
1. Replace the four positional windows with id-based pins; reorder `Rule.all` to match
   the inductive (9).
2. Split `Skeleton.lean` into IR + renderer so the axiom exemption is exact (28).
3. Header rows for the coverage generator's path overrides (37).
**Exit:** a new rule can be inserted anywhere and touches one battery. **Effort:** M.

### Packet F — "Records people actually read" (findings 23, 25, 24, 38, 34, 35)
1. Split `COORDINATION.md`; release the dead claims (23).
2. `REPAIRED` status + `Repaired at` column + `check-counterexample-register.sh` (25).
3. Move `receipts/`+`types/` under `generated/` with a pin-only drift gate, or gitignore
   them (24).
4. Route `docs/research/` and `misty-frolicking-naur.md` in the authority map (38).
5. `justfile` with `hermetic` / `host` / `gates` / `all`; retire the orphan script (34).
6. `FamilySpec` so a new family is a row, not 27 files (35).
**Exit:** an onboarding brief is `AGENTS.md` + a 200-line `COORDINATION.md` + `just all`.
**Effort:** L. **Note:** step 6 is the natural landing site for packet A step 3 and
packet C step 1; sequence it after both.

### Packet G — "Small cleanups" (findings 18, 19, 20, 29, 31, 32, 33, 39, 27)
The quick-wins list plus: fiber-tail tape reader unification (31), `effect_atoms`
arity generalisation (32), `effect-v4-family` onto `effect_atoms` (33), the structured
yield-3 run (39), a non-nested mask or a documented nesting (27), and un-exporting
`tracer.ts`'s internals with a `spelling-tail.ts` probe (20, 30).
**Effort:** M in aggregate, each item S. **Risk:** low. Good filler between the larger
packets.
