# Review of Gemini's domain-model spec v2 (coordinator, 2026-10-01 ~21:40)

Reviewed `gemini/domain-model-spec.md` (v2, 19:16) and `gemini/note.md` (19:17) against HEAD
`198dd533` on `refactor/phase1-phase3`, after Codex's second-eyes review of v1
(`/private/tmp/codex-second-eyes-2026-10-01/domain-spec-review/review.md` and
`domain-spec-ledger-review.md`, 19:10–19:14). Evidence words as in `brief-gemini.md`: proved,
tested, reading, assumed. Every file:line below was read in the tree tonight.

## Verdict

Direction right, not implementation-ready. v2 takes Codex's three blockers (the report is not a
schema document; no erasure claim; a claims registry independent of the declaration census) and
the concept-first organization. It fails on exactness in the one place it offers as the test of
the design: of the four claims in its §6 slice, three carry a wrong name, scope or identifier.
The "verified literature locators" were verified against nothing (no copy is in the tree or on
this Mac), and two are impossible as written. Gemini builds it; two seats fix the spec first.

## What v2 fixed (checked)

- Nine erased keys, `src/Effect4/Schema/Bridge.lean:105-108` (reading). Correct.
- `Schema.Literals([...])`, `Schema.Record(k, v)`, `Schema.NullOr`: the forms Codex typechecked
  under tsgo 7.0.0-dev.20260629.1 against effect 4.0.0-rc.112 (tested, Codex). v2's new
  `Schema.Union([...])` and `Schema.NonNegativeInt` were not in that probe: untested.
- The report is a plain record, not an `Effect4.Document`; entity ids separate from `$ref`.
- Claims exist independently of declarations; `absent` and `refuted` are states.

## What v2 got wrong (checked against the tree)

1. Witness namespace. `seq_typed` lives in `namespace Effect4.Program.Typed`
   (`src/Effect4/Laws/Program/Typed/Seq.lean:34`, theorem at `:59`). The slice JSON names
   `Effect4.Laws.Program.Typed.seq_typed`. Codex §7 flagged exactly this class (`fits_mono`).
2. Ledger scope. The goal is `Effect4.Program.Typed.M3bAssembly.denoteR_typed`, declared at
   `src/Effect4/Laws/Program/Typed/Assembly.lean:1637` as
   `theorem denoteR_typed (root : ProgramSource) : ProofGraph.Obligation (DenotesTyped root)`;
   `:1839` is the `#proof_wanted` marker, not the goal. v2 writes `Effect4.Machine.M3bAssembly`
   and a "formal judgment" (`HasTy env t ty ⟹ DenotesTyped (denoteR t) ty`) that is not the
   statement. The statement is `DenotesTyped root`.
3. Counterexample id. `E4-TYPED-CE-001` is RETIRED (`Test/Counterexamples/REGISTER.md:135`:
   "A term that types always evaluates"; "the ID is kept and never reused").
   `typedProg_not_bind_closed` (`Test/Program/TypedProgBindRed.lean:32`) has no register row
   (grep: 0 hits). TYPED ids run 001–029 (023 unused). A refuted claim must cite a real row or
   the receipt proposes one; the report must refuse an id the register does not have.
4. Hand-typed statement. The JSON's `seq_typed` judgment drops the world `w`, `w.leHost w'`,
   `Fits w' v mid.answer` and `root`, and names the shape `seq p k` where the theorem says
   `(guardR .onSuccess a).bind (seqR k)`. Display strings are printed from the environment,
   never typed (Codex ledger review §4).
5. `"leanVersion": "4.15.0"`. `lean-toolchain` says `leanprover/lean4:v4.33.1`.
6. Paths. `tools/architecture/` does not exist; the architecture map's one hand input is
   `tools/Tools/ArchitectureRoles.lean` (a Lean file). `ts/eff/src/` does not exist (ts/eff is
   flat: `check.ts`, `read.ts`, `*.gen.ts`, `test/`). `make check-tsgo` is the "no typescript
   below 7" check (`Makefile:318-322`), not a place to run a schema validation.
7. The committed artifact carries a wall-clock `timestamp`; Codex's acceptance condition 5
   forbids it (same input, same bytes).
8. Literature. Nothing is vendored, so nothing was verified. "ATTAPL chapter 3 … pp. 3–44"
   cannot be right (a third chapter does not start on page 3; Codex: ch. 3 is effect types and
   regions). "Generic Java ch. 20" contradicts the brief's own `tapl-20-recursive` and Codex
   ("chapter 20 starts at p. 267"). `gemini/chapter-table.md:326` still says "ATTAPL Chapter 8:
   Logical Relations" after the spec moved it to ch. 6; `gemini/note.md:314` gives ch. 6 a title
   mixing in typed assembly language. The owner's steer (21:30): vendor the real sources and
   cite from them; no locator from memory.

## Still open from Codex's list

- Ledger §4: the tooling record keeps `ProofRef`/`Goal`; strings are display. v2 keeps
  `statementStr : String`, `formalJudgment : String`, no `ProofRef`.
- Ledger §2: `axiomGatePasses : Bool` per declaration is not computable without the gate's
  policy; Codex asked for `pass | fail | notAudited` plus the policy identity, the narrow check
  named `withinSemanticAxiomCeiling`.
- Ledger §3: the extraction universe. v2 has `loadedRoots` and `ModuleFact.isLoaded`; no
  excluded-declaration census, no freshness, so "unplacedCount: 0" is relative to nothing stated.
- Review §6: how a declaration gets its concept (attribute, module default, inherited and shown
  as provisional) is unspecified; §7b's attribute and census survive only as the words
  "declaration attributes".
- The cut (rows 163, 128, …) has no place in the model; Codex: an applicability decision with a
  reason and an owner, not a status.
- Review §8's six acceptance conditions are not in the spec.

## What the ledger commands already give (reading, for the spec)

`src/Effect4/Laws/Auto/Obligations.lean:15-24`: a goal is a theorem whose type concludes
`ProofGraph.Obligation p`. `:26-31`: `#proof_wanted` adds `<goal>.wanted`, a `ProofWanted`
marker, to the environment (so a driver sees it after `importModules`). `:34-44`:
`#obligation_proved` adds `<goal>.checked` at the extracted proposition. `:76-79`: an existing
`.checked` is validated with `ProofRef.validate` (`tools/ProofGraph/Proof.lean:18-28`: theorem
kind, closed, universe names, `isDefEq` on the proposition, axioms within
`[propext, Quot.sound]`). Status derivation needs nothing new.

## Next

Seat A (sources, citations audit) and Seat B (spec v3, the Gemini implementation brief), briefs
beside this note (`brief-seat-A-sources.md`, `brief-seat-B-spec.md`); then Gemini lands.
