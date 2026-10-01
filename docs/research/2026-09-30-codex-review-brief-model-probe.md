# Codex review brief: the model-probe plan

Written 2026-09-30 by the coordinator. The owner, on reading the model probe's synthesis: "H2 go,
D1–D6 as recommended… first let's have Codex review the plan." The rulings are held until this
review returns. Nothing is implemented from this brief.

**What is under review.** The synthesis of the model probe,
[`2026-09-30-model-probe/synthesis.md`](2026-09-30-model-probe/synthesis.md), with the four seat
notes and four verifier notes beside it (completeness, pedigree, TREE, programs). It reviewed the
requirements note [`2026-09-30-full-program-model-requirements.md`](2026-09-30-full-program-model-requirements.md)
at `7cae243a`. The tree has since moved: B, D's independent parts and E are merged (`541283e1`),
and the registers say so (`ede35824`). Review against the current head.

**The plan, in six parts.** Attack each. Where a claim is checkable in Lean, check it; a reading
is a reading.

1. **H2 can go** (synthesis §5.1). The claim: no requirement changes the exit judgment's shape,
   `ExitOk w ty ex := FitsExit w ty ex ∧ NoShapeDefect ty ex`, on two conditions: the service
   table enters the typed state as a static component of the world, not as a parameter of the
   value judgments; and `NoShapeDefect` is stated over the core `Defect` alphabet and
   `ty.requires`, with no signature parameter. Questions:
   - Is there a requirement, a ruling or a counterexample under which the shape must change?
   - Does part two (`missingService` moved outward across frames) have a local proof route through
     row 51's context-wide `ServiceOk` and the provision algebra's `satisfies_iff_subset_keysRow`,
     or does it need a saved-frame argument the probe did not see
     (`2026-09-30-seat-codex-slice6-evidence/H2/diagnostics/MissingServiceTransport.lean`)?
   - Do your eight measured bodies (receipt, H2) stay eight under the two conditions?
2. **The six rulings the owner intends** (synthesis §6; the rows as they would read):
   - D1: "The signature parameter is Σ_app (the row table and the service table); Σ_core grows
     under DI-47; extension is conservative under C1–C8, written into DB-01."
   - D2: "The typed state reads the service table as a static world component" (shape A, 13–17
     declarations, against shape B's 59 statements and 15 bodies).
   - D3: "Declared service carriers are per service code" (`Machine/Key.lean`'s `carrier_def`
     frame; per key admits one code at two carriers, `one_code_two_carriers`).
   - D4: "Declared services: reserved names (below `firstFreeName`), carriers conflicting with the
     built-in table, and non-flat carriers are refused at admission; structured carriers wait on
     their own row." This replaces `disagreeingService` (`Api/Author.lean:46-50`), which refuses
     every fresh key today.
   - D5: "Rows extend by append; a published program carries its link table." `Package.install`
     prepends today (`Program/Authoring/Services.lean:186-187`).
   - D6: "The host-row protocol entry requires the row's domain bit" (`asyncPre`'s external arm,
     `Laws/Program/Typed/Residual.lean`; `typedProg_not_table_monotone`).

   For each: is the recommendation sound, is it the cheapest sound option, and what does it
   break? For D4, check the reserved range against the machine's keys. For D5, say what changes
   if `install` appends: which fixtures, goldens or corpus entries move. For D6, say whether the
   bit is needed for M6's command proofs or only for the extension lemmas.
3. **The Σ_app slice** (§5.2): `ProgramSource` gains services (about 9 declarations); the world
   gains the service table (13–17); D4's rules replace `disagreeingService`; D6's bit; the
   extension lemma family from `2026-09-30-model-probe/TREE/R2Probe.lean` (about 30 declarations)
   with its red controls; row 21 corrected. Claimed: about 22–26 restated declarations, after G
   and before the M5–M7 proofs; `MeaningSound`, `LoopSound` and `TypedRun` need no restatement.
   Recount, and say what the slice does to the M6 ledger statements and to item E's
   `ServicesFit`.
4. **R2 as eight conservativity conditions C1–C8** (§2.2). Are they complete, and is each status
   (proved, tested, owed) right? Is any condition missing: the faces, the OCaml profile, the
   session? Rerun the probes that carry the proved ones (`pedigree/Conservativity.lean`,
   `pedigree/VerifyConservativity.lean`, `TREE/R2Probe.lean`, `TREE/verify-Probe.lean`).
5. **R10–R13, the added requirements** (§2.2). Are they theorem shapes over the model, with their
   observation named, and not capability lists? Is there anything in the stateful catalogue, the
   dogfood findings or the counterexample register that none of R1–R13 covers?
6. **The basis refresh** (§3.2 corrections; §3.3 and §4 the plan). Is any pedigree correction
   itself wrong? Would any step of the refresh create a second owner of a fact (AGENTS.md:
   "If two files appear to own the same fact, stop")?

**Rules.**
- Read-only on both checkouts: no source, test, register or generated file changes; no `lake
  build`, no `make`, no generator. Probes compile with `lake env lean -DwarningAsError=true` in
  your worktree only, one at a time.
- Write under `docs/research/2026-09-30-codex-review-model-probe/` in your worktree: `audit.md`
  with the one thing first, then one section per part above, each claim with an evidence word
  (proved, tested, reading, assumed) and its probe or line; `probes/` and `logs/` beside it; a
  `verify.py` or an equivalent list of exact commands. Commit by explicit paths (force-add) on
  `codex/slice6-fixes`; no push.
- For every claim you refute or amend, the smallest amendment to the plan, and which ruling it
  touches.
- Name what you could not settle.

**Not in scope.** Implementing anything from the synthesis; the A, C, F, G and H1 queue of
addendum 4, which resumes after this review unless the owner says otherwise.
