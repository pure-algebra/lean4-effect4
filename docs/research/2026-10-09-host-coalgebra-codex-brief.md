# 2026-10-09 Brief for Codex: review and break the coalgebra layer and H9

Status: a brief (history, not authority). Base: the head of `refactor/phase1-phase3` that carries
this file, and branch `coalgebra` of `~/Dev/lean4-effects` (commits `8ddb936`, `b0dd607`,
`e6028a4` and `24a91a1`, local). The last two add typed handlers (v0.9.1) and indexed signatures
(v0.10.0); Effect4 still pins `b0dd607`.
The plan under review: `docs/research/2026-10-09-host-coalgebra.md`.

## 1. The one thing to know first

The owner asked for host handling that composes, by the algebra's dual. The generic layer landed
in `Effects` 0.9.0 (systems, bisimulations, hosts as comodels, protocols, runs). Effect4's local
run with calls now asks a host where it read a reply tape, and H9 is a theorem. The package's
rules want a breaker in a separate process before a release. You are that breaker. Change no file
under `src/`, `tools/` or the `Effects` library; write probes and a receipt.

## 2. What to review and break

1. **The `Effects` packet** (`test/contracts/coalgebra.contract.md` in `lean4-effects`). Attack
   each ENSURES line with a falsifier. Check that the claim boundary says no more than the
   theorems give. Check the four counterexample rows.
2. **The comodel constructions.** Probe `route`, `share`, `rename`, `through`, `guard`,
   `replies`, `record` on carriers of your choice. Is `run_record_replies`'s round-trip premise the
   right one? Is a host into another monad than `Option` worth a law now?
3. **The gate's walk in `Effects`** (`EffectsTest/Audit/Axioms.lean`). Confirm that it matches
   lean4-effect4's walk, and that the admission of its module is as narrow as stated.
4. **CO-4 in Effect4.** `localStepC` asks `hostAnswer host` at a call; a row outside the table is
   no answer. Check that H8 kept its statement and that its new route (`tape_holds`,
   `meaning_settled_tape`, `preflight_row`, `Holds.tapeAnswer`) has no gap.
5. **H9** (`denoteRows_eq_session_host`, `src/Effect4/Laws/Api/SessionMeaning.lean`). Attack the
   premise `HostAnswered`: is it the right reading of "the host gave the run's answers"? Probe
   three runs. In the first, a reply is refused. In the second, a host answers outside the row's
   columns. The third ends at a waiting call. Check `hostAnsweredCheck_sound`.
6. **The typed and indexed layers** (`Effects/Coalgebra/Sat.lean`, `Indexed.lean`). Attack
   ENSURES 8 to 14. Is `Program.Sat` the right typing, given that it is not complete for runs?
   Does the one-world embedding lose anything? Is a host state indexed by the world needed?
7. **H9 at the driver** (`src/Effect4/Laws/Api/HostDrive.lean`). Attack `Reactor.guardRows`,
   `Reactor.ofHost` and `reactorHost_ofHost`. Check the premise of distinct keys against
   `Table.lawful`.
8. **What H9 does not reach.** The drive lemma says that `Run.drive` with a reactor makes its run
   `HostAnswered`. Say what it needs. Say whether a finished one-fiber run can hold a refused
   reply.

## 3. The receipt

Write it under `docs/research/2026-10-09-host-coalgebra-review/`. Give each finding an id, its
evidence kind, its probe and the smallest next action. Record the commands and their results.
Read axioms with the exact walk (`ProofGraph.exactAxioms`), not with `#print axioms`.
