# Landing observation, 2026-10-01 18:15 UTC

**Meaningful resolution:** the scope-allocation counterexample is repaired on unmerged seat I2 at `f98edd9e37feca39474faa299f7271742d6910e7`. **One handoff issue:** the newly dispatched Schema probe still points to the initial scouting review and describes defects already repaired in revisions 2–5. Its input packet should include the latest accepted prototype and review before it repeats that work.

Main changed from `a2c2cb27` to `bff5063174b0aaea261659c6a4cb1fb3629a0d9d`, and is clean. Seat I2 moved from `d5f6a0fe` to `f98edd9e`; seat G's code and receipt are now merged on main. I2's receipt is still being finalized. This review pins committed code; its receipt snapshot is separately labeled as a working file. No active repository/worktree edits, branch moves, UI operations, messages to Claude seats, compilation, generators or installations were performed.

## Scope repair reviewed

The repair addresses both pieces of the original finding:

- `World.ScopeLive` means an entry exists, whether open or closed. Its transport lemma reads the existing world order's scope component.
- Membership at `Ty.scope` now requires this presence. Membership transport, environments and the inhabitance construction carry it; the latter allocates a scope rather than inventing a dangling handle.
- The five scope-answering posts now use that membership. Actual store-operation proofs establish it for make/fork/build, while memo release reads a memo-validity field supplied by the existing machine invariant. Ambient-scope presence is derived from the typed context; the former extra `MachineLive` field is removed.
- `TypedProg.scopeExit` also requires presence, closing the previously documented bypass of the protocol precondition.

The current [ScopePresence battery](/Users/pooks/Dev/lean4-effect4-seat-I2/Test/Counterexamples/Machine/Semantics/ScopePresence.lean:328) types allocation followed by close and the original checked allocation/fork source. `forkAfterMake_typed` uses the concrete `seq_typed` algebra law and transports the returned scope into the later world. `forkAfterMake_denotes` (`:399`) proves the denotation proposition at that source's root point. It does not assume the missing typing result as a premise. The earlier post/typing counterexamples are retained against named historical definitions.

The receipt reports successful narrow and final builds with allowed axiom output. I inspected the statements, proof bodies and receipt, but did not independently rerun its compiler or gates this tick. This supports retiring the specific counterexample upon integration; it does not close general M5, command preservation or M7. `step_deliver` is explicitly still open, and the broader unchecked-handle issue at `unknown` remains documented. The M7 empty-table restriction and normalized `Ty.subN` comparisons are retained.

## Schema handoff is behind the reviewed prototype

Main's [brief S](/Users/pooks/Dev/lean4-effect4/docs/research/2026-10-01-type-language-probe/brief-S.md:7) names the initial root-level review files and `SchemaExprProbe.reviewed.lean`. Its description at lines 26–29 still says the prototype changes accepted inputs and lacks located refusals and asserting controls. The README likewise lists the first review packet.

The [revision-5 review](/private/tmp/codex-schema-scout-review-2026-10-01/revision-5/review.md) now accepts the narrow readable profile for briefing, with fixed checks/duplicates, constructive ordering, a tested annotation allowlist, and explicit remaining proof obligations. The brief's literal “preserved or refused ... never dropped” annotation rule also needs reconciliation with the reviewed policy of erasing explicitly allowlisted documentation metadata under the named observation.

This is an evidence/handoff gap, not a newly found implementation defect. Add revision 5's report, `DefinitiveSchemaProbe.lean`, `ConstructiveProjectionProbe.lean` and results to S's inputs. Its genuinely new work—per-form expansion, maps, broader target comparison and deduplication measurements—can then build on those results. There is no need to restart the reviewed slice or interfere with the active seat.

## Retained evidence and next check

[Pinned source and working-receipt manifest](1815-evidence/manifest.json); [independent control review](1815-controls-review.md). The original review and counterexample remain unchanged as historical evidence at `509d243c`. Next check: I2 integration and its recorded scope repair, and whether the type-language synthesis incorporates revision 5's boundaries rather than the first scouting status. The campaign continues; monitoring remains active.

Final metadata check: main advanced to `674ce1612f935cb61d694491708cd7b2df67c14b` with only a STATE update naming the type-language probe. I2 added its receipt at `71dd425f0e652a96df97cc8930966e31ad531acd`; its code is unchanged from the reviewed `f98edd9e`, and it is still unmerged. The [committed receipt](1815-evidence/receipt-I2-committed.md) is retained separately.
