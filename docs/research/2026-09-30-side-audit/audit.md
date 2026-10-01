# Side audit of the next Effect4 slices

The proposed order can stand, but item H needs stronger command and intermediate-code contracts and item G needs an explicit fixture migration. The future numbers proposal also has two demonstrated omissions. These findings supplement Claude's design pass; they do not implement or widen its brief.

Reviewed from `bbdbb7acb6cf0881e43ad47500b0809ef9dd71f0` through the newly published addendum 2 at `0f16828aba1d6d811701286b204c79218f73fb3b`. The intervening changes were documentation only. No repository files were edited, no builds or generators ran in either implementation checkout, and no message was sent to Claude. Tests ran from an isolated copy of the existing compiled Lean libraries and separate scratch files. This is a focused audit, not a whole-tree build or coverage report.

## 1. Item H: token freshness leaves the command statement false

**Confirmed by Lean.** A checked program `succeed(unit)` has a proved typed initial state. Its queue may nevertheless contain `finish root (success 42)`: the handwritten queue predicate checks resumes and accepts every other command. Executing that command records a number as the result of the unit-typed root. No world can type the resulting machine at the stated root type.

The probe also states the exact proposed token-strengthened step rule from the lift verifier. The initial machine has no internal keys, the finish command has no resume key, and both new freshness premises hold. Lean refutes that strengthened rule too. This is a counterexample to the all-states command obligation, not a claim that the public API lets a user inject this command.

The source of the omission is [QueueOk](/Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Assembly.lean:87). The project already generates exit checks for `finish` and `observe` ([command source table](/Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typed/Sources.lean:63)). The probe proves that the generated `RCmdOk` rejects this exact bad command.

**Smallest amendment:** carry the generated command checks into the queue premise, alongside freshness. Then inspect the control commands' state conditions: checking exit payloads alone does not establish that commands such as `afterInterrupt`, `closeParAwait`, or `exitDone` are valid at the supplied state. Prove the commands actually emitted by each step meet the strengthened predicate. Do not dispatch the 18 command proofs on the present statement.

Evidence: [TokenFinish.lean](/Users/pooks/.codex/visualizations/2026/10/01/01a0f4f6-17d1-7860-a620-1505f12298c0/effect4-side-audit/probes/TokenFinish.lean), especially `loaded_typed`, `proposed_step_finish_false`, and `bad_generated_command_rejected`. All printed theorem dependencies are within `[propext, Quot.sound]`. The proposed `Fits` change does not alter the scalar mismatch between unit and a number; this probe does not claim to compile the entire future E/H implementation.

## 2. Item H: checking final exits alone does not constrain intermediate code

**Confirmed by Lean on a constructed state.** The proposed exit field refuses `badName`, but the current-code judgment still admits a pure computation that returns that defect. A state with such current code and no published exit satisfies the strengthened state predicate. Its internal keys and evaluation queue meet the proposed freshness rules, and the generated command check admits evaluation. Normal evaluation of that state then records the forbidden defect. Even adopting the generated command predicate exposes the issue one step earlier: `loop` emits a finish command that the stronger predicate rejects.

The witness uses the source `succeed(unit)` as its independently checked root, but deliberately constructs its intermediate code. It is not claimed reachable from that root. The planned step theorem quantifies over all states admitted by the invariant, which is why this fabricated state is decisive for that statement.

**Amend H before proof dispatch:** carry the separate no-malformed-failure guarantee through the current-code judgment and its continuation/postcondition contracts, then through saved stacks and queued results. Strengthening only `preds.exit` cannot make the proposed state property survive steps. The `Fits` migration alone will not provide this guarantee: its cause rule deliberately admits all defects (`membership/Walk.lean`, `fitsExit_of_clean`); that observation is source inspection, not a compiled future H implementation.

Evidence: [BadDefectCurrent.lean](/Users/pooks/.codex/visualizations/2026/10/01/01a0f4f6-17d1-7860-a620-1505f12298c0/effect4-side-audit/probes/BadDefectCurrent.lean), `strengthened_input`, `strengthened_output_false`, and `produced_queue_refused`. This retains the intended all-states proof scope; it does not recommend silently weakening the theorem to reachable states.

## 3. Item G: an existing regression would pass after losing its meaning

**Confirmed by finite checks and the proposed new leaf rule.** [leftWins and rightWins](/Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Provision.lean:607) put natural-number values under `dbKey`, whose declared service type is `handle "Db"`. G's new check rejects those leaves. Their typing regression currently asserts only that the two checker results are equal ([E4-PROV-CE-002 typing check](/Users/pooks/Dev/lean4-effect4/Test/Program/ProvisionContract.lean:98)). After G, it can remain green as `none = none`, while no longer demonstrating two admitted layers with the same signature and different results.

**Smallest amendment:** include `Provision.lean` and `ProvisionContract.lean` in G's fixture work, move these two examples to the existing nat-typed `dbBinding`, update the expected context keys, and require an affirmative successful typing result. The replacement pair was checked to retain the two different outputs. This should be named before dispatch because [G's stop rule](/Users/pooks/Dev/lean4-effect4/docs/research/2026-09-30-codex-brief-slice6-addendum-2.md:243) stops on newly refused examples beyond the listed gap programs.

Evidence: [ProvisionProbe.lean](/Users/pooks/.codex/visualizations/2026/10/01/01a0f4f6-17d1-7860-a620-1505f12298c0/effect4-side-audit/probes/ProvisionProbe.lean). This tests the exact proposed subtype checks and replacement examples; it does not apply the future checker patch.

## 4. Future numbers slice: mutable-cell updates bypass the three checked atoms

**Demonstrated on Lean and the printed TypeScript.** The numeric proposal checks `add`, `succ`, and `mul`. The separate `incr`, `double`, and `takeAndBump` functions also do arithmetic, including within Ref updates ([TypeScript functions](/Users/pooks/Dev/lean4-effect4/harness/truth/prelude.ts:82); [Lean store functions](/Users/pooks/Dev/lean4-effect4/src/Effect4/Machine/Stores.lean:852)).

A checked, printable program creates a cell holding `9007199254740991`, increments it twice, and compares the two returned values. Lean returns `false`; the exact printed TypeScript returns `true`. Every source literal is within the proposed limit, and the program uses none of the three arithmetic atoms. Under the intended target profile, it should refuse when the first update exceeds the limit.

**Amend row 108's plan when it is scheduled:** include store functions and stored values in the arithmetic inventory and invariant. The 31 term-evaluator call sites are not the full arithmetic boundary.

## 5. Future numbers slice: a program can catch and hide the refusal

**Demonstrated with the proposed checked addition and the existing `ProfileRefusal` class.** An uncaught overflow produces the expected defect. Wrapping the same operation in `catchCause` produces a successful `7`; wrapping it in `exit` and discarding that result also produces `7`. The checker accepts and printer emits the catch example. A harness that examines only the final defect never sees the consumed refusal.

**Amend the plan:** retain refusal independently of the program's result and let it take precedence, including after a competing fiber succeeds. The [existing clock boundary](/Users/pooks/Dev/lean4-effect4/harness/truth/session/clock.ts:44) already demonstrates this separation. Merely choosing a distinct exception class is insufficient.

Evidence for both numeric findings: [RefUpdates.lean](/Users/pooks/.codex/visualizations/2026/10/01/01a0f4f6-17d1-7860-a620-1505f12298c0/effect4-side-audit/probes/RefUpdates.lean), [host probe](/Users/pooks/.codex/visualizations/2026/10/01/01a0f4f6-17d1-7860-a620-1505f12298c0/effect4-side-audit/probes/refusal-probe.ts), and [host results](/Users/pooks/.codex/visualizations/2026/10/01/01a0f4f6-17d1-7860-a620-1505f12298c0/effect4-side-audit/logs/numeric-host.log). The exact printer expressions are replayed. The checked-add wrapper simulates the proposed change; it is not a production edit. No OCaml result is claimed. Addendum 2 explicitly leaves numbers outside its scope, so these are future-plan findings, not additional work silently added to E–H.

## Questions closed and controls added

- **Pending tokens already have the bound.** `pending_below` in `TokenFinish.lean` proves it for every typed state from the generated pending clause and `WorldValid.tokenBound`. H need not add a separate bound for these tokens. Their owner and payload correlations are separate questions.
- **The layer reset has useful passing controls.** For both local settings, the caller's continuation retains its outer variable and the layer retains its required service context. These test the latest brief's intended separation; the future runtime fix itself was not applied.
- **The lane's original impact detector omits unknown service keys.** A supplemental scan found zero such leaves among currently typed lane programs. Thus there is no observed extra lane regression from that omission. Retain the broader scan as G's evidence. Both checks are in [LayerControls.lean](/Users/pooks/.codex/visualizations/2026/10/01/01a0f4f6-17d1-7860-a620-1505f12298c0/effect4-side-audit/probes/LayerControls.lean).
- **Handle-free values alone do not justify an unrestricted runtime-to-Fits lemma.** A context containing a string under a nat service key has no handles and passes the coarse shape check, but fails `Fits` in every world. Lean proves this in [ContextBridge.lean](/Users/pooks/.codex/visualizations/2026/10/01/01a0f4f6-17d1-7860-a620-1505f12298c0/effect4-side-audit/probes/ContextBridge.lean). Item A's table rule excludes the context type, so this is not a bypass of that admitted profile. Any future bridge must carry the type-profile premise or validate context services. The latest addendum correctly parks the full runtime twin.

## Verification and limits

Run [verify.py](/Users/pooks/.codex/visualizations/2026/10/01/01a0f4f6-17d1-7860-a620-1505f12298c0/effect4-side-audit/verify.py) with Python 3. It checks the reviewed source hashes, serializes standalone Lean runs, checks printed dependencies for forbidden axioms, and reruns the pinned local Effect host examples. It uses the isolated compiled-library snapshot while present, or the repository's existing compiled libraries otherwise; it never invokes Lake or a generator.

[verification.json](/Users/pooks/.codex/visualizations/2026/10/01/01a0f4f6-17d1-7860-a620-1505f12298c0/effect4-side-audit/verification.json) records every exact command and exit result. [manifest.json](/Users/pooks/.codex/visualizations/2026/10/01/01a0f4f6-17d1-7860-a620-1505f12298c0/effect4-side-audit/manifest.json) records source hashes, the review commits and toolchain. The probes concern particular statement defects and finite host examples. They establish neither M5–M7 nor the complete future repairs.
