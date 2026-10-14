# Version 5 consumer review

Reviewed checkout: 7c9bb76172400d2f885cf461f2f09db334d2495a.
Reviewed proposal: /Users/pooks/.codex/attachments/ed50469e-edc3-42f1-be47-79990dda7e66/Pasted text.txt.
No source or authority edits. No Lake invocation in this review.

F3 design status: resolves the immediate shared-recorder lifetime defect for Stage 5 by explicitly retaining the current per-request lifetime. The proposed shared proxy and persistent replay contract cover the two necessary future changes; they are deferred, not current blockers. Startup construction must not be represented as an implementation-ready change within Stage 5.

Remaining amendments:

1. Replace `runOf, checkSession and H9Blocks cover directly` with prospective wording. Tools.RunChecks.runOf/checkSession are real single-request machinery. apps/todo/Check.lean build still calls Todo.builtAt; Todo.builtAt builds application.moduleOf, whose main is the bare applied entry. H9Blocks is a proposed future declaration. Stage 5 must wire a cached service consumer builder before claiming that existing replay runs that program.
2. Distinguish the TypeScript composite cachedListAfterAdd from the Lean listAddList and theorem cached_list_after_add. The TypeScript program lists twice, writes, lists. Cached.listAddList lists, writes, lists: it checks invalidation but not a repeated cache-hit branch. The theorem proves add-then-list at block meaning under the model from arbitrary cache content, and explicitly leaves machine replay agreement open. harness/truth/service/run-todo.ts does not select cachedListAfterAdd; scripts/check-host-protocol.py does not name it. Add a matching composite to the behavior gate with exact expected host-call sequence and retain the existing deliberately broken cache control.
3. Keep ContextFreeTy restricted to the external RowTable columns used by reply admission. Actual todo.table.json has four concrete external rows with no typeArgs. Answers are record Todo, list Todo, option Todo, bool; errors are prod(lit SqlError,string). They pass the proposed filter. The native Ref row templates contain type variables, but they belong to the native operation signature, not this external table. Broadening the all-row filter to native signatures would wrongly exclude this cache.

Finite checks:

    bun /tmp/proc6-v5-review/consumer-build/consumer-probe.ts
    python3 /tmp/proc6-v5-review/consumer-build/table-probe.py

Both exit 0. Runtime Bun 1.4.2 / Effect 4.0.0-rc.112. consumer-probe uses the current consumer source with only import paths adapted in a scratch copy. It imports the prior isolated fresh emission from the same HEAD; producer hash and emitted hash remain identical. Output: first empty list, cache-hit empty list, inserted tea item, final list with tea. Repository calls exactly [all, insert, all]. This tests the actual TypeScript composite but is not a Lean agreement proof.

Relevant SHA256:
EmitTodo.lean: 54f7e3720d4ce94da23f5a84d545ac6ff83dda6457fbe4544199be51f1d4c02d.
consumer.ts: e9af7f78650fe0d4ebcdcf6e8a30a6ddb28396adaace53abaacb87de20f4a9a8.
Fresh emission: 2116bb8d490a772c79431fe5df03bf5a9f359b673706da5af952a0cb8ceef409.

The table probe implements only the constructors present in this concrete table and fails on unexpected ones. It demonstrates that the intended filter admits this table; it does not prove the proposed recursive filter theorem.

## F1 source check: defect payload accessibility

The proposed fully recursive BudgetSafeVal lemma is stronger than current admission warrants: admitted die defects may retain arbitrary handle-free payload values. A poisoned context under that payload refutes recursive byte-tree safety, even if no current program operation can expose it.

Source inspection finds no current defect-payload extraction primitive:

- Machine.Term.firstFailure?, firstErrorValue? and queryError select Reason.error?. Machine.Cause.Reason.error? returns none for die and interrupt.
- NativeAtom.causeIsDie and other cause tests return only Bool. Machine.Term.NativeAtom.eval has no causeDefect or squash atom.
- Machine.Term.evalTerm exposes lists, records, tuple positions, and supported atoms. fst/snd and tupleAt inspect plain .list. Val.asList? accepts plain lists or fiber snapshots. None reads arbitrary .ctor children.
- Machine.Record.recordParts? requires ctor0 [list names,list values]. A failed exit is ctor1 [cause], so record field reads cannot open it. The underlying Val has separate none and some constructors; Decision.option is not a generic ctor1 projection.
- Program.Compile.contEOf caught/onCause append the whole Val.exitErr cause. caughtError uses firstErrorValue? and therefore only Fail payloads. orDieCause promotes the first Fail to Die; it provides no reverse path.
- Program.Compile.exitOfVal decodes an exit to rerun success/failure behavior, preserving the cause. It does not emit a Die payload as success.

Therefore an accessibility invariant that treats Die payloads as opaque is plausible for this fragment, but NOT proved by this review. Needed obligations include: closure of evalTerm and every accepted Decision under the safe accessible-value relation; closure of cause/exit reification and decoding; first-Fail extraction preserves accessible safety; all fragment native operations preserve it in stores and replies; catch/exit/onExit and context operations preserve it; program parameters and stores do not offer an alternate generic destructor. The theorem must use this weaker predicate, not keep the recursive predicate and cite opacity informally.

Concrete Todo scope: its four external answer types are record/list/option/bool, and the common error is prod(lit SqlError,string). They contain no exitOf or causeOf. Its list/add/complete/remove programs do not need arbitrary cause payload extraction. Actual row failures can still carry Die defects, so a recursive safety predicate over every byte of the whole failure remains too strong even here. A narrowly typed accessible-payload predicate could ignore defect internals without globally changing Admit.lean, provided the closure lemmas above land with it.

For future external exitOf/causeOf columns, the same opacity argument must cover nested safe Fail payloads and success values recursively, while exempting Die internals only behind the cause/exit views. Adding a defect getter or generic constructor destructor later invalidates that exclusion and must reopen the invariant.
