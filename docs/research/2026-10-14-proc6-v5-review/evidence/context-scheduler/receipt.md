# V5 F1 bridge review

The proposed recursive type filter does not establish the promised value-safety bridge. A canonical reified exit can carry a poisoned context inside a defect payload, even at the closed type exitOf unit never. An actual checked session admits this reply. The probe does not change the fiber budget, so this is a proof-bridge refutation, not a demonstrated runtime invariant violation.

## Pin and placement

HEAD: 7c9bb76172400d2f885cf461f2f09db334d2495a.
Proposal SHA256: 4156fd33ee16db55ddbf9ebb456439402f0daa5367834df325ab775a9c0f97fa.
Proposal path: /Users/pooks/.codex/attachments/ed50469e-edc3-42f1-be47-79990dda7e66/Pasted text.txt.
Placement: review controls for rows-block-host / translation-simulation / R6. No production theorem or repository edit.

Command:
LEAN_NUM_THREADS=3 lake env lean /tmp/proc6-v5-review/context-scheduler/Bridge.lean
Result: accepted, no errors, against existing oleans. No lake build was run. Log: bridge.log.

## Minimal witness

poison is Ctx.withServices of the singleton service maxOpsKey -> nat 1.
frame is the canonical record {hidden: Val.context poison}.
payload is Payload of frame, with isPayload verified by decide.
defectReason is die (Defect.error (Err.payload payload)), with empty annotations.
defectCause is the singleton cause containing that reason.

The specification's ContextFreeTy accepts both causeOf never and exitOf unit never: their children are never/unit and the filter recurses through causeOf/exitOf.

Finite results:
- Val.hasTy (Val.exitErr defectCause) (causeOf never) = true.
- Val.hasTy (Val.exitErr defectCause) (exitOf unit never) = true.
- A depth-100 inspection of every Store.Val child finds the poisoned context in both values.
- errAdmits never defectReason = true.
- reservedDie defectReason = false.
- frame.handles.isEmpty = true.

The bounded inspector is only a finite diagnostic, not a proposed production traversal or a universal proof. The witness is visibly below its depth limit. The proof-bridge fails because the proposal's recursive BudgetSafeVal must inspect this nested context and reject its reserved service key.

## Actual checked reply

The witness row is closed, async/external, request unit, answer exitOf unit never and error never. Its program is perform external0 unit.

The probe observes:
- admitSig = ok ().
- admitProgram.isOk = true.
- externalValue accepts success value Val.exitErr defectCause.
- Api.Author.Internal.finishBuild succeeds.
- Run.open/control evaluate followed by Run.answer produces no outstanding call, a completed successful value with the poisoned descendant, and fiber maxOpsBeforeYield 2048.

Final output: some (0, true, [2048]).

Thus no polymorphism, unknown, explicit context column, untyped program or malformed encoding is needed. The context is hidden inside a permitted defect. The scheduler budget remains at its default because the program merely returns the value.

## Decisive source

- Machine/Alphabets.lean Payload: a handle-free record, not a context-free record.
- Machine/Alphabets.lean Defect.error: stores an Err.
- Machine/Alphabets.lean Err.payload: stores Payload.val.
- Machine/Alphabets.lean Val.exitErr and Val.cause?: the canonical reified cause frame.
- Program/ErrorImage.lean reasonAdmits: die and interrupt return true for every error type.
- Program/Typed.lean Val.hasTy exitOf and causeOf: read the cause and apply causeAdmits.
- Program/Typed.lean reservedDefect: error payloads are not reserved defects.
- Program/Admit.lean admitAnswer: this reply passes externalValue and mintedIn.

The proposal's statement that die carries no Val is false. Interrupt carries only identity/annotations, and Ann is Unit, so that arm causes no similar issue.

## Other inspected cases and controls

The record checker consumes all value names and fields. Four finite controls reject: extra field at empty record type, wrong declared field type, extra named field, and unequal column lengths. There is no width-subtyping leak in namedHasTy.

Scalars match exact carrier shapes. Option/prod/list/except/tuple/map inspect their typed members; list's snapshot special case decodes only fiber handles. Union accepts one branch. Handle/app non-context names accept only their designated handle/saved-mask shapes; the handle tag is a distinct Store.Val constructor, so a context ctor cannot collide with it. Saved-mask frames contain only Bool. Nominal app arguments are unread by membership; the finite control confirms a Foreign handle fits app Foreign [unknown]. A no-type-variable claim must explicitly traverse app argument data if syntactic equality after instantiate is required, even though those arguments are irrelevant to value membership. The parent separately checks call-instance normalization.

The exact proposed filter is under-specified on fiberOf/refOf/deferredOf and app arguments. Define it with the generated Ty algebra and an explicit field per constructor before stating its bridge. These omissions are secondary to the established defect counterexample.

## Smallest sound corrections

1. Correct BudgetSafeReason to inspect die (error (payload p)) recursively, as well as fail payloads. Make BudgetSafeExit agree with the full recursive value definition.
2. A type-only reason bridge remains impossible: reasonAdmits admits that die reason at every error type, regardless of ContextFreeTy. Even rejecting causeOf and exitOf in answer types cannot control an outer host failure carrying the same defect.
3. If retaining the default-budget approach, require a semantic safety check/condition on actual applied reply exits, including nested reified causes and defect payloads. Connect that condition to the checked session's actual reply protocol. The existing admission check does not imply it.
4. Alternatively retain general contexts and scheduler stuttering in the machine relation; this avoids a new host restriction. Neither route requires changing local block meaning to a default-only context.
5. If a strictly type-derived success-value bridge is still desired, reject causeOf and exitOf unless membership is supplemented by a value check; ordinary recursion through their children is insufficient. This alone does not repair outer failures.

No exact counterexample to H9Blocks, typing preservation or the runtime default-budget invariant follows from this probe. The exact V5 hasTy-to-BudgetSafeVal bridge is refuted, and its explanation of die payloads is incorrect. A revised safe-reply protocol or broader scheduler relation remains open.
