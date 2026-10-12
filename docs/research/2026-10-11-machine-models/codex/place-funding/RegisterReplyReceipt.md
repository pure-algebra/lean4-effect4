# Actual asynchronous reply producer

Both source counting and Atomic writer reservations read one native terminal-reply proof.
The original source-counting statement remains unchanged.

## Placement

1. Concept: scope-lifetime-finalization R11, serving the original source-use and Atomic log debit endpoints.
2. Question: register_reply states the actual reply shape; register_reply_zero is its existing numeric consumer.
3. Reach: any actual successful immediate registerAsync result, arbitrary store and completed-exit view, and the existing native interpreter.
4. Limits: the reply shape proves no state bound, callback funding, source ownership, history, or host agreement.
5. Unlock: source and writer primitive accounting share the actual producer instead of repeating its registerAwait branches.

## Changes and evidence

Base: cbc338533. Source head: bfd3778e3.
NativeConfiguration adds register_reply beside completion_reply.
SourceOpportunityPrimitive retains register_reply_zero as the scalar adapter.
The source diff adds 23 lines and removes 14 lines.
The old register_reply_zero statement is unchanged.
No original scenario statement or runtime behavior changes.

```sh
LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.SourceOpportunityPrimitive Test.Dogfood.Scenario.Atomic.WriterMachine
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true /private/tmp/MachineRegisterReplyReader.lean
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true /private/tmp/MachineRegisterReplyAudit.lean
```

The narrow build passes 1155 jobs.
The real source and Atomic scalar readers pass without diagnostics.
The audit passes 214 declarations within [propext, Quot.sound], with zero planned and zero modulo declarations.
The whitespace check passes.
Atomic.Cleanup.log_debits remains open.
