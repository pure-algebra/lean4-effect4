# Receipt: seats READ, IMPOSE and APP wound down, their last work landed by the coordinator (2026-10-13)

Status: receipt (history, not authority). The owner stopped the seats over build contention and
asked the coordinator to land their work. Gemini's round 2 runs on.

## The one thing to know before merging

The landing adds a field to the typing `Signature` (`keyNames`, `src/Effect4/Program/Typing/Rules.lean`).
Every worktree that merges it rebuilds the core once. Typing reads none of the field.

## What landed

- **READ, item 3: keys by name** (row 378 (19), (22)). A call row whose spelling is `Ns.method`,
  with one requirement key, names that key `Ns` (`Row.keyNamespace?`, `rowKeyNames`,
  `src/Effect4/Program/Native.lean`). The native signature carries the names
  (`Signature.keyNames`). A key's one spelling is `keySpelling` (`src/Effect4/Codegen/Types.lean`):
  its name, else its runtime text. The printers, both Lean readers and `Context.Context<R>` read
  it there. `KeyNames.nameOf` keeps only names that invert, so the readers stay exact
  (`keyOfSpelling_keySpelling`, `keySpelling_injective`, `src/Effect4/Laws/Codegen/ReadLeaf.lean`).
  The to-do's file now reads `Effect.Effect<…, "TodoRepo">` and `Context.Service<"TodoRepo", …>`.
- **IMPOSE, HO-5** (row 340). A service method whose definition takes programs takes them after
  its arguments, and passes them on (`methodType`, `methodClosure`,
  `src/Effect4/Codegen/Print.lean`). The Lean and TypeScript readers read the closure back, and
  the arity is the parameters less the programs (`readServiceMethods_ok`,
  `src/Effect4/Laws/Codegen/Services.lean`). An initial program that takes a program stays
  refused. The cache block now prints as the service `ListCache`.
- **APP, item 4: the gate** (row 378 (16)). `make check-host-protocol` runs the to-do on SQLite.
  It runs four repositories: the shipped one, `forgetful`, `titleless` and a read-only one. It
  also runs three changed copies of the shipped session. Lean checks every request
  (`apps/todo/Check.lean`). The front reads its arguments with the wire's own readers
  (`apps/todo/server.ts`).
- **The coordinator's fixes in the merge.** The service printer passes the key names
  (`methodType`, `methodClosure`), or a block service's shape would spell `R` apart from its
  definitions. Two law call sites name their signature or pass the names
  (`readModule_printModule_defs`'s use of `readDefs_printDefs`, `printModule_readable`). Two
  batteries pass the new argument (`Test/Codegen/TypeReader.lean`, `Test/Codegen/DefinitionsPrint.lean`).

Base `d59b95676`. The seats' saved work is on branches `wip/read` (`fcdcfe274`),
`wip/impose` (`d5c96e912`) and `wip/app` (`ae852a4f5`), none of them built when saved.

## Commands and results

| Command | Result |
| --- | --- |
| `lean-slot.sh lake build Effect4 Effect4.Laws` and the touched batteries (`Test.Codegen.{ReadContract,DefinitionsPrint,TypeReader}`, `Test.Schema.DialectContract`, `Test.Dogfood.Scenario.{TodoFile,TodoService}`, `Test.Dogfood.Bank`, `ProofGraph.Registry`) | green after the fixes above |
| `#axiom_audit` over the 21 touched modules | 6228 declarations within `[propext, Quot.sound]`, 0 modulo planned goals |
| `make check-host-protocol` | PASS. The to-do's service: 13 scripts on rc.112, 2 red controls. SQLite: 11 requests from an empty database each pass Lean's five checks; forgetful and titleless fail `agrees` and `conforming`; 8 writes that SQLite refused escape as the row's error; 3 changed records fail `built`, `replayed`, `exit` |
| `make check-ts-reader` | `files 501: matched 416, mismatched 0`; 780 pass, 0 fail. The corpus does not move |
| `make check-target` | conformance 104 of 104; assignability PASS; rows PASS |

Versions: effect 4.0.0-rc.112, bun 1.4.2, tsgo 7.0.0-dev.20260629.1 (`ts/eff`).

## Open obligations

- The TypeScript reader reads a key by its runtime text alone (`readKey`, `ts/eff/read.ts`). A
  module whose rows name a key, such as the to-do's file, is read back by Lean alone.
- The cache block's module does not read back: the header reader reads no `Ref.Ref<…>` column.
- IMPOSE's item 4 remains: the to-do imposes the cache, its file prints, and the host-protocol
  gate runs again.
- READ's two collision gaps remain: `rowNameUses` (`src/Effect4/Codegen/Print.lean`) leaves out
  the generated `NsKey` names, and a plain row `Ns.x.y` beside a service `Ns` is not refused.

## Bounded evidence

The SQLite run is one script of 14 requests, on one machine. Concurrency between requests is not
checked. Nothing here says how rc.112 behaves beyond the recorded completions.
