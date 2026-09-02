# Fork and supervision implementation receipt

Base: `f4f55fae372be373465a9d7049f1c4721073f1ad`.
Independent breaker checkpoint: `5568f00`.
Implementation and assurance join: the commit containing this receipt.

The resumed fork/supervision packet is implemented in
[`Effect4/Concurrency/Supervision.lean`](../Effect4/Concurrency/Supervision.lean).
Its 294 frozen declaration checks and 136 public theorem obligations pass.
The separate binary first-completion race packet is unchanged.

## What this slice establishes

The implementation admits observed fork startup, keeps inherited and
post-start state distinct, registers only live non-daemon children, separates
awaited Exit values from joined effects, records interrupt causes, and connects
child observers to canonical Scope keys. Shared wait controllers consume
actual publications. Race startup is split from registration so that earlier
callbacks can run during a later entrant's immediate execution.

The exact contract remains the breaker's
[`fiber-supervision.contract.md`](../test/contracts/fiber-supervision.contract.md).
The original packet, battery, axiom report, proof DAG, and independent
counterexample module are byte-identical to the breaker checkpoint. No
production theorem statement was weakened to obtain a proof.

The independent production review checked immediate post-world admission,
parent and child allocation ownership, race callback timing, publication
frontiers, and the explicit semantic boundaries. It found no production
correctness issues. The integration review found false acceptance paths for
substituted type rows and renamed graph edges, and an unbound trust-closure
claim. The join now compares exact type allocations, shapes, and edge names
with the frozen DAG, and leaves the trust-receipt binding open.

## Assurance and remaining obligations

[`generated/fiber-assurance.tsv`](../generated/fiber-assurance.tsv) is produced
by the existing Fiber assurance generator. It retains the original
representative's declaration lists and receipts and adds:

- 705 compiler-owned declarations, including 294 authored public names;
- 136 exact public theorem and axiom receipts;
- 27 type/judgment dispositions, 19 exact shapes, and three finite leaves;
- all fifteen counterexamples, `E4-CONC-CE-012` through `E4-CONC-CE-026`.

The public theorem receipts are 31 with no axioms, 74 with `propext`, and 31
with `propext,Quot.sound`. None reaches `Classical.choice`. The independent
counterexamples have eleven axiom-free receipts and four using only
`propext,Quot.sound`. The existing audit module checks metadata; this slice
adds no trust exemption.

The generated `SUPERVISION-PG-RC112` graph closes six local edges: identity,
construction, semantics, laws, counterexamples, and coverage. Representation
is not applicable because this packet introduces no codec or generated target
program. Three edges remain required-open:

| Edge | Remaining obligation |
| --- | --- |
| `BRIDGES` | Interpret actual body execution, context, annotations, dispatch, continuation resumption, publication, and shared scope/race state at the supplied observation boundaries. |
| `TARGETS` | Relate the controller to pinned host execution. The ten finite host cases are evidence, not an interpretation theorem for every program or schedule. |
| `TRUST` | Bind a fresh repository trust-gate receipt to the generated graph. The join checks every local axiom receipt, but a separately executed full trust test is not consumed by the generator and cannot close this edge. |

Runtime coverage joins 136 exact theorem snapshots through 222 tagged witness
uses. Only the intended fifteen rows changed: the fourteen previously absent
rows become partial, and the existing `fork.join` row remains partial. Every
row states its missing source clause. No runtime row is promoted to green by
this slice, and no denominator, source anchor, or pinned source-span digest
changes. The breaker's raceAll census wording corrects the observed early
success and mutable cleanup-set branches without changing the source pin.

## Boundaries that matter to subsequent development

`Fiber.publish` constructs a view of an externally justified publication. It
can overwrite a previously done view and does not establish a one-shot
runtime transition or prove that cleanup ran once. The existing operational
Fiber representative remains the owner of that safety claim.

The parent wait controller retains its local body Exit only along the
successful wait continuation with no intervening parent evaluation. A later
parent interruption can replace that Exit, as CE-025 and the host case show.
An interrupt request is never itself a publication or a cleanup completion.

Immediate execution may extend global allocation, install the shared
middleware, change the parent, or close the scope. Admission checks both the
post-parent and post-child allocation ownership. Scope binding consumes the
post-start state of the same ambient scope.

A race winner records whether its callback-visible live set is empty. The
empty branch can leave a late entrant running; the nonempty branch defers
cleanup and reads the later contents of the same set. Requests and actual
publications remain separate decisions. Result stability is stability of the
first accepted callback result, not a claim that callbacks cease or that a
masked wait must finish.

First-order and host claims remain conditional on the admitted payload
alphabets and their interpretation. A function passed to encode an
interruptor is an operation argument, never stored program syntax.

## Verification

The commands below are run from the repository root. The verification results
are completed before the implementation commit is created.

| Command | Result |
| --- | --- |
| `lake env lean -DmaxErrors=10000 Effect4/Concurrency/Supervision.lean` | PASS; zero diagnostics. |
| `lake build Effect4.Concurrency.Supervision` | PASS. |
| `lake env lean -DmaxErrors=10000 Effect4Test/Concurrency/FiberSupervisionContract.lean` | PASS; all 294 exact checks, zero diagnostics. |
| `lake env lean Effect4Test/Concurrency/FiberSupervisionAxiomReport.lean` | PASS; all 136 receipts within the permitted ceiling. |
| `lake env lean Effect4Test/Counterexamples/Concurrency/FiberSupervision.lean` | PASS; all fifteen independent witnesses. |
| `./scripts/check-fiber-assurance.sh` | PASS; fresh declaration, shape, axiom, and graph joins match the generated projection. Also rerun by the reaction test below. |
| `./scripts/test-fiber-assurance-gate.sh` | PASS; all six original defects and four supervision defects rejected; the unmodified shape control passes. |
| `./scripts/check-fiber-supervision-host.sh` | PASS; pinned package bytes, compiler positive/negative/restored controls, diagnostics coverage, and all ten finite cases. |
| `./scripts/test-trust-gate.sh` | PASS; the unmodified and restored probe copy pass, planted unsafe/partial/unadmitted-choice declarations fail, and tokenizer/equality/admission controls pass. Only the two separately declared red modules are excluded. |
| `./scripts/check-effect-runtime-census.sh` | PASS; pinned census bytes, row identities and kinds, exact statements, and axiom receipts agree. |
| `lake build` | FAIL only for the already declared `Effect4Test.Protocol.ByteParserContract`, `Effect4Test.Concurrency.RaceRepresentativeContract`, and consequential `Effect4Test` root closure check. |
| `./scripts/check-internal-citations.sh` and `git diff --check` | PASS. |

The final census check exposed an existing name extractor that skipped the
three frozen theorem names containing `?`. Its accepted identifier character
class now includes that character; the exact ordered comparison is unchanged.
No contract, theorem name, or statement was changed to accommodate the gate.
Independent review compared the extracted names with fresh Lean output and
confirmed that removing any of the three affected statements still causes
rejection.

The host gate pins the complete installed Effect package, compares the
vendored source bytes, checks the actual harness with TypeScript 7.0.2, rejects
an intentional type error, accepts restoration, and checks the diagnostics
provider examined the file. It then runs the ten deterministic finite cases.
No timing delay or fairness assumption determines their expected results.

The full package is not described as green while the independently owned
byte-parser and binary race packets remain red. The trust self-test checks
that the declared red set matches actual failures, then removes those modules
only in its temporary probe copy. It does not establish compiled trust for
those excluded modules.

## File fence and continuation

The only changed library module is `Effect4/Concurrency/Supervision.lean`.
The original Fiber, Interrupt, Scheduler, binary Race, Scope, Cause, and Exit
sources and the earlier frozen representative packets remain unchanged.
Existing README edits and `.claude/launch.json` are outside this work and
excluded from its commits. The completed reification skill pack is committed
separately at the user's request in `d25cd82`. No push or PC synchronization
is part of this continuation.

The next semantic work is the continuation and host interpretation listed by
`SUPERVISION-PG-RC112`, coordinated with the existing fiber machine. A full
concurrency cutover cannot hide these open edges or replace them with finite
probe results. The remaining trust-receipt binding is an assurance integration
obligation, separate from the already checked local proof dependencies.
