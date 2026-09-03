> **Superseded (2026-09-02).** The first-order flow packet moved to
> lean4-effects and was re-frozen as Flow v2 in
> `test/contracts/flow-v2.contract.md` there (Effects v0.4.0, `e86f141`):
> block parameter lists, positional operands, the cycle clause, and seventeen
> ordered admission clauses. This file is retained as the v1 record; its
> battery and the Effect4 mutation script were retired with the pin bump.

# First-order Flow admission contract

Status: FROZEN / RED, breaker-authored 2026-08-31

Implementation fence: `Effect4/Flow/{Block,Raw,Checked,Admission}.lean`

Battery: `Effect4Test/Flow/AdmissionContract.lean`

Counterexamples: `test/counterexamples/REGISTER.md`, rows
`E4-FLOW-CE-001` through `E4-FLOW-CE-005`, `E4-FLOW-CE-007`,
`E4-FLOW-CE-013`, and `E4-FLOW-CE-014`

## Claim boundary

This packet freezes the first representative of Effect4's reifiable program
boundary: nominal identifiers, one closed operation alphabet, raw first-order
blocks, graph closure and local typing predicates, ordered diagnostics, and an
opaque admitted graph carrying a proof of those predicates.

The intended proof grade is kernel-checked admission soundness and relative
completeness for this finite checker. This packet does not define elaboration
to `Program`, operational or denotational semantics, decisions, runs,
frontiers, handlers, foreign registration, generation, or TypeScript. It makes
no termination or determinism claim about an admitted graph. Those are later
packets over this carrier.

## Frozen evidence and rejected alternatives

The Foldlab evidence revision is
`feb29321fd50204aa338209d313e84a3f8b71c66`. The local S2 coordinator report
was re-read at SHA-256
`2324ad78f58504263531eae170ffd57cb9b439532ea700e54803924fafe9f35d`.
It reports seven distinct `RawProgram` carriers, six distinct `AER` carriers,
eight distinct `ProgramWF` predicates, and five incompatible diagnostic/check
families across 24 workshop files. The report is currently untracked Foldlab
evidence, not a source pin and not an Effect4 API authority.

No S2 carrier is copied. In particular, this packet has no `AER`,
`ProgramWF`, `PProg`, handler table, region table, foreign registry, host
closure, or program-owned environment. It retains only the carrier-independent
lesson that diagnostics need a payload, a precise site, a fixed clause order,
and evidence that the reported clause actually condemns the input.

The existing Effect4 `Program` remains the sole algebraic proof carrier.
`RawFlow` and `CheckedFlow` are first-order graph content for identity, sharing,
cycles, admission, and later generation; they are not another free monad.

## CATEGORIES

- `inductive-data` — identifiers, raw terms, blocks, and flows are finite
  first-order data;
- `contracts` — the checked constructor is private and admission is the public
  proof-producing boundary;
- `specification-design` — seven independently named well-formedness clauses
  compose into exactly one `FlowWF` structure;
- `algebraic-laws` — soundness, completeness, erasure, and reachability closure
  are the admission laws;
- `proof-mechanics` — every checker branch is finite list recursion with an
  explicit first-error order;
- `abstraction-modules` — clients inspect `erase` and proved observations, not
  the checked representation constructor;
- `claim-scope` — graph closure is distinct from execution, denotation, and
  target conformance.

## REQUIRES

1. Lean core and Std at the repository's pinned Lean 4.33.1 toolchain.
2. The implemented `Effect4.Algebra.Program` remains a distinct higher-order
   proof syntax. No Flow declaration depends on a host continuation.
3. `Ty` has decidable equality at the admission boundary. The closed alphabet
   supplies executable operation lookup and two inverse lookup laws.
4. Identifier order is the natural order of the wrapped `Nat`; canonical block
   and root tables are strictly ascending in that order.

## Public declaration DAG

Binder names may differ. Names, universes, argument roles, constructor fields,
result types, and theorem propositions are frozen by the Lean battery.

### D0 — nominal identifiers

```lean
structure BlockId where value : Nat
structure OperationId where value : Nat
structure AlphabetId where value : Nat
structure DecisionId where value : Nat
```

Each has `DecidableEq`. They are distinct nominal types: an operation,
decision, or alphabet identifier cannot be used as a block identifier without
an explicit conversion.

### D1 — closed operation alphabet

```lean
structure FlowAlphabet.{uTy,uOp} (Ty : Type uTy) where
  id : AlphabetId
  Op : Type uOp
  operationId : Op -> OperationId
  lookup : OperationId -> Option Op
  requestTy : Op -> Ty
  answerTy : Op -> Ty
  lookup_operationId : forall operation,
    lookup (operationId operation) = some operation
  operationId_of_lookup : forall {id operation},
    lookup id = some operation -> operationId operation = id
```

`FlowAlphabet` is the closed semantic environment supplied to admission. Raw
content stores only its `AlphabetId`; it does not store the lookup functions.
The two laws make operation identifiers faithful on the admitted alphabet.

### D2 — raw first-order ANF graph

```lean
inductive RawTerm where
  | ret
  | jump (target : BlockId)
  | perform (operation : OperationId) (target : BlockId)
  | choose (decision : DecisionId) (left right : BlockId)

def RawTerm.successors : RawTerm -> List BlockId

structure RawBlock (Ty : Type uTy) where
  id : BlockId
  inputTy : Ty
  term : RawTerm

structure RawFlow (Ty : Type uTy) where
  alphabet : AlphabetId
  roots : List BlockId
  entry : BlockId
  inputTy : Ty
  resultTy : Ty
  blocks : List (RawBlock Ty)
```

The block's single input is the ANF payload. `ret` returns that payload;
`jump` and `choose` pass it unchanged; `perform` uses it as the request and
passes the operation answer to its target block. Therefore no value AST or
host continuation is duplicated in this admission slice.

### D3 — lookup, reachability, and well-formedness

The public relations are:

```lean
lookupBlock : RawFlow Ty -> BlockId -> Option (RawBlock Ty)
Edge : RawFlow Ty -> BlockId -> BlockId -> Prop
ReachableFrom : RawFlow Ty -> BlockId -> BlockId -> Prop
Reachable : RawFlow Ty -> BlockId -> Prop
EntryReachable : RawFlow Ty -> BlockId -> Prop
```

`Edge raw source target` holds exactly when the declared source block contains
`target` in `RawTerm.successors`. `ReachableFrom` is reflexive-transitive graph
reachability. `Reachable` starts at any declared root; `EntryReachable` starts
at `raw.entry`.

The seven clauses are named separately and assembled without an acyclicity,
totality, or reachability-coverage field:

```lean
AlphabetWF alphabet raw
IdsWF raw
RootsWF raw
ReferencesWF raw
OperationsWF alphabet raw
EntryWF raw
TermsWF alphabet raw

structure FlowWF alphabet raw : Prop where
  alphabet : AlphabetWF alphabet raw
  ids : IdsWF raw
  roots : RootsWF raw
  references : ReferencesWF raw
  operations : OperationsWF alphabet raw
  entry : EntryWF raw
  terms : TermsWF alphabet raw
```

Their meanings are frozen as follows.

- `AlphabetWF`: `raw.alphabet = alphabet.id`.
- `IdsWF`: block identifiers are pairwise distinct, block rows are strictly
  ascending by identifier, and every `DecisionId` occurring in `choose` is
  globally unique, including in unreachable blocks.
- `RootsWF`: roots are nonempty, pairwise distinct, strictly ascending, contain
  the entry, and every root resolves through `lookupBlock`.
- `ReferencesWF`: every successor of every declared block resolves. This is a
  whole-document closure check, not a reachable-subgraph check.
- `OperationsWF`: every operation identifier in every `perform` resolves in
  the supplied alphabet.
- `EntryWF`: the entry resolves and its block input type equals
  `raw.inputTy`.
- `TermsWF`: every declared block satisfies these local equations:
  `ret` requires `block.inputTy = raw.resultTy`; `jump target` requires the
  target input type to equal `block.inputTy`; `perform op target` requires the
  block input type to equal the operation request type and the target input
  type to equal its answer type; `choose _ left right` requires both target
  input types to equal `block.inputTy`.

Cycles, self-cycles, unreachable declared blocks, and unreachable closed cycles
are permitted. A dangling edge is rejected even when its source is unreachable.

### D4 — ordered diagnostics and checked admission

`AdmissionClause` has exactly this constructor and scan order:

```text
alphabetMismatch
duplicateBlockId
duplicateDecisionId
nonCanonicalBlockOrder
emptyRoots
duplicateRoot
nonCanonicalRootOrder
entryNotRoot
danglingRoot
danglingSuccessor
unknownOperation
entryTypeMismatch
termTypeMismatch
```

`CheckSite` is packet-owned and identifies the precise flow, block-table row,
decision block, root row, successor slot, operation block, entry, or term.
`DiagnosticPayload Ty` distinguishes no payload, alphabet IDs, block IDs,
decision IDs, operation IDs, and expected/actual types. `Diagnostic Ty` stores
`clause`, `site`, and `payload`; a clause-only diagnostic is not admitted.

`scan : List AdmissionClause` is the fixed order above.
`diagnoseAt alphabet raw clause` returns the first offending table occurrence
inside that clause, using source-list order and left-before-right successor
order. `FirstDiagnostic alphabet raw diagnostic` states both that
`diagnostic` is emitted by its clause and that all clauses before it in `scan`
emit `none`. Its public `condemns` projection prevents a checker from returning
one fixed but unrelated error.

```lean
structure CheckedFlow (alphabet : FlowAlphabet Ty) where
  private mk ::
  raw : RawFlow Ty
  wf : FlowWF alphabet raw

def CheckedFlow.erase : CheckedFlow alphabet -> RawFlow Ty

def admit [DecidableEq Ty] (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty) :
  Except (Diagnostic Ty) (CheckedFlow alphabet)
```

The checked constructor remains private. `raw`, `wf`, and `erase` are public
observations. Admission scans clauses in the frozen order and constructs the
checked value only after all clauses return `none`.

## ENSURES

The builder must prove these exact edges without `sorry`, `admit`, custom
axioms, unsafe declarations, partial declarations, or `Classical.choice`:

1. `admit_sound`: an admitted raw flow satisfies `FlowWF`.
2. `admit_complete`: every `FlowWF` raw flow is admitted.
3. `error_iff_not_wf`: some admission error occurs exactly when `FlowWF` does
   not hold.
4. `error_iff_firstDiagnostic`: a particular error is returned exactly when it
   is the `FirstDiagnostic`.
5. `FirstDiagnostic.condemns`: the reported diagnostic is emitted by its named
   clause.
6. `Diagnostic.clause_all_complete`: all clause checks return `none` exactly
   when `FlowWF` holds.
7. `erase_wf`: erasure of a checked flow is well formed.
8. `erase_admit`: successful admission erases to the input raw flow.
9. `admit_erase`: re-admitting an erasure yields the same checked value.
10. `FlowWF.reachable_declared`: every root-reachable block resolves in the
    declared table.

These theorems establish admission, not semantic adequacy. In particular,
`admit_complete` is relative to these seven frozen clauses.

## Decrease, frame, and trust

`lookupBlock`, clause checks, and admission recurse over finite lists. Any
helper that scans successors decreases on the successor list; reachability is
an inductive relation, not an executable unbounded graph search. The checker
does not mutate state, invoke a handler, execute a host callback, or allocate a
runtime resource. Its frame is the supplied alphabet plus the raw value.

The public proof ceiling is Lean's kernel plus the repository allowlist
`[propext, Quot.sound]`; this slice is expected to need at most proof
irrelevance/propositional extensionality for checked-value equality. The
default declaration gate independently rejects custom axioms, unsafe code,
partial code, `sorry`, and unrooted modules.

## Falsification battery

- `E4-FLOW-CE-001`: repeated block IDs are rejected before block ordering.
- `E4-FLOW-CE-002`: dangling roots and dangling successors report distinct,
  exact sites.
- `E4-FLOW-CE-003`: an unknown operation ID is rejected even when its target
  resolves.
- `E4-FLOW-CE-004`: a known operation whose answer type disagrees with its
  target block is rejected as a term type mismatch.
- `E4-FLOW-CE-005`: a locally typed self-cycle is admitted; acyclicity is not a
  hidden `FlowWF` clause.
- `E4-FLOW-CE-007`: a flow with an alphabet mismatch and a duplicate block ID
  reports the alphabet mismatch, proving the frozen first-error order matters.
- `E4-FLOW-CE-013`: `RawTerm` rejects a Lean function where a block ID is
  required; canonical content has no host continuation field.
- `E4-FLOW-CE-014`: an unreachable closed self-cycle is admitted, while an
  unreachable dangling successor is rejected by whole-document closure.

`E4-FLOW-CE-006` and the execution/nondeterminism/frontier counterexamples are
reserved for the later elaboration and semantics packets. They are not silently
discharged here.

## RED and acceptance commands

The breaker records the intended red state with:

```text
lake env lean Effect4Test/Flow/AdmissionContract.lean
```

It must fail only because the frozen Flow declarations do not yet exist. After
implementation, acceptance additionally requires:

```text
lake env lean Effect4Test/Flow/AdmissionContract.lean
lake clean && lake build Effect4Test
```

The builder then records exported theorem axiom receipts and mutation results
without editing this contract or its Lean battery.
