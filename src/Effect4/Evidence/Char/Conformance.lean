import Effect4.Evidence.Char.Conformance.GSet
import Effect4.Evidence.Char.Conformance.Vector
import Effect4.Evidence.Char.Canonical
import Effect4.Evidence.Char.Conformance.VectorSet
import Effect4.Evidence.Char.Conformance.Receipt
import Effect4.Evidence.Char.Conformance.Generators
import Effect4.Evidence.Char.Conformance.Consume
import Effect4.Evidence.Char.Conformance.Compose
import Effect4.Evidence.Char.Conformance.Surface
import Effect4.Evidence.Char.Derived
import Effect4.Evidence.Char.Conformance.Cell

/-!
# Char.Conformance: the monotone conformance substrate

A characterized component yields a **grow-only set of conformance vectors**; an
implementation is replayed against that set and the replays are receipts.
Adding a verb, a test, a mutant, a doctest, a depth or a component only ever
*adds* vectors and receipts, because the set is a G-Set and every generator is a
monotone map into it. This root imports the modules that own each concern:

| Module | Owns | Part of the semantic compiler |
| --- | --- | --- |
| `Conformance/GSet.lean` | the grow-only set and its CRDT laws | the merge |
| `Conformance/Vector.lean` | `Fact`, `Provenance`, `Vector`, `factOf` | the instruction, and the only way to mint one |
| `Canonical.lean` | the hand `Canonical`/`Content` instances of the generic carriers, and `anyRef` | the addressing |
| `Conformance/VectorSet.lean` | `VectorSet`, `Sound`, `kills` | the module |
| `Conformance/Receipt.lean` | `Implementation`, `Receipt`, `Receipts`, `asFixtureEvidence` | the back end's carriers |
| `Conformance/Generators.lean` | `fromSuite`, `fromMutants`, `enumerate`, `enumerateRefused`, `fromDoctests` | the front-end lowering |
| `Conformance/Consume.lean` | `Target`, `consume`, `replayAgainst` | the back end |
| `Conformance/Compose.lean` | `Machine.prod`, `injectL` | linking |
| `Conformance/Surface.lean` | `characterize`, `extend`, `Characterized`, `Fixture` | the driver |
| `Derived.lean` | the generated `Canonical`/`Content` instances of the monomorphic carriers | the addressing |
| `Conformance/Cell.lean` | the worked instance and anti-vacuity kit | the substrate's own test |

The room's carriers are ordered by their typed references (Q4), and the modules follow that
order: `Implementation ≺ Receipt ≺ Evidence ≺ Claim ≺ Manifest ≺ Target ≺ Characterized`, with
`Char/Evidence.lean` and `Char/Manifest.lean` sitting between `Conformance/Receipt.lean` and
`Conformance/Consume.lean`.

The three-function surface is `characterize`, `extend`, `consume`. A coding LLM
supplies the five hand-authored parts and depth, and reads back addressed
evidence; the human in the loop is the doctest ratifier and the owner of the
freeze surfaces, nowhere else.
-/
