import Effect4.Store.Domain.Cas
import Effect4.Store.Domain.Genesis
import Effect4.Store.Domain.ShapeRead
import Effect4.Store.Domain.Derived.Value
import Effect4.Schema.OfShape
import Effect4.Laws.Store.Results

/-!
# Result envelopes: one result per query (seams ST3)

Finite controls over the actual node check, word admission, verification and read face.

* **Tested: plan §4.7, ordinary row 7.** Nodes `q`, `r1`, then `r2` for `q`, with no moves: fresh,
  fresh, then `poisoned`, naming the query and both results. A duplicate result is admitted.
* **Red (tested): malformed envelopes.** A payload that is not the envelope, an unknown envelope
  version, a wrong specification and a query field at another kind refuse `badEnvelope`. A query
  reference at kind `query` that names a schema node refuses `wrongKind`; edges precede the envelope.
* **Tested: incidental references.** A result's output may mention another query. Only the query
  field is designated: a results read selects by it, and no conflict follows from the mention.
* **Tested: varying output.** A run identity in the query's input names a new query, so its result
  is admitted beside the first.
* **Red (tested): the three entrances.** The pre-envelope checker admitted a malformed result at
  insertion, word admission and verification. Each now refuses it, and each refuses two results.
* **Control: the raw output.** The generated `Canonical Val` frames a reference as data, so the
  envelope embeds its output as is (`Shape.value`), and its references stay edges.
* **Tested: the read face.** A missing node or root answers nothing; a typed read returns the
  exact envelope.

These are finite evaluations. `Cas.result_once` (`src/Effect4/Laws/Store/Results.lean`) is the law.
-/

set_option autoImplicit false
namespace Test.Store.ResultControls
open Effect4 Effect4.Store

/-! ## The carriers -/

def gate : ActionId := ⟨"check-ocaml", 1, zeroDigest⟩
def queryA : Query Nat := ⟨gate, 41⟩
def queryB : Query Nat := ⟨gate, 42⟩
def qa : Digest := (address queryA).digest
def qb : Digest := (address queryB).digest
def resultA : Answered Nat := ⟨0, address queryA, .nat 7⟩
def resultA' : Answered Nat := ⟨0, address queryA, .nat 8⟩
def resultB : Answered Nat := ⟨0, address queryB, .ref Kind.query.byte qa.bytes⟩
def ra : Digest := (address resultA).digest
def ra' : Digest := (address resultA').digest

-- Each carrier reads back exactly; the envelope's grammar is common to every input carrier.
#guard Canonical.ofVal (Canonical.toVal gate) = some gate
#guard (Canonical.ofVal (Canonical.toVal queryA) : Option (Query Nat)).map (·.input) = some 41
#guard (nodeOf resultA).resultQuery? = some qa
#guard (nodeOf resultB).resultQuery? = some qb
#guard specOf (Answered Nat) = specOf (Answered String)
-- A query's specification names its input's shape.
#guard specOf (Query Nat) ≠ specOf (Query String)

/-! ## The store: genesis, the two schemas, the two queries -/

def schemas : List Node :=
  [genesisNode, nodeOf (shape (Query Nat)).document, nodeOf (shape (Answered Nat)).document]

def accepted (result : Except TxnRefusal (Receipt × Store)) : Store :=
  match result with | .ok (_, store) => store | .error _ => Store.empty

def base : Store := accepted (Store.empty.commit ⟨schemas ++ [nodeOf queryA, nodeOf queryB], []⟩)
#guard base.nodes.length = 5

/-! ## Ordinary row 7 -/

-- `q` is resident; `r1` enters fresh; `r2` for the same query refuses, naming both results.
#guard match base.commit ⟨[nodeOf resultA], []⟩ with
  | .ok (receipt, _) => receipt.nodes = [(ra, .fresh)]
  | _ => false
def withA : Store := accepted (base.commit ⟨[nodeOf resultA], []⟩)
#guard match withA.commit ⟨[nodeOf resultA'], []⟩ with
  | .error (.node 0 (.poisoned query first second)) => query == qa && first == ra && second == ra'
  | _ => false
-- In one transaction with no moves: the whole commit refuses at its third node.
#guard match Store.empty.commit ⟨schemas ++ [nodeOf queryA, nodeOf resultA, nodeOf resultA'], []⟩ with
  | .error (.node 5 (.poisoned query first second)) => query == qa && first == ra && second == ra'
  | _ => false
-- A duplicate result has the same identity and is admitted.
#guard match withA.commit ⟨[nodeOf resultA], []⟩ with
  | .ok (receipt, _) => receipt.nodes = [(ra, .duplicate)]
  | _ => false

/-! ## Malformed envelopes -/

def resultSpec : Digest := specOf (Answered Unit)
#guard refusedWith (base.putNode ⟨0, .result, resultSpec, .nat 0⟩) .badEnvelope
-- An unknown envelope version.
#guard refusedWith (base.putNode (nodeOf ({ resultA with version := 1 } : Answered Nat))) .badEnvelope
-- A wrong specification: the query's schema node resolves, so the envelope check refuses.
#guard refusedWith (base.putNode { nodeOf resultA with spec := specOf (Query Nat) }) .badEnvelope
-- A query field at kind `schema` that names a schema node resolves as an edge, then refuses.
#guard refusedWith (base.putNode { nodeOf resultA with
  payload := .ctor 0 [.nat 0, .ref Kind.schema.byte (specOf (Query Nat)).bytes, .nat 7] }) .badEnvelope
-- A query field at kind `query` naming a schema node: edges precede the envelope.
#guard refusedWith (base.putNode { nodeOf resultA with
  payload := .ctor 0 [.nat 0, .ref Kind.query.byte (specOf (Query Nat)).bytes, .nat 7] })
  (.wrongKind (specOf (Query Nat)) .query .schema)
-- A result for a query that is not resident dangles.
#guard refusedWith ((accepted (Store.empty.commit ⟨schemas, []⟩)).putNode (nodeOf resultA)) (.dangling qa)
-- The node version precedes everything after the payload frame.
#guard refusedWith (base.putNode { nodeOf resultA with version := 1 }) .badVersion

/-! ## The raw output -/

-- The generated `Canonical Val` frames a reference as data: its edge would be lost.
#guard (Canonical.toVal (Val.ref Kind.program.byte zeroDigest.bytes)).refs = []
-- Embedded as is, an output's reference is an edge, and admission resolves it.
#guard refusedWith (base.putNode (nodeOf ({ resultA with output := .ref Kind.program.byte zeroDigest.bytes } : Answered Nat)))
  (.dangling zeroDigest)
#guard (⟨.value, []⟩ : ShapeDoc).accepts (.ctor 713 [.nat 2, .bytes [0, 255]])
-- The raw shape has no generic JSON inverse: the reader refuses rather than guess.
#guard readIn [] [] .value (.str "a") = none

/-! ## Incidental references and varying output -/

-- `resultB` answers `qb` and mentions `qa` in its output: no conflict with `resultA`.
def withAB : Store := accepted (withA.commit ⟨[nodeOf resultB], []⟩)
#guard withAB.nodes.length = 7
-- A run identity in the input names a new query, so a second output is admitted beside the first.
def queryRun : Query Nat := ⟨gate, 43⟩
def resultRun : Answered Nat := ⟨0, address queryRun, .nat 8⟩
#guard match withA.commit ⟨[nodeOf queryRun, nodeOf resultRun], []⟩ with
  | .ok (receipt, _) => receipt.nodes.map (·.2) = [.fresh, .fresh]
  | _ => false

/-! ## The three entrances -/

/-- The malformed result the pre-envelope checker admitted (its red control, ST3 preparation). -/
def malformed : Node := ⟨0, .result, probeSchemaAddress, .nat 0⟩
def malformedAddress : Digest := sha256 malformed.encode
#guard refusedWith ((afterPut Store.empty probeSchema).putNode malformed) .badEnvelope
#guard !(Word.wf [⟨probeSchemaAddress, probeSchema⟩, ⟨malformedAddress, malformed⟩])
#guard match Store.verify ⟨[(probeSchemaAddress, probeSchema), (malformedAddress, malformed)], []⟩ with
  | .error (.badEnvelope at_) => at_ == malformedAddress
  | _ => false

def bindings : Word :=
  (schemas ++ [nodeOf queryA, nodeOf resultA]).map fun n => ⟨sha256 n.encode, n⟩
def twoResults : Word := bindings ++ [⟨ra', nodeOf resultA'⟩]
#guard Word.wf bindings
#guard !(Word.wf twoResults)
#guard (Word.apply twoResults Store.empty).toOption.isNone
-- A store holding both results, built by hand, fails verification with both named.
#guard match Store.verify ⟨twoResults.map fun b => (b.digest, b.node), []⟩ with
  | .error (.poisoned at_ query first) => at_ == ra && query == qa && first == ra'
  | _ => false

/-! ## The read face -/

def reached : Option Cas :=
  match Cas.empty.commit ⟨schemas ++ [nodeOf queryA, nodeOf queryB, nodeOf resultA, nodeOf resultB],
      [.create "gates/check-ocaml" .journal ⟨.result, ra⟩]⟩ with
  | .ok (_, cas) => some cas
  | .error _ => none

-- A journal root over a result: results carry no designated parent, so the root only starts.
#guard reached.isSome
#guard (reached.map fun cas => Cas.read cas (.node zeroDigest)) = some []
#guard (reached.map fun cas => Cas.read cas (.root "absent")) = some []
#guard (reached.map fun cas => (Cas.read cas (.root "gates/check-ocaml")).map (·.1)) = some [ra]
-- A results read selects by the designated query: `resultB` mentions `qa` and is not returned.
#guard (reached.map fun cas => (Cas.read cas (.results qa)).map (·.1)) = some [ra]
#guard (reached.map fun cas => (Cas.read cas (.results qb)).length) = some 1
-- A closure read holds the result, its query and the schemas, children first.
#guard (reached.map fun cas => ((Cas.read cas (.closure ⟨.result, ra⟩)).map (·.1)).getLast?) = some (some ra)
#guard (reached.map fun cas => (Cas.read cas (.closure ⟨.result, ra⟩)).any (·.1 == qa)) = some true
-- A typed read returns the exact envelope.
#guard (reached.bind fun cas => (Cas.get cas (address resultA)).toOption.map (·.output)) = some (.nat 7)

end Test.Store.ResultControls
