module

public import Effect4.Schema.DocumentJson
public import Effect4.Schema.Bridge

/-!
# Schema.Prepare — a persisted document prepared for the exact bridge

Decisions row 396 (2): references resolve and unions take `Ty`'s binary shape at the `Document`
boundary, before the exact bridge (`Bridge.ofSchema`). `ofSchema_exact` then stays a statement
about the prepared representation: `ofSchema (prepare d) = some t → normS (prepare d) = schema t`.
No law relates the original document to its preparation; none has a consumer yet (Codex's review,
F3, `docs/research/2026-10-15-ocaml-interop-explore/codex-review.md`).

The references table is a system of equations, one per key, and `Ty` has no recursive type, so the
preparation solves an acyclic system by substitution in dependency order:

1. **The table.** One entry per key, by the policy every reader and writer of a table shares
   (`dedupeReferences`, decisions row 8 (C)): a repeat with an equal body is the same equation, a
   repeat whose body differs is refused at its key.
2. **The order.** A depth-first walk from the root through the reference graph's edges
   (`Representation.refs`) places each reached key after the keys its entry references
   (`visit`). A key with no entry is refused at the node that references it. A key met again
   while its own entry is being walked lies on a cycle, and is refused at its entry: rc.112 admits
   such a document (`E4-SCHEMA-CE-025`), but `Ty` cannot represent it. An entry the root does not
   reach is not read.
3. **Substitution.** Each reference replaced by its entry, already resolved (`substAlg`, the
   identity algebra with its reference arm replaced, as `Schema.Template.fillAlg` replaces its
   child references).
4. **Union shape.** A bare union takes the shape `Ty.ofMembers` gives a member list under
   `schema`: no member is `never`, one member is that member, and an `anyOf` of three or more nests
   to the right, in order (`shapeAlg`). A `oneOf` of two or more is kept: nesting changes which
   inputs it admits. A union with checks, or with an annotation the bridge does not erase, is kept.

What it does not establish: that a prepared representation decodes what rc.112's document
decodes. Each pass is checked on finite controls (`Test/Schema/DocumentJson.lean`).
-/

@[expose] public section

namespace Effect4.Schema.Prepare

open Effect4 Effect4.DocumentRefusal

/-! ## The order -/

/-- Visit `k` from the node at `site`: the keys placed so far (`done`), then those `k`'s entry
reaches, then `k`. `stack` holds the keys whose entries are being walked. Each level pushes a key
of the table that is not on the stack, so on a table with distinct keys `deps.length + 1` levels of
`fuel` never run out; the empty-fuel case answers as the cycle it would be. -/
def visit (deps : List (String × List String)) : Nat → List String → List String → List String →
    String → Read (List String)
  | 0, _, _, _, k => .error ⟨["references", k], .recursiveReference k⟩
  | fuel + 1, stack, done, site, k =>
    if done.contains k then pure done
    else if stack.contains k then .error ⟨["references", k], .recursiveReference k⟩
    else match List.lookup k deps with
      | none => .error ⟨site, .missingReference k⟩
      | some ks => do
        let done ← ks.foldlM (fun done k' => visit deps fuel (k :: stack) done ["references", k] k')
          done
        pure (done ++ [k])

/-- The keys the root reaches, each after the keys its entry references. -/
def order (deps : List (String × List String)) (root : Representation) : Read (List String) :=
  root.refs.foldlM (fun done k => visit deps (deps.length + 1) [] done ["representation"] k) []

/-! ## Substitution and union shape -/

/-- Each reference to a key of `table` replaced by its entry; any other reference kept. -/
def substAlg (table : List (String × Representation)) :
    RepresentationAlgebra RepresentationSelfCarrier :=
  { RepresentationAlgebra.id with
    representation_reference := fun k => (List.lookup k.value table).getD (.reference k) }

def subst (table : List (String × Representation)) (r : Representation) : Representation :=
  cata_representation (substAlg table) r

/-- A first member and the rest, as binary `anyOf` unions nested to the right, in order: the shape
`schema (Ty.ofMembers (a :: rest))` writes. -/
def nest : Representation → List Representation → Representation
  | a, [] => a
  | a, b :: rest => .union none [] [a, nest b rest] .anyOf

/-- A union in `Ty`'s binary shape: a bare union of no member is `never`, of one member that
member; a bare `anyOf` of three or more nests to the right. Anything else is kept as it is. -/
def shapeUnion (ann : Annotations) (checks : List Check) (types : List Representation)
    (mode : UnionMode) : Representation :=
  if Bridge.normAnn ann = none ∧ checks = [] then
    match types, mode with
    | [], _ => .never none []
    | [t], _ => t
    | a :: b :: c :: rest, .anyOf => nest a (b :: c :: rest)
    | _, _ => .union ann checks types mode
  else .union ann checks types mode

def shapeAlg : RepresentationAlgebra RepresentationSelfCarrier :=
  { RepresentationAlgebra.id with representation_union := shapeUnion }

def shapeUnions (r : Representation) : Representation := cata_representation shapeAlg r

/-! ## The preparation -/

/-- **A document prepared for the exact bridge**: its references resolved, its unions in `Ty`'s
binary shape; or the located refusal of a conflicting key, a missing key, or a key on a cycle. -/
def prepare (d : Document) : Read Representation := do
  let entries ← dedupeReferences d.references
  let table := entries.map fun e => (e.key, e.representation)
  let keys ← order (table.map fun (k, r) => (k, r.refs)) d.representation
  let resolved := keys.foldl (fun acc k =>
    acc ++ [(k, subst acc ((List.lookup k table).getD (.reference ⟨k⟩)))]) []
  pure (shapeUnions (subst resolved d.representation))

/-- **A persisted document's JSON as a program type**: read exactly (`Document.ofJson`), prepared,
then read by the exact bridge. `none` is the bridge's refusal: a node `Ty` cannot represent. -/
def tyOfJson (j : Json) : Read (Option Program.Ty) := do
  let d ← Document.ofJson j
  let r ← prepare d
  pure (Bridge.ofSchema r)

end Effect4.Schema.Prepare
