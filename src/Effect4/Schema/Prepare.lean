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

Three passes, each a fold or a table:

1. **Placement.** The keys the root reaches through the table (`reachable`), checked: a repeated
   key, a key with no entry, and a key that reaches itself are refused, located at the table.
   A recursive document is refused, not unfolded to a depth: a depth bound is no meaning for it.
   The keys are placed so that each comes after the keys its entry references (`place`).
2. **Substitution.** Each reference replaced by its entry, already resolved
   (`substAlg`, the identity algebra with its reference arm replaced).
3. **Union shape.** A bare union of one member is that member, and a bare `anyOf` of three or
   more nests to the right, in order (`shapeAlg`). A `oneOf` of three or more is kept: nesting
   changes which inputs it admits. A union with checks, or with an annotation the bridge does not
   erase, is kept.

What it does not establish: that a prepared representation decodes what rc.112's document
decodes. Each pass is checked on finite controls (`Test/Schema/DocumentJson.lean`).
-/

@[expose] public section

namespace Effect4.Schema.Prepare

open Effect4 Effect4.Schema.DocumentJson

/-! ## The keys a representation references -/

/-- The referenced keys, in the order met: an algebra of the representation fold. -/
def refsAlg : RepresentationAlgebra (fun _ => List String) where
  representation_declaration _ _ tps cs := tps.flatten ++ cs.flatten
  representation_reference k := [k.value]
  representation_suspend _ cs th := cs.flatten ++ th
  representation_null _ cs := cs.flatten
  representation_undefined _ cs := cs.flatten
  representation_void _ cs := cs.flatten
  representation_never _ cs := cs.flatten
  representation_unknown _ cs := cs.flatten
  representation_any _ cs := cs.flatten
  representation_string _ cs := cs.flatten
  representation_number _ cs := cs.flatten
  representation_boolean _ cs := cs.flatten
  representation_bigint _ cs := cs.flatten
  representation_symbol _ cs := cs.flatten
  representation_literal _ cs _ := cs.flatten
  representation_uniqueSymbol _ cs _ := cs.flatten
  representation_objectKeyword _ cs := cs.flatten
  representation_enum _ cs _ := cs.flatten
  representation_templateLiteral _ cs ps := cs.flatten ++ ps.flatten
  representation_arrays _ cs els rest :=
    cs.flatten ++ (els.map (·.type)).flatten ++ rest.flatten
  representation_objects _ cs ps is :=
    cs.flatten ++ (ps.map (·.type)).flatten ++ (is.map fun i => i.parameter ++ i.type).flatten
  representation_union _ cs ts _ := cs.flatten ++ ts.flatten
  check_filter rep _ _ := (rep.schemas.getD []).flatten
  check_filterGroup rep _ cs := ((rep.bind (·.schemas)).getD []).flatten ++ cs.flatten

/-- The keys a representation references, in the order met. -/
def refsOf (r : Representation) : List String := cata_representation refsAlg r

/-! ## Placement -/

/-- The first key that repeats in a table's key list. -/
def firstDuplicate : List String → Option String
  | [] => none
  | k :: ks => if ks.contains k then some k else firstDuplicate ks

/-- The keys reached from `start` through `deps`, each once, in the order met. Each round adds
the keys the reached ones reference; `deps.length + 1` rounds reach every key that can be. -/
def reachable (deps : List (String × List String)) (start : List String) : List String :=
  (List.range (deps.length + 1)).foldl
    (fun seen _ =>
      seen ++ ((seen.flatMap fun k => (List.lookup k deps).getD []).filter
        (fun k => !seen.contains k)).eraseDups)
    start.eraseDups

/-- The pending keys placed so that each follows every key its entry references. When no pending
key can be placed, the first pending one reaches itself, and it is refused at its entry. -/
def place (deps : List (String × List String)) : Nat → List String → List String →
    Read (List String)
  | _, placed, [] => pure placed
  | 0, _, k :: _ => under "references" (under k (refuse (.recursiveReference k)))
  | fuel + 1, placed, k :: ks =>
    match (k :: ks).find? (fun p => ((List.lookup p deps).getD []).all placed.contains) with
    | some p => place deps fuel (placed ++ [p]) ((k :: ks).filter (· != p))
    | none => under "references" (under k (refuse (.recursiveReference k)))

/-! ## Substitution and union shape -/

/-- Each reference to a key of `table` replaced by its entry; any other reference kept. -/
def substAlg (table : List (String × Representation)) :
    RepresentationAlgebra RepresentationSelfCarrier :=
  { RepresentationAlgebra.id with
    representation_reference := fun k => (List.lookup k.value table).getD (.reference k) }

def subst (table : List (String × Representation)) (r : Representation) : Representation :=
  cata_representation (substAlg table) r

/-- A first member and the rest, as binary `anyOf` unions nested to the right, in order. -/
def nest : Representation → List Representation → Representation
  | a, [] => a
  | a, b :: rest => .union none [] [a, nest b rest] .anyOf

/-- A union in `Ty`'s binary shape: a bare union of one member is that member; a bare `anyOf` of
three or more nests to the right. Anything else is kept as it is. -/
def shapeUnion (ann : Annotations) (checks : List Check) (types : List Representation)
    (mode : UnionMode) : Representation :=
  if Bridge.normAnn ann = none ∧ checks = [] then
    match types, mode with
    | [t], _ => t
    | a :: b :: c :: rest, .anyOf => nest a (b :: c :: rest)
    | _, _ => .union ann checks types mode
  else .union ann checks types mode

def shapeAlg : RepresentationAlgebra RepresentationSelfCarrier :=
  { RepresentationAlgebra.id with representation_union := shapeUnion }

def shapeUnions (r : Representation) : Representation := cata_representation shapeAlg r

/-! ## The preparation -/

/-- Where a missing key is referenced: the root, or the first entry that references it. -/
def siteOf (root : Representation) (deps : List (String × List String)) (k : String) :
    List String :=
  if (refsOf root).contains k then ["representation"]
  else match deps.find? (fun d => d.2.contains k) with
    | some (k', _) => ["references", k']
    | none => []

/-- **A document prepared for the exact bridge**: its references resolved, its unions in `Ty`'s
binary shape; or the located refusal of a repeated key, a missing key, or a recursive one. -/
def prepare (d : Document) : Read Representation := do
  if let some k := firstDuplicate (d.references.map (·.key)) then
    under "references" (under k (refuse (.duplicateKey k)))
  let deps := d.references.map fun e => (e.key, refsOf e.representation)
  let needed := reachable deps (refsOf d.representation)
  if let some k := needed.find? (fun k => (List.lookup k deps).isNone) then
    throw ⟨siteOf d.representation deps k, .missingReference k⟩
  let order ← place deps (needed.length + 1) [] needed
  let table := order.foldl (fun acc k =>
    acc ++ [(k, subst acc ((List.lookup k (d.references.map fun e => (e.key, e.representation))).getD
      (.reference ⟨k⟩)))]) []
  pure (shapeUnions (subst table d.representation))

/-- **A persisted document's JSON as a program type**: read exactly (`Document.ofJson`), prepared,
then read by the exact bridge. `none` is the bridge's refusal: a node `Ty` cannot represent. -/
def tyOfJson (j : Json) : Read (Option Program.Ty) := do
  let d ← Document.ofJson j
  let r ← prepare d
  pure (Bridge.ofSchema r)

end Effect4.Schema.Prepare
