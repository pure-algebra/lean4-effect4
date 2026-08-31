import Cas.Values.Json

/-!
# The architecture, as a type

The library described in its own model: the data vocabulary, the
capability seams, the laws above them, and the backends below them —
one `Architecture` type, one `foldlabCas` value, and the shape's own
laws as guards (a law never needs a capability no seam carries; a
read-only backend provides exactly the read capability; reads ride the
loader).

The TypeScript runtime carries the same description as a value, a
Schema, a service, and a layer (`src/cas/Architecture.ts`). The two
descriptions cannot drift: each side derives the capability matrix
from its own value, renders it through its own canonical JSON, and
guards the SAME pinned string — one literal, two derivations, red on
either side the moment they disagree.
-/

namespace Cas

/-- One capability of the byte plane — the unit the seams split by. -/
inductive Capability where
  | read
  | write
  | roots
  deriving DecidableEq, Repr

def Capability.key : Capability → String
  | .read => "read"
  | .write => "write"
  | .roots => "roots"

/-- One law above the seams: what it means, and which capabilities it
needs — nothing else about storage. -/
structure ArchLaw where
  name : String
  plane : String
  needs : List Capability
  means : String
  deriving Repr

/-- One backend below the seams: which capabilities it provides —
dumbness is the absence of anything else to say. -/
structure ArchBackend where
  name : String
  provides : List Capability
  means : String
  deriving Repr

/-- One carrier of the data vocabulary, with its model and runtime
homes. -/
structure ArchType where
  name : String
  form : String
  lean : String
  ts : String
  deriving Repr

/-- The library's shape: data vocabulary, seams, laws, backends. -/
structure Architecture where
  types : List ArchType
  seams : List Capability
  laws : List ArchLaw
  backends : List ArchBackend
  deriving Repr

/-- The value: `@foldlab/cas`. -/
def foldlabCas : Architecture where
  types := [
    ⟨"address", "32-byte digest of the canonical pre-image — the identity",
      "Addr32 (Cas/Node.lean)", "ContentId (src/cas/Node.ts)"⟩,
    ⟨"ref", "expected kind tag + address: one typed edge",
      "Ref (Cas/Node.lean)", "CasReference (src/cas/Node.ts)"⟩,
    ⟨"node", "version byte, kind tag, payload bytes, ordered refs",
      "Node (Cas/Node.lean)", "CasNodeInput (src/cas/Node.ts)"⟩,
    ⟨"store", "partial map address ⇀ node; grows only; closed = nothing dangles",
      "Store (Cas/Store.lean)", "seams + store law (src/cas/Backend.ts, Store.ts)"⟩,
    ⟨"root", "typed address: phantom value type + expected kind tag",
      "Root α (Cas/Refs.lean)", "Root<A> (src/cas/Value.ts)"⟩,
    ⟨"marker", "{\"$ref\": k} — the k-th reference, in canonical byte order",
      "marker grammar (Cas/Refs.lean)", "refMarkers walks (src/internal/refMarkers.ts)"⟩,
    ⟨"payload", "canonical JSON envelope {revision, value}",
      "Json.Value + renderCompact (Cas/Json.lean)", "canonicalJson (src/cas/Value.ts)"⟩,
    ⟨"addressScheme", "the digest the laws recompute — quantified over, never fixed",
      "H : Bytes → Addr (Cas/Address.lean)", "AddressScheme service (src/cas/Store.ts)"⟩ ]
  seams := [.read, .write, .roots]
  laws := [
    ⟨"store", "cas", [.read, .write],
      "put is the admission law: closure and edge kinds checked"⟩,
    ⟨"loader", "cas", [.read],
      "load-only re-verification: digest recomputed, canonical re-decode"⟩,
    ⟨"valuePut", "cas", [.read, .write],
      "typed values encode; references marker-lowered in canonical order"⟩,
    ⟨"valueGet", "cas", [.read],
      "typed values decode; references resolve to lazy typed roots"⟩,
    ⟨"blob", "cas", [.read, .write],
      "verified chunked blobs, recipe 1"⟩,
    ⟨"graphClosure", "cas", [.read],
      "children-first deduplicated reachability"⟩,
    ⟨"graphVerify", "cas", [.read],
      "the untrusted-host audit: every reachable node re-verified"⟩,
    ⟨"serverCore", "server", [.read, .write, .roots],
      "cas-http/0 interpreted over the same seams an embedded store uses"⟩ ]
  backends := [
    ⟨"memory", [.read, .write, .roots], "plain maps, grow-only"⟩,
    ⟨"file", [.read, .write, .roots],
      "a store root: objects/<2 hex>/<62 hex> + roots/<hex>, temp+rename"⟩,
    ⟨"kvs", [.read, .write],
      "any Effect KeyValueStore; SQL is the Litestream route; no roots seam"⟩,
    ⟨"pathReader", [.read],
      "any host serving bytes at a path; writes do not compile"⟩ ]

/-! ## The shape's own laws

Five statements about `foldlabCas`, and they are THEOREMS rather than
`#guard`s. The difference is not the checking — `decide` and `#guard`
run the same decision procedure — but the record: a theorem is a named
declaration of the library, so it earns a row in the surface ledger and
an entry in the axiom census, and a claim the estate makes about its
own shape is then in the ledger with every other claim rather than in
a comment beside one. A `#guard` checks and says nothing afterwards.

`decide` is the whole proof of each: every statement is a closed
computation over a finite value, and it is that finiteness — not any
argument — that makes the claims checkable at all. -/

def capsSubset (xs ys : List Capability) : Bool := xs.all (ys.contains ·)

/-- No law needs a capability no seam carries: the seam set is the
whole of what the plane offers, so a law asking for more would be a law
nothing can serve. -/
theorem lawsNeedOnlySeams :
    foldlabCas.laws.all fun l => capsSubset l.needs foldlabCas.seams := by
  decide

/-- No backend provides a capability no seam carries: a backend
offering more than the seams name would be offering it through no
seam. -/
theorem backendsProvideOnlySeams :
    foldlabCas.backends.all fun b => capsSubset b.provides foldlabCas.seams := by
  decide

/-- Read-only honesty: the path reader provides exactly the read seam.
Any host serving bytes at a path is a store the laws above can read
from and nothing more — writes do not compile. -/
theorem readOnlyHonesty :
    (foldlabCas.backends.find? (·.name = "pathReader")).map (·.provides)
      = some [.read] := by
  decide

/-- Roots honesty: the key-value backend provides the byte plane and no
roots seam, because a key-value store carries no key enumeration —
publishing over it does not compile. -/
theorem rootsHonesty :
    (foldlabCas.backends.find? (·.name = "kvs")).map (·.provides)
      = some [.read, .write] := by
  decide

/-- Reads ride the loader: the load law and every typed read need only
the read seam, so the read-only backend serves them all. The first
conjunct is the load law on its own — it is the one the other three
factor through, and it is stated separately so that a change narrowing
it is a change to a named claim. -/
theorem readsRideTheLoader :
    (foldlabCas.laws.find? (·.name = "loader")).map (·.needs) = some [.read] ∧
      ["loader", "valueGet", "graphClosure", "graphVerify"].all fun name =>
        (foldlabCas.laws.find? (·.name = name)).map (·.needs) = some [.read] := by
  decide

/-! ## The capability matrix — the shared pin -/

open Json in
def capsJson (cs : List Capability) : Value :=
  .arr (((cs.map (·.key)).mergeSort fun a b => decide (a ≤ b)).map .str)

open Json in
/-- The load-bearing projection both descriptions derive and pin: which
capabilities each law needs, each backend provides, the seam set, and
the data-vocabulary names. Prose stays per-side; this cannot drift. -/
def capabilityMatrix (a : Architecture) : Value :=
  .obj [ ("backends", .obj (a.backends.map fun b => (b.name, capsJson b.provides)))
       , ("laws", .obj (a.laws.map fun l => (l.name, capsJson l.needs)))
       , ("seams", capsJson a.seams)
       , ("types", .arr (((a.types.map (·.name)).mergeSort
           fun a b => decide (a ≤ b)).map .str)) ]

/-- The pinned canonical rendering, shared verbatim with the runtime's
`test/Architecture.test.ts`. Changing the shape means changing this
string in BOTH homes — that is the point. -/
def capabilityMatrixPin : String :=
  "{\"backends\":{\"file\":[\"read\",\"roots\",\"write\"],\"kvs\":[\"read\",\"write\"],\"memory\":[\"read\",\"roots\",\"write\"],\"pathReader\":[\"read\"]},\"laws\":{\"blob\":[\"read\",\"write\"],\"graphClosure\":[\"read\"],\"graphVerify\":[\"read\"],\"loader\":[\"read\"],\"serverCore\":[\"read\",\"roots\",\"write\"],\"store\":[\"read\",\"write\"],\"valueGet\":[\"read\"],\"valuePut\":[\"read\",\"write\"]},\"seams\":[\"read\",\"roots\",\"write\"],\"types\":[\"address\",\"addressScheme\",\"marker\",\"node\",\"payload\",\"ref\",\"root\",\"store\"]}"

#guard Json.renderCompact (capabilityMatrix foldlabCas) = capabilityMatrixPin

/-- Print the pin — regenerate both homes from one command when the
shape changes: `lake env lean --run` this module's `pin` executable
lane, or read it off a failing guard. -/
def pin : IO Unit := IO.println (Json.renderCompact (capabilityMatrix foldlabCas))

end Cas
