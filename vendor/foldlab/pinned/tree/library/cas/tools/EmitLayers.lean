import Cas.Backend.EmitLayer
import Gate

/-!
# The layer emitter — `lake exe emitlayers`

G6-a: one authored service topology, put as content at the system kind
and printed as an Effect module. The topology below is the SOURCE; every
byte of the emitted TypeScript — expressions, declared layer types, the
import list — is computed from it by `Cas/Backend/EmitLayer.lean`.

The topology is AUTHORED, not recovered. It names constructors that are
already written in `library/effects/src/cas`, but it is not a
description of any layer stack that package composes: recovering a
description from existing TypeScript is a different question with a live
correctness hazard (Effect memoizes by object reference, a description
shares by digest), and this lane does not open it.

`--check` is the byte-identity gate, wired into `check:cas`. Run from
the package root (`library/cas`).
-/

open Cas.Schema Cas.Backend Cas.Backend.Ts

namespace EmitLayersMain

/-! ## The modules the topology names

A module is an ADDRESS now, not a string. Each specifier below is put
as a marker file node (`EmitLayer.fileRef` — the design decision and
its open half are stated there), and a constructor reference names the
address rather than the path. The specifier survives as a plain string
only where a `ServiceRef` still carries one: a service reference names
a TYPE, not written code, and promoting it is a different question with
a different consumer.

The two spellings are held together at the source: `storePath` is
`storeFile.spec`, so a specifier is written once and the file node and
the service references cannot part. -/

def storeFile : FileRef := fileRef "../../src/cas/Store.ts"
def backendFile : FileRef := fileRef "../../src/cas/Backend.ts"
def kvsBackendFile : FileRef := fileRef "../../src/cas/KvsBackend.ts"
def kvsFile : FileRef := fileRef "effect/unstable/persistence/KeyValueStore"

/-- The resolution table every emission below is performed against.
`effect` itself is absent on purpose: no CONSTRUCTOR is taken from it —
only the `Crypto.Crypto` service type and `Layer`, both of which ride
`ServiceRef.path` and the emitter's always-taken import. A file node
for it would be a row nothing resolves. -/
def files : Files := [storeFile, backendFile, kvsBackendFile, kvsFile]

def storePath : String := storeFile.spec
def backendPath : String := backendFile.spec
def kvsBackendPath : String := kvsBackendFile.spec
def kvsPath : String := kvsFile.spec

/-! ## The services — keys exactly as `Context.Key.key` spells them -/

def crypto : ServiceRef :=
  { key := "effect/Crypto", name := "Crypto.Crypto", path := "effect" }

def addressScheme : ServiceRef :=
  { key := "foldlab/cas/AddressScheme", name := "AddressScheme"
  , path := storePath }

def byteReader : ServiceRef :=
  { key := "foldlab/cas/ByteReader", name := "ByteReader"
  , path := backendPath }

def byteWriter : ServiceRef :=
  { key := "foldlab/cas/ByteWriter", name := "ByteWriter"
  , path := backendPath }

def rootStore : ServiceRef :=
  { key := "foldlab/cas/RootStore", name := "RootStore"
  , path := backendPath }

def casStore : ServiceRef :=
  { key := "foldlab/cas/CasStore", name := "CasStore", path := storePath }

def casLoader : ServiceRef :=
  { key := "foldlab/cas/CasLoader", name := "CasLoader", path := storePath }

def keyValueStore : ServiceRef :=
  { key := "effect/persistence/KeyValueStore", name := "KeyValueStore"
  , path := kvsPath }

/-! ## The topology

One DAG, two roots: the same typed-node law standing over two different
byte-plane backings — a fresh in-memory backend, and the seams derived
from Effect's own `KeyValueStore`. That is the architecture claim the
package states in prose (`Store.ts`: "the store owns no storage: it is
one law over whichever backend the composition supplies"), said as
content instead.

The two roots SHARE `storeLaw` and `addressLive` by address: one digest,
named twice. Here the two regimes agree — the emitted module names one
`const` for each, so Effect's reference memoization shares exactly what
the description shares — but the agreement is a fact about this
topology, not a law, which is why `freshMemoryBacking` exists to say the
other thing out loud.

Children first: every edge names addresses that already exist, which is
what makes the residual fold a lookup rather than a traversal. -/

def topology : Option (List Binding) := do
  let cryptoLive ← bind "cryptoWebCrypto"
    ["The platform digest, as a leaf this grammar refuses to open: the",
     "constructor reaches for `crypto.subtle` through `Effect.tryPromise`.",
     "It contributes identity, never structure."]
    (.«opaque» (codeRef storeFile "layerCryptoWebCrypto")
      "host escape: WebCrypto `subtle.digest` behind a tryPromise"
      [crypto] [])
  let scheme ← bind "addressSha256"
    ["Scheme-0 SHA-256 as the address scheme — one key answered, one",
     "key still demanded."]
    (.service (codeRef storeFile "AddressScheme.layerSha256")
      addressScheme [crypto])
  let addressLive ← bind "addressLive"
    ["The scheme over the platform digest, the digest kept PRIVATE:",
     "`provide` keeps only the outer layer's answers."]
    (.provide ⟨cryptoLive.addr⟩ ⟨scheme.addr⟩)
  let backing ← bind "memoryBacking"
    ["The three byte-plane seams from one in-memory backend — a leaf",
     "whose constructor answers a whole context."]
    (.backing (codeRef backendFile "layerMemoryBackend")
      [byteReader, byteWriter, rootStore] [])
  let freshBacking ← bind "freshMemoryBacking"
    ["The same backing, built again rather than shared. This topology",
     "wants ITS OWN store, and `fresh` is the only place a description",
     "can say so: sharing is extensional here, by digest, so two",
     "occurrences of one backing are one instance unless told otherwise."]
    (.fresh ⟨backing.addr⟩)
  let foundation ← bind "foundation"
    ["The scheme and the seams side by side — neither demands anything",
     "of the other."]
    (.merge [⟨addressLive.addr⟩, ⟨freshBacking.addr⟩])
  let storeLaw ← bind "storeLaw"
    ["The typed-node law: two services answered, three demanded. Left",
     "unsatisfied on purpose, so the residual fold has something to",
     "discharge."]
    (.backing (codeRef storeFile "layerStore")
      [casLoader, casStore] [addressScheme, byteReader, byteWriter])
  let system ← bind "casSystem"
    ["The whole system: the law over its own foundation, with the",
     "foundation KEPT — `provideMerge` answers with both sides, and",
     "nothing is demanded of the caller."]
    (.provideMerge ⟨foundation.addr⟩ ⟨storeLaw.addr⟩)
  let kvsMemory ← bind "kvsMemory"
    ["Effect's own in-memory key-value store — the persistence family's",
     "simplest realization, and a written constructor like any other."]
    (.service (codeRef kvsFile "layerMemory") keyValueStore [])
  let kvsBacking ← bind "kvsBacking"
    ["The byte-plane seams derived from whatever `KeyValueStore` the",
     "composition supplies — two seams answered, the realization",
     "demanded."]
    (.backing (codeRef kvsBackendFile "layerKvsBackend")
      [byteReader, byteWriter] [keyValueStore])
  let kvsSeams ← bind "kvsSeams"
    ["The seams over the memory realization, the realization kept",
     "private."]
    (.provide ⟨kvsMemory.addr⟩ ⟨kvsBacking.addr⟩)
  let kvsFoundation ← bind "kvsFoundation"
    ["The scheme beside the key-value seams."]
    (.merge [⟨addressLive.addr⟩, ⟨kvsSeams.addr⟩])
  let kvsSystem ← bind "kvsSystem"
    ["The second root: the SAME law, over a different backing. It",
     "answers with no `RootStore` — the key-value seams do not publish",
     "roots — which is the residual fold visibly doing its job rather",
     "than copying the first root's answer."]
    (.provideMerge ⟨kvsFoundation.addr⟩ ⟨storeLaw.addr⟩)
  pure [cryptoLive, scheme, addressLive, backing, freshBacking, foundation,
        storeLaw, system, kvsMemory, kvsBacking, kvsSeams, kvsFoundation,
        kvsSystem]

/-! ## CANON-1 — service sets are spelled canonically HERE

**The law.** Two spellings of one service set now share one address.

**Why it needed saying.** A system node's address is a function of the
WRITTEN TERM, list order included (`Cas/Schema/System.lean:82-87`),
while `EmitLayer`'s residual fold deduplicates and sorts by key. So
`[casStore, casLoader]` and `[casLoader, casStore]` emit byte-identical
TypeScript and answer identical Contexts from two different addresses.
That is a CACHE-HIT DEFEATER — a plan keyed by address misses on a term
that means exactly what the hit meant — and not a tidiness complaint,
which is why the à la carte reason is the one that decides it.

**Where the canonicalization lives, and why here.** At the authoring
door: every service list in the topology above is written in
`canonServices` order, so the term this file STORES is already
canonical and no normalization happens between authoring and address.
The guard below is the enforcement, and it holds the SOURCE canonical
too — an author who writes an unsorted list gets a red elaboration
naming the defect, rather than a term that is quietly renormalized
somewhere downstream and an address nobody predicted.

**What full door-level canonicalization would take, and why it is not
this slice.** `SystemNode` is generated by `cas_union`
(`Cas/Schema/Notation.lean:92-113`), whose arms are plain inductive
constructors: there is no smart-constructor seam to canonicalize in.
Closing the door at the constructor would mean either (a) teaching the
`cas_union` macro a per-field normalization hook, so a field declared
`List ServiceRef` is canonicalized on construction for every kind the
notation generates, or (b) hand-writing `SystemNode` smart constructors
beside the generated inductive and making them the only admitted way to
build a node — which means the raw constructors have to become
unreachable, not merely discouraged. (a) is a change to the kind-
authoring notation and touches every `cas_union` in the estate; (b)
reintroduces by hand exactly what the notation exists to generate. Both
are carrier changes and both want their own ruling. Until then the
authored value plus this guard is the whole of CANON-1, and its scope
is honestly narrower than the name: it holds for terms authored in this
file, not for every `SystemNode` an arbitrary caller can construct. -/

/-- The service lists an arm carries as authored content. Edge arms
carry addresses, not services, so they contribute nothing. -/
def authoredServices : SystemNode → List (List ServiceRef)
  | .backing _ p r => [p, r]
  | .«opaque» _ _ p r => [p, r]
  | .service _ _ r => [r]
  | .fresh _ => []
  | .merge _ => []
  | .provide _ _ => []
  | .provideMerge _ _ => []

-- CANON-1, checked at elaboration: every service list in the authored
-- topology is already spelled canonically, so the stored term is the
-- canonical one and equal service sets reside at equal addresses. A red
-- here means a list above was written out of key order or with a
-- duplicate — spell it `canonServices`-sorted rather than relaxing the
-- guard.
#guard match topology with
  | none => false
  | some bs => bs.all fun b => (authoredServices b.node).all isCanonServices

/-! ## The module -/

def header : List String := [
  "GENERATED — do not edit. Effect layers lowered from an authored",
  "service topology (`tools/EmitLayers.lean`), stored at the system",
  "kind and printed by `lake exe emitlayers`; regeneration is",
  "byte-identity-gated (`--check`, wired into `check:cas`).",
  "",
  "Every import path below is RESOLVED, not copied: a constructor",
  "reference names its module by store address (`CodeRef.file`, at the",
  "file kind), and the specifier is recovered from that file node's",
  "name. The file nodes are markers — they certify WHICH MODULE, never",
  "which bytes; full-content provenance is the open half of that",
  "ruling (`Cas/Backend/EmitLayer.lean`).",
  "",
  "The acceptance this module carries is BEHAVIOURAL SHAPE, not byte",
  "identity of a hand-written original: `EmittedLayers.test.ts` builds",
  "each requirement-free layer below and asserts its Context holds",
  "exactly the key set the topology declares.",
  "",
  "What that certifies: the key set. What it does not: acquisition",
  "order, provide-versus-provideMerge residuals below the surface, and",
  "how many instances of a shared child exist. The last one is the",
  "failure mode worth naming, because its industry precedent is silent",
  "— an action cache that agrees on a hash and disagrees on the output",
  "serves the wrong answer without a word. This gate is the loud",
  "version of that check, and it is deliberately narrower than the",
  "estate's usual byte gate. The module's own BYTES are still gated by",
  "`--check`; what is behavioural is only the claim that the wiring",
  "means what the description says."
]

/-- The lane's emitted header. The module declared no version before
this one, so its `schemaVersion` opens at 1. -/
def emitted : Gate.Emitted where
  schemaVersion := 1
  emitter := "emitlayers"
  module := "library/cas/tools/EmitLayers.lean"

def rendered : IO String := do
  match topology with
  | none => throw (IO.userError
      "the topology does not project: a node's payload was refused")
  | some bs =>
    match emitModule header files bs with
    | none => throw (IO.userError
        "the topology does not resolve: a child address names nothing bound")
    | some m =>
      pure (Render.module house0
        { m with header := m.header ++ emitted.headerLines })

/-- Where the generated layers live in the effects package — beside the
generated programs, inside the test tree, so `tsc -p tsconfig.test.json
--noEmit` typechecks them as a matter of course. A positional argument
overrides it. -/
def defaultTarget : System.FilePath :=
  "../effects/test/generated/EmittedLayers.ts"

def fixtures (target : Option System.FilePath) : IO (List Gate.Fixture) := do
  let text ← rendered
  let n := (topology.map (·.length)).getD 0
  return [⟨target.getD defaultTarget, text, s!"{n} layers"⟩]

end EmitLayersMain

def main := Gate.mainAt "lake exe emitlayers" EmitLayersMain.fixtures
