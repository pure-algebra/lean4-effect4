import Effect4.StdLib.Rc112

/-!
# StdLib.Links

Owner: the census as a store — the documents, the name space, the one store the pinned library
lives in — and the semantics this tree holds for an export.

The store is built children-first, because admission resolves every edge before it admits a
node (`Store/Store.lean:262-276`): the genesis (the meta-schema, `Store/Genesis.lean`), then the
three documents this census needs as schema nodes under it, then the twenty-one pinned files,
then the eighteen hundred entries — each with a `ref` edge at kind `source` that the file's node
answers — then one `tree` node binding `module/name` to each entry, then the root
`stdlib/rc112` at root kind `stdlib`. Names left the store with the trie (Q3), so a name
resolves through that tree and nowhere else, and ids are gone.

`store` is stated, not guarded. Its first node is a SHA-256 over ninety-two kilobytes and its
last is the eighteen-hundredth hash of the run; what a battery can afford to reduce is lane B's
measurement, so the prefixes `storeSchemas` and `storeSources` are exported for it to measure
against. Everything a guard can afford is here: the reading side (`entryAt`, `semanticsOf`,
`Link.checked`) never hashes anything but the twenty-one file addresses `Rc112.entries` carries.

A `Link` ties a census path to the model elements that reify it: a frame primitive (what the
rc.112 run loop evaluates it as), a machine action (what `withFiber` does for it), a store
operation (what a `sync` thunk does for it). Every link is checked: the path is a census entry,
and a primitive, action or store operation names a constructor the model has. The service-route
rows the links used to cite went to branch `archive/flow-route` with the families
(`docs/research/2026-09-04-prod-cleanup-inventory.md`, D3); the Eff-era replacement is the
`arms` table of `src/Effect4/Program/Eff.lean`, one row per constructor with the rc.112 line it
compiles to.

This is the atom-level view of code: a name in a program resolves through the tree to its
entry, and through the links to its semantics.
-/

set_option autoImplicit false

namespace Effect4.StdLib

open Effect4 (Document Json)
open Effect4.Store

/-! ## The documents and the printer

Each document is the carrier's shape rendered by the Q5 table, and it is also the spec the
carrier's nodes carry (`specOf`); each `json` is the same table's printer. Neither is identity —
the address is the structural bytes (Q1) — and both live here rather than beside the carriers
because the shapes come from the generated instances of `StdLib/Derived.lean`. The kind
alphabet a document renders is the *constructor* spelling (`class_`, `namespace_`), because the
shape is read off the inductive; `ExportKind.spelling` stays the census TSV's spelling. -/

/-- The schema of a pinned file. -/
def sourceDoc : Document := Canonical.document Source

/-- The schema of an export. -/
def entryDoc : Document := Canonical.document Entry

/-- The schema of a name space. -/
def treeDoc : Document := Canonical.document Tree

/-- A pinned file as JSON, read off its shape; the digest crosses as lowercase hex. -/
def Source.json (source : Source) : Json := Canonical.print source

/-- An export as JSON, read off its shape; the source reference crosses as lowercase hex. -/
def Entry.json (entry : Entry) : Json := Canonical.print entry

/-! ## The name space -/

/-- One binding for a row: its name, and its node's address at kind `export`. -/
def bind (acc : List (String × AnyRef)) (entry : Entry) : List (String × AnyRef) :=
  let name := entry.pathName
  let target : AnyRef := ⟨.export, (address entry).digest⟩
  if acc.any fun binding => binding.1 == name then
    acc.map fun binding => if binding.1 == name then (name, target) else binding
  else acc ++ [(name, target)]

/-- The bindings of a census: one per distinct `module/name`, at the position of its first row
and the address of its last. That is what the retired trie's repeated `putAt` left under a path,
and it is why `Effect.gen` — declared once as a `const` and once as a `declare namespace` —
binds to the namespace. -/
def bindings (entries : List Entry) : List (String × AnyRef) := entries.foldl bind []

/-- The census tree: every name of the pinned library, bound to its entry's node. -/
def nameTree : Tree := ⟨bindings Rc112.entries⟩

/-- The name the census root carries. -/
def rootName : String := "stdlib/rc112"

/-! ## The store -/

/-- The genesis and the three documents this census files under it. Admission resolves a node's
spec edge, so every kind the census puts needs its document resident first: `Source` for the
files, `Entry` for the exports, `Tree` for the name space. -/
def storeSchemas : Store :=
  putOr (putOr (putOr (putOr Store.empty metaSchema) sourceDoc) entryDoc) treeDoc

/-- The twenty-one pinned files, under their document. -/
def storeSources : Store := Rc112.sources.foldl putOr storeSchemas

/-- The pinned standard library as one store: the genesis, the three documents, the files, the
entries, the name space, and the root `stdlib/rc112` naming it. -/
def store : Store :=
  let withEntries := Rc112.entries.foldl putOr storeSources
  let withTree := putOr withEntries nameTree
  putRootOr withTree ⟨rootName, .stdlib, .tree, (address nameTree).digest, 1⟩

/-! ## Reading the census

The cheap face: `entryAt` reads the census list, so nothing but the twenty-one file addresses is
hashed. The store face: `treeResolve` reads the tree node's bindings, which is what a reader
with only the store in hand would do; the two agree by the construction of `bindings`. -/

/-- The entry a census path names: the last row with that module and name, which is the one the
tree binds. -/
def entryAt (path : List String) : Option Entry :=
  (Rc112.entries.filter fun entry => entry.pathName == pathName path).getLast?

/-- The address a census path names. -/
def resolve (path : List String) : Option (Ref Entry) := (entryAt path).map address

/-- The reference a census path names, read out of the tree node itself. -/
def treeResolve (path : List String) : Option AnyRef :=
  (nameTree.bindings.find? fun binding => binding.1 == pathName path).map Prod.snd

/-- Every name the census binds, in first-appearance order. -/
def names : List String := nameTree.bindings.map Prod.fst

/-! ## The links -/

/-- A model element an export is tied to. -/
inductive ModelRef where
  /-- A constructor of `Effect4.Prim`: the frame the run loop evaluates. -/
  | prim (constructor : String)
  /-- A `WithFiberAction`: what the fiber does for it. -/
  | action (name : String)
  /-- A `Deep.Stores.SyncOp`: what the store does for it. -/
  | syncOp (name : String)
deriving DecidableEq, Repr

/-- One export's semantics: the census path it is named at, and the model elements it reifies.
The path is `[module, name]`, the census spelling; the store spells it `module/name`. -/
structure Link where
  /-- The census path, `[module, name]`. -/
  path : List String
  /-- The model elements the export reifies. -/
  refs : List ModelRef
deriving DecidableEq, Repr

/-- The frame primitives, as `src/Effect4/Machine/Frames.lean` declares them. -/
def primNames : List String :=
  ["success", "failure", "sync", "suspend", "withFiber", "yieldableError", "iterator",
   "onSuccess", "onFailure", "onSuccessAndFailure", "exitFrame", "onExit", "setInterruptible",
   "whileLoop", "yieldNowWith", "async", "asyncFinalizer"]

/-- The fiber actions, as `src/Effect4/Machine/Fibers.lean` declares them. -/
def actionNames : List String :=
  ["fork", "forkIn", "forkScoped", "runIn", "interrupt", "interruptScoped", "interruptAll",
   "awaitAll", "awaitAllFailFast", "snapshotChildren", "awaitNewChildren", "raceAll",
   "setInterruptible", "setContext", "getContext", "getId"]

/-- The store operations, as `src/Effect4/Machine/Stores.lean` declares them. -/
def syncOpNames : List String :=
  ["refMake", "refGet", "refSet", "refGetAndSet", "refSetAndGet", "refUpdate", "refGetAndUpdate"]

/-- The links this tree holds today: the runtime surface the models reify. -/
def links : List Link :=
  [ ⟨["Effect", "gen"], [.prim "iterator"]⟩
  , ⟨["Effect", "sync"], [.prim "sync"]⟩
  , ⟨["Effect", "suspend"], [.prim "suspend"]⟩
  , ⟨["Effect", "succeed"], [.prim "success"]⟩
  , ⟨["Effect", "fail"], [.prim "failure"]⟩
  , ⟨["Effect", "failCause"], [.prim "failure"]⟩
  , ⟨["Effect", "flatMap"], [.prim "onSuccess"]⟩
  , ⟨["Effect", "catchCause"], [.prim "onFailure"]⟩
  , ⟨["Effect", "matchCauseEffect"], [.prim "onSuccessAndFailure"]⟩
  , ⟨["Effect", "onExit"], [.prim "onExit"]⟩
  , ⟨["Effect", "exit"], [.prim "exitFrame"]⟩
  , ⟨["Effect", "uninterruptible"], [.prim "setInterruptible", .action "setInterruptible"]⟩
  , ⟨["Effect", "interruptible"], [.prim "setInterruptible", .action "setInterruptible"]⟩
  , ⟨["Effect", "whileLoop"], [.prim "whileLoop"]⟩
  , ⟨["Effect", "yieldNow"], [.prim "yieldNowWith"]⟩
  , ⟨["Effect", "yieldNowWith"], [.prim "yieldNowWith"]⟩
  , ⟨["Effect", "callback"], [.prim "async", .prim "asyncFinalizer"]⟩
  , ⟨["Effect", "withFiber"], [.prim "withFiber"]⟩
  , ⟨["Effect", "forkChild"], [.prim "withFiber", .action "fork"]⟩
  , ⟨["Effect", "forkDetach"], [.prim "withFiber", .action "fork"]⟩
  , ⟨["Effect", "forkIn"], [.prim "withFiber", .action "forkIn"]⟩
  , ⟨["Effect", "forkScoped"], [.prim "withFiber", .action "forkScoped"]⟩
  , ⟨["Effect", "raceAll"], [.prim "withFiber", .action "raceAll"]⟩
  , ⟨["Effect", "contextWith"], [.prim "withFiber", .action "getContext"]⟩
  , ⟨["Fiber", "interrupt"], [.action "interrupt"]⟩
  , ⟨["Fiber", "interruptAll"], [.action "interruptAll"]⟩
  , ⟨["Fiber", "awaitAll"], [.action "awaitAll"]⟩
  , ⟨["Ref", "make"], [.prim "sync", .syncOp "refMake"]⟩
  , ⟨["Ref", "get"], [.prim "sync", .syncOp "refGet"]⟩
  , ⟨["Ref", "set"], [.prim "sync", .syncOp "refSet"]⟩
  , ⟨["Ref", "getAndSet"], [.prim "sync", .syncOp "refGetAndSet"]⟩
  , ⟨["Ref", "setAndGet"], [.prim "sync", .syncOp "refSetAndGet"]⟩
  , ⟨["Ref", "update"], [.prim "sync", .syncOp "refUpdate"]⟩
  , ⟨["Ref", "getAndUpdate"], [.prim "sync", .syncOp "refGetAndUpdate"]⟩
  , ⟨["Deferred", "poll"], [.prim "sync"]⟩
  , ⟨["Deferred", "await"], [.prim "async"]⟩ ]

/-- Whether a model reference names something the model declares. -/
def ModelRef.declared : ModelRef → Bool
  | .prim name => primNames.contains name
  | .action name => actionNames.contains name
  | .syncOp name => syncOpNames.contains name

/-- Whether a link's path is a census entry and every reference is declared. -/
def Link.checked (link : Link) : Bool :=
  (entryAt link.path).isSome && link.refs.all ModelRef.declared

/-- The semantics held for a path: its entry and its references. -/
def semanticsOf (path : List String) : Option (Entry × List ModelRef) :=
  (entryAt path).map fun entry =>
    (entry, ((links.find? fun link => link.path == path).map Link.refs).getD [])

/-! ## Anti-vacuity

Everything here reads the census list, not the store: the store's first node hashes the
ninety-two-kilobyte meta-schema and its last is the eighteen-hundredth hash of the run, and what
a kernel can afford of that is lane B's measurement (`docs/research/2026-09-05-workshop-cas/NOTES-C.md`). -/

#guard links.length == 36
#guard links.all Link.checked
#guard (entryAt ["Effect", "gen"]).map Entry.kind == some .namespace_
#guard (entryAt ["Ref", "get"]).map Entry.module == some "Ref"
#guard (entryAt ["Fiber", "await"]).isSome
#guard (entryAt ["Deferred", "await"]).isSome
#guard (entryAt ["Effect", "notAnExport"]).isNone
-- `Layer.scoped` is a construction, not an export: the census refuses to link it.
#guard (entryAt ["Layer", "scoped"]).isNone
#guard (semanticsOf ["Effect", "gen"]).map Prod.snd == some [.prim "iterator"]
#guard (semanticsOf ["Ref", "get"]).map Prod.snd == some [.prim "sync", .syncOp "refGet"]
-- A path with an entry but no link held yet answers the entry and no references.
#guard (semanticsOf ["Effect", "map"]).map Prod.snd == some []
#guard !(ModelRef.declared (.syncOp "refTeleport"))
#guard !(ModelRef.declared (.prim "onStep"))
-- Every entry's source reference points at a file the census holds.
#guard Rc112.sources.length == 21
#guard (Rc112.sources.find? fun source => source.module == "Ref").map address ==
  (entryAt ["Ref", "get"]).map Entry.source

/-! ## Receipts -/

#print axioms sourceDoc
#print axioms entryDoc
#print axioms treeDoc
#print axioms Source.json
#print axioms Entry.json
#print axioms bind
#print axioms bindings
#print axioms nameTree
#print axioms storeSchemas
#print axioms storeSources
#print axioms store
#print axioms entryAt
#print axioms resolve
#print axioms treeResolve
#print axioms names
#print axioms ModelRef.declared
#print axioms Link.checked
#print axioms semanticsOf

end Effect4.StdLib
