import Cas.Schema.System
import Cas.Backend.Target
import Cas.Backend.Ts
import Cas.Codec.NodeCodec
import Cas.Codec.Sha256
-- The file kind is the grammar's own (`0x0B` over manifest over
-- chunk), so a code reference's target is built by the grammar's
-- constructors and not by a second spelling of a named blob.
import Cas.Grammar.Syntax
-- The emitted table stamps each topology's own address, so the
-- generated module names the content it was lowered from.
import Cas.Codec.Hex

/-!
# Layer emission — a described topology as TypeScript

`Cas/Schema/System.lean` says what a service topology IS; this module
says what it LOOKS LIKE in the target language. Nothing new is minted
on the way: the expressions are `Ts.Expr.call` over a (possibly
dotted) `Ts.Expr.ident`, the declared type is `Target.LayerType.lower`,
and the module is the same `Ts.Module` every other emitter builds. The
ratified claim that layer generation needs ZERO new fragment forms is
executed here rather than restated.

## The three things that are DERIVED

- **The expression.** One arm, one call: `Layer.provide`,
  `Layer.provideMerge`, `Layer.mergeAll`, `Layer.fresh`, or the bare
  constructor reference for a leaf. Generated code does not imitate the
  hand-written `.pipe(…)` style and is not meant to — the acceptance is
  behavioural, not textual.
- **The declared type.** `Layer.Layer<ROut, E, RIn>` where `ROut` is the
  keys the topology answers with and `RIn` is what it still demands,
  both computed by the fold below. A wrong fold is a TypeScript
  compile error in the generated module, which is the cheapest gate in
  the chain.
- **The import list.** Every code reference names its module BY
  ADDRESS, and the module specifier is recovered from the file node's
  `name` through the resolution table below. The imported name is the
  FIRST DOTTED SEGMENT of the export, so `AddressScheme.layerSha256`
  imports `AddressScheme` and `Crypto.Crypto` imports `Crypto`. A
  dotted reference therefore requires its first segment to be a real
  named export — the rule is stated because it is a real constraint on
  what a topology may name.

## What the address promotion cost the emitter, stated

`CodeRef.path` was a module specifier the emitter read straight off the
term. `CodeRef.file` is an address, and an address is not a path: the
emitter has to RESOLVE it. That is the honest coupling this ruling
buys, and it is paid the same way the residual fold already pays for
addressed children — with a table built beside the bindings, consulted
by lookup, and refusing (`none`) when an address names nothing. The
gain is that the topology's edge to written code is now a typed edge
the store walks, counts, and refuses at the wrong kind, instead of a
string nothing checks.

## The fold, and what it is not

`residualOf` computes what a node answers with and what it still
demands, in Effect's own algebra: `provide` keeps the outer's answers
and discharges the outer's demands against the inner's answers;
`provideMerge` keeps both sides' answers and discharges the same way;
`mergeAll` unions both; `fresh` changes neither. Sets are kept
deduplicated by key and sorted by key, so the derived type and the
derived table are one order and the bytes are stable.

The fold is over a TABLE built children-first, never over the term:
children are store addresses, so a node cannot be resolved without the
content its addresses name. That is the whole reason the carrier needs
no fixpoint, and it is why `emitModule` takes an ordered binding list
rather than a tree.

## What this module does NOT do

It never RECOVERS a topology from TypeScript. Effect memoizes a layer
by object reference, a description shares by digest, and the two
disagree about how many instances exist — so recovery is a correctness
question this lane does not open (`EFFECT-AST-PLACEMENT.md` §3a).
Generation is one-way here by ruling, not by omission. It also emits no
error channel (`E` is always `never`) and no constructor arguments: a
leaf names a layer VALUE, never a layer-returning function. Both are
growth with a consumer, not gaps to be filled speculatively.
-/

namespace Cas.Backend

open Cas.Schema Cas.Backend.Ts

/-! ## The node, and the address it resides at -/

/-- The node one system term resides at: the landed projection bridge
(`Projection.putNode`) at the system kind, revision 1. -/
def systemNodeOf (n : SystemNode) : Option Cas.Node :=
  Cas.Schema.putNode Cas.Grammar.schemeVersion systemKindTag 1 n

/-- Its content address under the production digest — the identity the
store answers when this topology is admitted, and the identity a
parent's `StoreRef` names. -/
def systemAddressOf (n : SystemNode) : Option Addr32 :=
  (systemNodeOf n).map fun node => Cas.sha256Addr (Cas.encodeNode node)

/-! ## Files — the module specifiers, recovered from addresses

A `CodeRef` names its module by address now, so the specifier the
import list needs is not in the term. The file kind carries a NAME, and
by the convention this lane authors under that name IS the module
specifier. Recovering it is a lookup, on the same children-first
discipline `resolveAll` runs and for the same reason: a node cannot be
emitted without the content its addresses name.

### The file node's content — the design decision, stated not assumed

A `CodeRef.file` could address either of two things, and they are not
equivalent:

- the module's FULL SOURCE. Complete provenance: the topology becomes a
  Merkle DAG all the way down to the bytes that build it, and the
  address certifies exactly which code. The cost is that the topology's
  address — and therefore the emitted module's byte gate, and the
  committed addresses of every parent node — churns on EVERY edit to
  any source file the topology names. A whitespace fix in `Store.ts`
  moves `casSystem`'s address and turns `check:cas` red for a reason
  the topology has no opinion about;
- a MARKER: a file node carrying the specifier as its name, and nothing
  the emitter does not read. Its address is a function of the specifier
  alone, so it moves when the specifier moves and never otherwise.

**v0 takes the marker.** A byte gate that goes red for unrelated
reasons stops being read, and the emitter reads the name and only the
name — so full content would be provenance the generated artifact pays
for and never spends. The marker is honest about what it certifies:
WHICH MODULE, never WHICH BYTES.

**Full-content file nodes are the OPEN HALF of this ruling**, not a
rejected option. They want a source-ingestion step (the recipe-1 writer
over real file bytes, not `blobOfString`'s one-chunk clamp) and a
ruling on what a topology's address is allowed to depend on. Neither is
decided here, and neither should be decided silently by whichever form
a first implementation happened to pick. -/

/-- One file node the topology names: the address it resides at and the
module specifier its `name` carries. -/
structure FileRef where
  addr : Addr32
  spec : String

/-- The resolution table an emission is performed against. -/
abbrev Files := List FileRef

/-- The marker file node for a module specifier: the specifier as the
file's name, `text/plain`, over a one-chunk blob of the specifier's own
bytes. See the design decision above — this is the provenance-light
form, deliberately. -/
def markerFile (spec : String) : Cas.Grammar.Tree .file :=
  .file (Cas.Grammar.Name.utf8 spec) (Cas.Grammar.Name.utf8 "text/plain")
    (Cas.Grammar.blobOfString spec)

/-- A module specifier as the addressed file it resides at, under the
production digest. -/
def fileRef (spec : String) : FileRef :=
  { addr := (markerFile spec).address Cas.sha256Addr, spec := spec }

/-- The code reference naming `export` in the module `f` carries. -/
def codeRef (f : FileRef) («export» : String) : CodeRef :=
  { «export» := «export», file := ⟨f.addr⟩ }

/-- The module specifier a code reference names. `none` when its
address names no file in the table — the same refusal an unresolved
child address gets, paid at emission. -/
def specOf (fs : Files) (c : CodeRef) : Option String :=
  (fs.find? fun f => f.addr.val == c.file.addr.val).map (·.spec)

/-! ## Bindings — a topology as an ordered, addressed list -/

/-- One exported layer: the name it is exported under, its prose, the
system node it is, and the address that node resides at. -/
structure Binding where
  name : String
  doc : List String
  node : SystemNode
  addr : Addr32

/-- Bind one node to an exported name, computing its address. `none` is
the projection's own reserved-key refusal travelling out. -/
def bind (name : String) (doc : List String) (node : SystemNode) :
    Option Binding :=
  (systemAddressOf node).map fun addr =>
    { name := name, doc := doc, node := node, addr := addr }

/-! ## The residual fold -/

/-- What a node answers with, and what it still demands. Both lists are
deduplicated by key and sorted by key. -/
structure Residual where
  provides : List ServiceRef
  requires : List ServiceRef

private def hasKey (xs : List ServiceRef) (s : ServiceRef) : Bool :=
  xs.any fun x => x.key == s.key

private def dedup : List ServiceRef → List ServiceRef
  | [] => []
  | s :: rest =>
    let tail := dedup rest
    if hasKey tail s then tail else s :: tail

/-- The canonical spelling of a service SET: deduplicated by key, then
sorted by key. The residual fold has always used it; it is public
because the AUTHORING side needs the same function.

**CANON-1.** A system node's address is a function of the written term,
list order included, so `[a, b]` and `[b, a]` are two addresses for one
service set — and since the residual fold normalizes anyway, the two
emit identical TypeScript and answer identical Contexts. That is a
cache-hit defeater, not an untidiness: a plan keyed by address misses
on a term that means exactly what the hit meant. The fix is to spell
service sets canonically where they are AUTHORED, so the stored term is
already canonical; see `tools/EmitLayers.lean`. -/
def canonServices (xs : List ServiceRef) : List ServiceRef :=
  (dedup xs).mergeSort fun a b => decide (a.key ≤ b.key)

/-- Whether a list is already spelled canonically — the authoring-side
check, decided on keys because `ServiceRef` carries no `BEq`. -/
def isCanonServices (xs : List ServiceRef) : Bool :=
  xs.map (·.key) == (canonServices xs).map (·.key)

private def without (xs ys : List ServiceRef) : List ServiceRef :=
  xs.filter fun x => !hasKey ys x

private def residual (provides requires : List ServiceRef) : Residual :=
  { provides := canonServices provides, requires := canonServices requires }

/-- One resolved binding: its address, its exported name, its
residual. Built children-first, so a lookup never recurses. -/
abbrev Resolved := List (Addr32 × String × Residual)

private def find? (t : Resolved) (a : Addr32) : Option (String × Residual) :=
  (t.find? fun row => row.1.val == a.val).map (·.2)

/-- What a node answers with and demands, resolved against the
children already bound. -/
def residualOf (t : Resolved) : SystemNode → Option Residual
  | .service _ p r => some (residual [p] r)
  | .backing _ p r => some (residual p r)
  | .«opaque» _ _ p r => some (residual p r)
  | .fresh inner => (find? t inner.addr).map (·.2)
  | .merge parts => do
    let rows ← parts.mapM fun p => (find? t p.addr).map (·.2)
    pure (residual (rows.flatMap (·.provides)) (rows.flatMap (·.requires)))
  | .provide inner outer => do
    let ri ← (find? t inner.addr).map (·.2)
    let ro ← (find? t outer.addr).map (·.2)
    pure (residual ro.provides (ri.requires ++ without ro.requires ri.provides))
  | .provideMerge inner outer => do
    let ri ← (find? t inner.addr).map (·.2)
    let ro ← (find? t outer.addr).map (·.2)
    pure (residual (ro.provides ++ ri.provides)
      (ri.requires ++ without ro.requires ri.provides))

/-! ## The expression -/

private def nameAt (t : Resolved) (a : Addr32) : Option Ts.Expr :=
  (find? t a).map fun row => .ident row.1

/-- One arm, one call. A leaf is the bare constructor reference; every
edge is `Layer.<combinator>(…)` over the exported names of its
children. -/
def exprOf (t : Resolved) : SystemNode → Option Ts.Expr
  | .service c _ _ => some (.ident c.«export»)
  | .backing c _ _ => some (.ident c.«export»)
  | .«opaque» c _ _ _ => some (.ident c.«export»)
  | .fresh inner => do
    let i ← nameAt t inner.addr
    pure (.call (.ident "Layer.fresh") [i])
  | .merge parts => do
    let ps ← parts.mapM fun p => nameAt t p.addr
    pure (.call (.ident "Layer.mergeAll") ps)
  | .provide inner outer => do
    let i ← nameAt t inner.addr
    let o ← nameAt t outer.addr
    pure (.call (.ident "Layer.provide") [o, i])
  | .provideMerge inner outer => do
    let i ← nameAt t inner.addr
    let o ← nameAt t outer.addr
    pure (.call (.ident "Layer.provideMerge") [o, i])

/-! ## The declared type -/

private def qualified (name : String) :
    Cas.Schema.Foreign.TypeScript.QualifiedName :=
  match name.splitOn "." with
  | [] => ⟨[name], by simp⟩
  | part :: parts => ⟨part :: parts, by simp⟩

private def unionOf (xs : List ServiceRef) :
    Cas.Schema.Foreign.TypeScript.TypeExpr :=
  match xs with
  | [] => .never
  | [one] => .named (qualified one.name)
  | many => .union (many.map fun s => .named (qualified s.name))

/-- `Layer.Layer<ROut, E, RIn>` for a residual, through the hand-seeded
target row. The error channel is `never`: this fragment emits no
failing constructor. -/
def layerTypeOf (r : Residual) : String :=
  (LayerType.lower
    { provides := unionOf r.provides
    , requires := unionOf r.requires }).render

/-! ## The import list -/

private def rootOf (name : String) : String :=
  (name.splitOn ".").headD name

/-- Every (module, imported name) pair one node contributes. `none`
when the node's constructor names a file the table does not carry — a
topology cannot be emitted against a table that does not resolve it. -/
private def refsOf (fs : Files) : SystemNode → Option (List (String × String))
  | .service c p r => do
    let spec ← specOf fs c
    pure ((spec, rootOf c.«export») ::
      ((p :: r).map fun s => (s.path, rootOf s.name)))
  | .backing c p r => do
    let spec ← specOf fs c
    pure ((spec, rootOf c.«export») ::
      ((p ++ r).map fun s => (s.path, rootOf s.name)))
  | .«opaque» c _ p r => do
    let spec ← specOf fs c
    pure ((spec, rootOf c.«export») ::
      ((p ++ r).map fun s => (s.path, rootOf s.name)))
  | _ => some []

private def insertSorted (x : String) : List String → List String
  | [] => [x]
  | y :: ys =>
    if x == y then y :: ys
    else if x < y then x :: y :: ys
    else y :: insertSorted x ys

private def addRef :
    List (String × List String) → String × String →
      List (String × List String)
  | [], (path, name) => [(path, [name])]
  | (p, ns) :: rest, (path, name) =>
    if p == path then (p, insertSorted name ns) :: rest
    else (p, ns) :: addRef rest (path, name)

/-- Every module the topology names, with the names it takes from it —
paths and names both sorted, so the header is a function of the
description and the file table alone. `Layer` from `effect` is always
taken: every emitted module declares layer types even when it emits no
edge. `none` when a constructor's file address resolves to nothing. -/
def importsOf (fs : Files) (bs : List Binding) : Option (List Ts.Import) := do
  let perNode ← bs.mapM fun b => refsOf fs b.node
  let pairs := ("effect", "Layer") :: perNode.flatten
  let grouped := pairs.foldl addRef []
  let sorted := grouped.mergeSort fun a b => decide (a.1 ≤ b.1)
  pure (sorted.map fun (path, names) => .named names path)

/-! ## The module -/

/-- The resolved table for a binding list, children-first. `none` when
a child address names nothing already bound — which is the acyclicity
check, paid for by the ordering rather than by a traversal. -/
def resolveAll (bs : List Binding) : Option Resolved :=
  bs.foldlM (init := ([] : Resolved)) fun t b => do
    let r ← residualOf t b.node
    pure (t ++ [(b.addr, b.name, r)])

/-- One exported layer: its prose, its derived type, its expression. -/
def declOf (t : Resolved) (b : Binding) : Option Ts.Decl := do
  let e ← exprOf t b.node
  let row ← find? t b.addr
  pure (.const
    { doc := b.doc
    , name := b.name
    , value := e
    , type := some (layerTypeOf row.2) })

/-- The differential's own table: every REQUIREMENT-FREE binding beside
the key set the topology says it answers with. A layer that still
demands services cannot be built without provision, so it is exported
as a const and left out of the table — the gate covers what it can
actually run.

Each row also carries the topology's own CONTENT ADDRESS. A generated
projection that does not name the term it projects cannot be checked
against it, and the address is the only name a description has; it is
also what makes a stored topology nameable from the host at all, which
is what an annotation on the system plane needs. The differential reads
`name`/`keys`/`layer` and ignores it. -/
def tableDecl (t : Resolved) (bs : List Binding) : Ts.Decl :=
  let rows := bs.filterMap fun b =>
    match find? t b.addr with
    | some (name, r) =>
      if r.requires.isEmpty then
        some (Ts.Expr.objectML [
          ("name", .str name),
          ("address", .str (Cas.hexS b.addr.val)),
          ("keys", .arr (r.provides.map fun s => .str s.key)),
          ("layer", .ident name)])
      else none
    | none => none
  .const {
    doc := ["Every requirement-free topology beside the service keys it",
            "declares and the address it resides at — what the",
            "Context-key-set differential compares."]
    name := "topology"
    value := .arr rows }

/-- The whole generated module: header, derived imports, one exported
const per binding, and the differential's table. The file table is what
turns each constructor's addressed module back into a specifier. -/
def emitModule (header : List String) (fs : Files) (bs : List Binding) :
    Option Ts.Module := do
  let t ← resolveAll bs
  let decls ← bs.mapM (declOf t)
  let imports ← importsOf fs bs
  pure { header := header, imports := imports,
         decls := decls ++ [tableDecl t bs] }

end Cas.Backend
