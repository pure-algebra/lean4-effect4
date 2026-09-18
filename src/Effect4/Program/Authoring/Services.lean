import Effect4.Program.Authoring.Sugar

/-!
# Program.Authoring.Services — services, packages and layers, written as words

The records are in `Program/Authoring.lean`, because `Module` holds them; this module is
every operation over them, and it adds no constructor, no wire tag and no printed shape.
Each definition is a Lean function over the generated lifts, so what a program means and
prints has one owner.

* A **service** is a key, the carrier the signature types it at, and the operations that may
  be performed on a value of that carrier. `Agrees` decides at a declaration site that the
  declaration and the signature say the same thing, and `carrier_unique`
  (`Laws/Program/Author.lean`) is why two declarations of one key cannot disagree.
  `use`, `give`, `layer` and `constant` are the four things an author does with one.
* A **package** is a block of rows and services installed as one unit. `install` puts them
  into a module, and `Row.call` resolves a row by its spelling, so an author never writes a
  table position.
* The **layer** words are the rc.112 spellings we had no name for: `Layer.value` (a layer
  over a value that is not a literal, `Layer.ts:1191`), `Layer.empty` (`:1155`), `Layer.all`
  (`mergeAll`, `:1652`), `with_` and `provideAll` (`Effect.provide`), `provideFresh`
  (`{ local: true }`).
* The **fiber** words are `fork`, `daemon`, `daemonIn` and `join`. The daemon flag is a word
  at the call site: a child that outlives its parent is spelled `daemon body`, never a
  boolean set inside an options record two lines away.
* `nativeSignatureWith` is the native signature with an application's own service carriers in
  front of the six the type codes spell. It is here and not beside `nativeSignature`
  (`Program/Native.lean`) so that no existing signature, byte or proof moves: at the empty
  table the two are the same value, `rfl`.
-/

set_option autoImplicit false

namespace Effect4.Program

open Effect4 (ServiceKey)

/-- The native signature's service table with an application's own carriers in front. A key
the application declares is typed at the carrier it declared; every other key is typed as
before — the reserved `Scope`, nothing under the machine's own names, and otherwise the
carrier the type code spells (`nativeServiceTy`). -/
def nativeServiceTyWith (services : List (ServiceKey × Ty)) (key : ServiceKey) : Option Ty :=
  match services.find? (fun entry => entry.1 == key) with
  | some (_, ty) => some ty
  | none => nativeServiceTy key

/-- The native signature over a supplied row table and a supplied service table. The service
table is threaded exactly as the row table is, and is empty by default. -/
def nativeSignatureWith (table : RowTable := []) (services : List (ServiceKey × Ty) := []) :
    Signature NativeOp :=
  { nativeSignature table with serviceTy := nativeServiceTyWith services }

/-- No supplied service carriers is the signature as it was: the six the type codes spell. -/
theorem nativeSignatureWith_nil (table : RowTable) :
    nativeSignatureWith table [] = nativeSignature table := rfl

namespace Authoring

open Effect4.Program

/-! ## Services -/

namespace ServiceDef

/-- The carrier an operation is spelled on: the first component of its request, which is the
receiver (`RowShape.method`, `Program/Eff.lean`). An operation whose request is the receiver
alone is spelled on it too. -/
def receiver (r : RowDef) : Ty :=
  match r.row.request.normalize with
  | .prod recv _ => recv
  | t => t

/-- The declaration and the signature say the same thing: the key is typed at the carrier
that was declared, and every operation is spelled on a value of that carrier. Decidable, so
an author pins it with one `#guard` at the declaration site. -/
def Agrees {Op : Type} (sig : Signature Op) (s : ServiceDef) : Bool :=
  (sig.serviceTy s.key == some s.carrier)
    && s.ops.all (fun r => receiver r == s.carrier.normalize)

/-- `yield* Db` — the service's value. -/
def use {Op : Type} (s : ServiceDef) : Src Op := Authoring.service s.key

/-- `Effect.provideService(body, Db, value)` — the service bound to a value for one body. -/
def give {Op : Type} (s : ServiceDef) (value : TermSrc) (body : Src Op) : Src Op :=
  Authoring.provideService s.key value body

/-- `Layer.effect(Db, build)` — the layer that builds this service. -/
def layer {Op : Type} (s : ServiceDef) (build : Src Op) : LayerSrc Op :=
  Authoring.Layer.effect s.key build

end ServiceDef

/-! ## Layers -/

/-- `Layer.sync(key, value)` (`Layer.ts:1191`), and the `Layer.succeed` a string can take:
the constructor takes a literal the value alphabet admits, and a string is not one
(`PROV-FB-STRING-VALUE`), so a layer over a value is the layer whose body answers it. The
body is closed, so `value` is a literal or an atom over literals. -/
def Layer.value {Op : Type} (key : ServiceKey) (value : TermSrc) : LayerSrc Op :=
  Layer.effect key (Authoring.succeed value)

/-- `Layer.empty` (`Layer.ts:1155`): it provides nothing and requires nothing. -/
def Layer.empty {Op : Type} : LayerSrc Op :=
  Layer.effectDiscard (Authoring.succeed Authoring.unit)

/-- `Layer.mergeAll(...)` (`Layer.ts:1652`): several layers as siblings, one build. A sibling
provides nothing to a sibling (`merge_requires`, `Program/Provision.lean`). -/
def Layer.all {Op : Type} (layers : List (LayerSrc Op)) : LayerSrc Op := Layer.mergeAll layers

/-- `Layer.succeed(key, value)` for a service already in hand. -/
def ServiceDef.constant {Op : Type} (s : ServiceDef) (value : TermSrc) : LayerSrc Op :=
  Layer.value s.key value

/-- `Effect.provide(body, layer)` — the layer built for this body and nothing else. -/
def with_ {Op : Type} (layer : LayerSrc Op) (body : Src Op) : Src Op :=
  provideLayer layer false body

/-- `Effect.provide(body, [l₁, …, lₙ])` — several layers at one site. -/
def provideAll {Op : Type} (layers : List (LayerSrc Op)) (body : Src Op) : Src Op :=
  provideLayer (Layer.all layers) false body

/-- `Effect.provide(body, layer, { local: true })` — a build of its own, not the shared one. -/
def provideFresh {Op : Type} (layer : LayerSrc Op) (body : Src Op) : Src Op :=
  provideLayer layer true body

/-! ## Fibers

The daemon flag is a word at the call site. `ForkOptions` (`Machine/Supervision.lean`) carries
it as a field, and a field set two lines from the body it detaches is exactly the reading
mistake the word removes. -/

/-- A child started at once, supervised by its parent, inheriting its mask. -/
def childOptions : Effect4.Supervision.ForkOptions :=
  { startImmediately := true, daemon := false, maskMode := .inherit }

/-- The same child, detached: it outlives the fiber that forked it. -/
def daemonOptions : Effect4.Supervision.ForkOptions :=
  { startImmediately := true, daemon := true, maskMode := .inherit }

/-- `Effect.fork(body)` — a child fiber, supervised by its parent. Answers the fiber. -/
def fork {Op : Type} (body : Src Op) (options : Effect4.Supervision.ForkOptions := childOptions) :
    Src Op :=
  withFiber (Action.fork body options)

/-- `Effect.forkDaemon(body)` — a child that outlives its parent. Answers the fiber. -/
def daemonFork {Op : Type} (body : Src Op) : Src Op :=
  withFiber (Action.fork body daemonOptions)

/-- `Effect.forkIn(body, scope)` — a detached child owned by a scope, not by its parent. -/
def daemonForkIn {Op : Type} (body : Src Op) (scope : TermSrc) : Src Op :=
  withFiber (Action.forkIn body daemonOptions scope)

/-- `daemon body` and `daemon body in scope`: the two detaching forks, with the word that
detaches them at the call site. -/
syntax (name := daemonFork_) "daemon " term (" in " term)? : term

macro_rules
  | `(daemon $body:term) => `(daemonFork $body)
  | `(daemon $body:term in $scope:term) => `(daemonForkIn $body $scope)

/-- `Fiber.await(f)` — the child's exit, whatever it is. -/
def await {Op : Type} (fiber : TermSrc) : Src Op := awaitFiber fiber .awaitValue

/-- `Fiber.join(f)` — the child's answer, its failure raised in the joiner. -/
def join {Op : Type} (fiber : TermSrc) : Src Op := awaitFiber fiber .joinEffect

/-! ## Packages -/

namespace Package

/-- An existing row table as a package: the rows a host library offers, in their order. -/
def ofRows (name : String) (rows : RowTable) : Package :=
  { name := name, rows := rows.map RowDef.mk }

/-- The rows a list of packages offers, in package order. -/
def rowsOf (ps : List Package) : List RowDef := ps.flatMap (·.rows)

/-- The services a list of packages declares, in package order. -/
def servicesOf (ps : List Package) : List ServiceDef := ps.flatMap (·.services)

/-- Install packages into a module: their rows and services come first, then the module's
own. Positions are never written by an author, so which comes first only fixes the table. -/
def install {Op : Type} (ps : List Package) (m : Module Op) : Module Op :=
  { m with rows := rowsOf ps ++ m.rows, services := servicesOf ps ++ m.services }

end Package

end Authoring

end Effect4.Program
