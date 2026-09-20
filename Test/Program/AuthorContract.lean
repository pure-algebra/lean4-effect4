import Effect4.Api.Author
import Effect4.Laws.Program.Author
import Effect4.Codegen.Authoring.Forms
import Effect4.Laws.Program.Authoring.Forms
import Test.Program.LayerSharingContract

/-!
# Author contract — a module declares what it needs, and one call builds it

`Test/Program/AuthoringContract.lean` pins the lifts: a program written by name elaborates to
the tree an author would otherwise count out. This battery pins the layer above it, the one a
real application writes: rows declared under their spelling and called by it, services
declared with their carrier, layers checked before any program provides them, and one call
from the module to the value a run needs.

Three programs end to end. **E1** is the layer-sharing battery's own `once`, written in the
new surface: two service declarations, one layer, the layer used twice. It elaborates to
exactly the tree `Test/Program/LayerSharingContract.lean` certifies, so the new surface is
held to a program the runtime already proves things about. **E2** is a package operation: the
rc.112 key-value store's shipped table installed as a package, its rows called by spelling,
and no table position written anywhere. **E3** is a two-service deployment whose sibling
mistake — a merge where a `provideMerge` was meant — is caught by `Api.checkLayer` before a
program exists.

Then B-9: a name the surface mints for itself is reserved, `var` refuses it, and a binder
minted through `Env.mint` cannot be captured. The red control is pinned beside the fix: the
generated forms still mint a constant spelling, so the bug is reachable through them until
their generator mints through `Env.mint` too.
-/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Test.Program.AuthorContract

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Api (Val)
open TypeScript (house0)
open TypeScript.Render (expr)

/-! ## E1 — a service, the layer that builds it, and the layer used twice

`Test/Program/LayerSharingContract.lean` writes this program by level, against two service
keys spelled as pairs of numbers. Here the two keys are declared once with the carrier the
signature types them at, and the program reads like the language. -/

/-- The counter service: its key, and the carrier the signature types that key at. -/
def Counter : ServiceDef := { key := ⟨⟨4⟩, ⟨4⟩⟩, carrier := .nat }

/-- The cell the counter counts in. -/
def TheRef : ServiceDef := { key := ⟨⟨6⟩, ⟨7⟩⟩, carrier := NativeOp.refTy }

-- The declarations and the signature say the same thing, decided at the declaration site.
#guard Counter.Agrees (nativeSignature) && TheRef.Agrees (nativeSignature)
#guard ServiceDef.Agrees (nativeSignature) { key := Counter.key, carrier := .string } = false

/-- The layer that builds the counter: it takes the cell, bumps it, and provides `5`. -/
def counter : LayerSrc NativeOp := Counter.layer <| eff do
  let ref ← TheRef.use
  Ref.update .incr ref
  return 5

/-- The whole application: the cell provided as a value, the counter layer used twice by
name, and the cell read at the end. -/
def once : Module NativeOp :=
  { services := [Counter, TheRef]
    layers := [("Counter", counter)]
    main := eff do
      let r ← Ref.make 0
      TheRef.give r <| eff do
        _ ← provide (Layer.ref "Counter") (provide (Layer.ref "Counter") Counter.use)
        Ref.get r }

/-- The same, with a third use. -/
def twice : Module NativeOp :=
  { services := [Counter, TheRef]
    layers := [("Counter", counter)]
    main := eff do
      let r ← Ref.make 0
      TheRef.give r <| eff do
        _ ← provide (Layer.ref "Counter")
          (provide (Layer.ref "Counter") (provide (Layer.ref "Counter") Counter.use))
        Ref.get r }

-- The new surface elaborates to the trees the layer-sharing battery certifies, reference
-- target and all.
#guard elaborateModule once = .ok Test.Program.LayerSharingContract.once
#guard elaborateModule twice = .ok Test.Program.LayerSharingContract.twice

-- One call: elaborated, table assembled, typed, admitted.
#guard (Effect4.Api.Author.build once).toOption.map (fun b => b.ty.answer) = some .nat
#guard (Effect4.Api.Author.build once).toOption.map (fun b => b.closed) = some true
#guard (Effect4.Api.Author.build once).toOption.map (fun b => b.table.length) = some 0
#guard (Effect4.Api.Author.build once).toOption.map (fun b => b.runSync) = some (Exit.success (Val.nat 1))
#guard (Effect4.Api.Author.build twice).toOption.map (fun b => b.runSync) = some (Exit.success (Val.nat 1))

-- The layer is checked on its own, before a program provides it: it provides the counter and
-- still needs the cell.
#guard (Effect4.Api.checkLayer counter).toOption.map (fun l => (l.provides, l.requires, l.closed))
  = some ([Counter.key], [TheRef.key], false)

-- And it prints on its own.
#guard (Effect4.Api.checkLayer counter).toOption.map (fun l => l.print.map (expr house0 0))
  = some (.ok "Layer.effect(Context.Service<number>(\"k4_4\"), Effect.flatMap(Effect.service(Context.Service<Ref.Ref<number>>(\"k6_7\")), (a0) => Effect.flatMap(Ref.update(a0, incr), (a1) => Effect.succeed(5))))")

theorem counter_scoped : LayerSrc.Scoped counter := by
  unfold counter; authoring_scoped

/-! ## E2 — a package operation, with no table position written anywhere

The rc.112 in-memory key-value store ships as a `RowTable` (`Program/Packages`). Installed as
a package, its rows are declared under their spellings, and a call resolves the spelling to
the position the module's own table gave it. Before this an author wrote `perform (.external
1)` and had to know that `1` was `get` in whichever table they would later pass to `Api.check`. -/

def kv : Package := Package.ofRows "kv" Packages.keyValueStoreMemory

def readKey : Module NativeOp := Package.install [kv]
  { main := eff do
      let store ← Row.call (kv.op "Kv.make") unit
      Row.call (kv.op "get") (app "pair" [store, str "greeting"]) }

#guard readKey.rowNames = [("Kv.make", 0), ("get", 1), ("set", 2), ("remove", 3), ("has", 4)]
#guard readKey.table = Packages.keyValueStoreMemory

#guard elaborateModule readKey
  = .ok (.bind (.perform (.external 0) (.lit .unit))
      (.perform (.external 1)
        (.app "pair" (.cons (.var 0) (.cons (.lit (.str "greeting")) .nil)))))

#guard (Effect4.Api.Author.build readKey).toOption.map (fun b => b.ty.answer) = some (.option .string)
#guard (Effect4.Api.Author.build readKey).toOption.map (fun b => b.positionOf "get") = some (some 1)
#guard (Effect4.Api.Author.build readKey).toOption.map (fun b => b.table.length) = some 5

-- A row the module never declared refuses at its call site, by the spelling it was called
-- under; before, a wrong position typed as some other row or fell off the table.
#guard elaborateModule
    ({ main := Row.call (Row.host "Kv.missing" .unit .unit) unit } : Module NativeOp)
  = .error ⟨[], .unboundRow "Kv.missing"⟩
#guard elaborateModule ({ main := Row.call (kv.op "nosuch") unit } : Module NativeOp)
  = .error ⟨[], .unboundRow "nosuch"⟩

-- Two rows under one spelling refuse: a table key is the spelling and the trailing names.
#guard elaborateModule
    ({ rows := [Row.host "twice" .unit .unit, Row.host "twice" .nat .nat]
       main := succeed unit } : Module NativeOp)
  = .error ⟨[], .duplicateRow "twice"⟩

-- O-11 decided on this module's own declarations: the three conditions `Table.lawful` checks.
#guard Table.lawful readKey.table
#guard RowDef.duplicate? readKey.rowDefs = none
#guard checkTable readKey.table = none

/-! ## E3 — a two-service deployment, and the sibling mistake caught before a program exists

`merge` gives two layers to the surroundings side by side; `provideMerge` gives one to the
other and both to the surroundings. Written by level against a private alphabet, the
difference showed up only when a whole application was typed. Now the deployment is a value
with a signature, and the mistake is the one whose requirement row is not empty. -/

def Db : ServiceDef := { key := ⟨⟨10⟩, ⟨4⟩⟩, carrier := .nat }
def Rate : ServiceDef := { key := ⟨⟨11⟩, ⟨4⟩⟩, carrier := .nat }
def DbEnv : ServiceDef := { key := ⟨⟨20⟩, ⟨4⟩⟩, carrier := .nat }
def RateEnv : ServiceDef := { key := ⟨⟨21⟩, ⟨4⟩⟩, carrier := .nat }

#guard [Db, Rate, DbEnv, RateEnv].all (ServiceDef.Agrees (nativeSignature))

/-- The two services, each built from its own configuration binding. -/
def services : LayerSrc NativeOp :=
  Layer.mergeAll [ Db.layer (eff do let e ← DbEnv.use; succeed e)
            , Rate.layer (eff do let e ← RateEnv.use; succeed e) ]

/-- The configuration bindings. -/
def bindings : LayerSrc NativeOp :=
  Layer.mergeAll [ DbEnv.constant (nat 1), RateEnv.constant (nat 2) ]

/-- The deployment: the bindings feed the services, and both reach the surroundings. -/
def deployment : LayerSrc NativeOp := Layer.provideMerge services bindings

/-- The mistake: siblings, so nothing feeds anything. -/
def siblingMistake : LayerSrc NativeOp := Layer.merge services bindings

#guard (Effect4.Api.checkLayer services).toOption.map (fun l => (l.provides, l.requires))
  = some ([Db.key, Rate.key], [DbEnv.key, RateEnv.key])

#guard (Effect4.Api.checkLayer deployment).toOption.map (fun l => (l.provides, l.requires, l.closed))
  = some ([Db.key, Rate.key, DbEnv.key, RateEnv.key], [], true)

-- The sibling mistake provides the same four keys and is NOT closed: it still asks for the
-- two bindings it also provides, because a merge gives nothing to a sibling.
#guard (Effect4.Api.checkLayer siblingMistake).toOption.map (fun l => (l.provides, l.requires, l.closed))
  = some ([Db.key, Rate.key, DbEnv.key, RateEnv.key], [DbEnv.key, RateEnv.key], false)

/-- The program that uses both services, with no layer in sight. -/
def handler : Src NativeOp := eff do
  let db ← Db.use
  let rl ← Rate.use
  succeed (app "pair" [db, rl])

-- A program's environment, as data.
#guard (Effect4.Api.author handler).toOption.map Effect4.Api.Typed.requires = some [Db.key, Rate.key]
#guard (Effect4.Api.author handler).toOption.map Effect4.Api.Typed.closed = some false

-- Deployed under the correct layer, the program is closed; under the mistake it is not.
#guard (Effect4.Api.author (provide deployment handler)).toOption.map Effect4.Api.Typed.closed = some true
#guard (Effect4.Api.author (provide siblingMistake handler)).toOption.map Effect4.Api.Typed.requires
  = some [DbEnv.key, RateEnv.key]

-- The deployed program with no declarations of its own: one call, one built value.
#guard (Effect4.Api.Author.program (provide deployment handler)).toOption.map (fun b => b.closed)
  = some true
#guard (Effect4.Api.Author.program (provide deployment handler)).toOption.map
    (fun b => b.runSync) = some (Exit.success (Val.list [Val.nat 1, Val.nat 2]))

-- The carriers a module declares, in the shape the signature's service table reads.
#guard ({ services := [Db, Rate], main := succeed unit } : Module NativeOp).serviceTypes
  = [(Db.key, Ty.nat), (Rate.key, Ty.nat)]

theorem deployment_scoped : LayerSrc.Scoped deployment := by
  unfold deployment services bindings; authoring_scoped

theorem handler_scoped : Src.Scoped handler := by
  unfold handler; authoring_scoped

/-! ## The fiber words, and the daemon flag at the call site -/

/-- A child fiber, joined. -/
def forked : Src NativeOp := eff do
  let f ← fork (succeed (nat 1))
  join f

/-- A child that outlives its parent. The word that detaches it is at the call site. -/
def detached : Src NativeOp := eff do
  let f ← daemon (succeed (nat 1))
  join f

/-- The same, owned by a scope rather than by the parent. -/
def detachedInScope : Src NativeOp := eff do
  let s ← Scope.make .sequential
  daemon (succeed (nat 1)) in s

#guard elaborate forked
  = .ok (.bind (.withFiber (.fork (.succeed (.lit (.nat 1))) childOptions))
      (.awaitFiber (.var 0) .joinEffect))
#guard elaborate detached
  = .ok (.bind (.withFiber (.fork (.succeed (.lit (.nat 1))) daemonOptions))
      (.awaitFiber (.var 0) .joinEffect))
#guard elaborate detachedInScope
  = .ok (.bind (.perform (.scopeMake .sequential) (.lit .unit))
      (.withFiber (.forkIn (.succeed (.lit (.nat 1))) daemonOptions (.var 0))))
#guard (elaborate forked).toOption.map Effect4.Api.wellTyped = some true
#guard (elaborate detached).toOption.map Effect4.Api.wellTyped = some true
#guard (elaborate detachedInScope).toOption.map Effect4.Api.wellTyped = some true

theorem forked_scoped : Src.Scoped forked := by unfold forked; authoring_scoped
theorem detached_scoped : Src.Scoped detached := by unfold detached; authoring_scoped
theorem detachedInScope_scoped : Src.Scoped detachedInScope := by
  unfold detachedInScope; authoring_scoped

/-! ## The layer words -/

#guard elaborateLayer (Layer.value Counter.key (nat 5) : LayerSrc NativeOp)
  = .ok (.effect Counter.key (.succeed (.lit (.nat 5))))
-- what `Layer.succeed` cannot take: a string is outside the value alphabet its literal
-- argument is admitted at, so a string-valued service is the layer whose body answers it.
#guard Program.layerTy (nativeSignature) (.succeed Counter.key (.str "x")) = none
#guard (Effect4.Api.checkLayer (Layer.value Counter.key (str "x"))).toOption.map
    (fun l => l.provides) = some [Counter.key]
#guard elaborateLayer (Layer.empty : LayerSrc NativeOp)
  = .ok (.effectDiscard (.succeed (.lit .unit)))
#guard (Effect4.Api.checkLayer (Layer.empty : LayerSrc NativeOp)).toOption.map
    (fun l => (l.provides, l.requires)) = some ([], [])

/-! ## An application's own service carriers

`nativeServiceTy` spells six carriers by type code, and an application with a seventh had to
squeeze into one of them. A supplied service table is threaded exactly as the supplied row
table is, and the empty one is the signature as it was. -/

#guard (nativeSignature).serviceTy ⟨⟨12⟩, ⟨12⟩⟩ = none
#guard (nativeSignatureWith [] [(⟨⟨12⟩, ⟨12⟩⟩, .string)]).serviceTy ⟨⟨12⟩, ⟨12⟩⟩ = some .string
#guard (nativeSignatureWith [] []).serviceTy Counter.key = (nativeSignature).serviceTy Counter.key

/-- A service the six type codes do not spell, checked under the supplied table. -/
def Greeting : ServiceDef := { key := ⟨⟨12⟩, ⟨12⟩⟩, carrier := .string }

#guard ServiceDef.Agrees (nativeSignature) Greeting = false
#guard ServiceDef.Agrees (nativeSignatureWith [] [(Greeting.key, Greeting.carrier)]) Greeting

#guard (Effect4.Api.checkLayer (Greeting.constant (str "hello")) []
    (nativeSignatureWith [] [(Greeting.key, Greeting.carrier)])).toOption.map
    (fun l => (l.provides, l.closed)) = some ([Greeting.key], true)

/-! ## B-9 — a name the surface minted cannot be captured

`Names.resolve` answers the last binding of a name. A convenience that binds a fixed spelling
and is then handed that spelling as its own argument binds the wrong variable, and the result
is scoped, types and runs: the one silently wrong program the named surface was built to
remove was still reachable.

The rule: a minted name begins with `reservedPrefix`, which `var` refuses, so an author
cannot write one; and it carries the level it is bound at (`Env.mint`), so two mints in one
scope are two names. `var_push_minted` (`Laws/Program/Author.lean`) is why that is enough. -/

#guard reservedPrefix = "_%"
#guard Name.reserved "_%answer1" = true
#guard Name.reserved "_answer1" = false
#guard Name.reserved "r" = false
#guard Env.mint { names := ["a", "b"] } "answer" = "_%answer2"
#guard Name.reserved (Env.mint { names := ["a", "b"] } "answer") = true

-- An author who writes a reserved name is refused at the site, with the name.
#guard elaborate (Ref.get (var "_%r") : Src NativeOp) = .error ⟨[], .reservedName "_%r"⟩
#guard elaborate (bind "x" (Ref.make (nat 0)) (Ref.get (var "_%x")) : Src NativeOp)
  = .error ⟨[1], .reservedName "_%x"⟩
#guard elaborate
    (Forms.tapContinuation "_%answer1" (succeed (nat 1)) (succeed (nat 2)) : Src NativeOp)
  = .error ⟨[1, 1], .reservedName "_%answer1"⟩

-- RED CONTROL, B-9 still open in the generated forms: `Forms.tapContinuation` mints the
-- constant `"_answer1"` (`Authoring/Forms.lean`, generated from `Codegen.Forms.all`), so an
-- author who names their own answer `"_answer1"` reads the continuation's answer instead of
-- their own — `.var 1` where they meant `.var 0`. Owed: the forms generator mints through
-- `Env.mint` and reads through `minted`, as the expansion below does.
#guard elaborate
    (Forms.tapContinuation "_answer1" (succeed (nat 1)) (succeed (nat 2)) : Src NativeOp)
  = .ok (.bind (.succeed (.lit (.nat 1)))
      (.bind (.succeed (.lit (.nat 2))) (.succeed (.var 1))))

/-- `Effect.tap`'s expansion with the continuation's binder minted instead of spelled: the
shape `Codegen/Forms` pins, with `"_answer1"` replaced by `Env.mint "answer"`. This is what
the forms generator must emit. -/
def tapMinted (answer : String) (effect continuation : Src NativeOp) : Src NativeOp :=
  fun env p =>
    bind answer effect
      (fun env' p' => bind (env'.mint "answer") continuation (succeed (var answer)) env' p')
      env p

-- THE FIX: the same author name, and the author's own variable.
#guard elaborate (tapMinted "_answer1" (succeed (nat 1)) (succeed (nat 2)))
  = .ok (.bind (.succeed (.lit (.nat 1)))
      (.bind (.succeed (.lit (.nat 2))) (.succeed (.var 0))))
-- and any other name behaves as it did.
#guard elaborate (tapMinted "r" (succeed (nat 1)) (succeed (nat 2)))
  = elaborate (Forms.tapContinuation "r" (succeed (nat 1)) (succeed (nat 2)) : Src NativeOp)

/-! ## Scope safety of the new surface, and the axioms every proof reaches -/

#guard (elaborateModule once).toOption.map (Eff.scopedAt 0) = some true
#guard (elaborateModule readKey).toOption.map (Eff.scopedAt 0) = some true
#guard (elaborate handler).toOption.map (Eff.scopedAt 0) = some true
#guard (elaborate detachedInScope).toOption.map (Eff.scopedAt 0) = some true

#print axioms counter_scoped
#print axioms deployment_scoped
#print axioms handler_scoped
#print axioms forked_scoped
#print axioms detached_scoped
#print axioms detachedInScope_scoped
#print axioms Effect4.Program.Authoring.Row.call_scoped
#print axioms Effect4.Program.Authoring.build_table_lawful
#print axioms Effect4.Program.Authoring.build_rows_resolve
#print axioms Effect4.Program.Authoring.var_push_minted
#print axioms Effect4.Program.Authoring.var_reserved
#print axioms Effect4.Program.Authoring.ServiceDef.carrier_unique
#print axioms Effect4.Program.Authoring.build_lawful
#print axioms Effect4.Program.Authoring.build_runnable
#print axioms Effect4.Api.Author.build
#print axioms Effect4.Program.Authoring.Row.call
#print axioms Effect4.Program.Authoring.elaborateModule
#print axioms Effect4.Program.nativeSignatureWith_nil

end Test.Program.AuthorContract
