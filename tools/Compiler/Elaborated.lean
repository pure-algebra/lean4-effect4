import Lean.Elab.Term
import Effect4.Machine.Key

/-!
# Compiler.Elaborated — what an executable knows of its own elaboration

A project's executable calls `Compiler.main` by static import (decision E1), so at run time the
application is a value: the Lean modules and names it came from are gone. Two facts of the
executable's environment are read where they are known: when the module that calls
`Compiler.main` or `Compiler.mainOver` is elaborated. They are kept in the executable as data
(`elaborated%`, the default of the two functions' `elaborated` argument), so a project's
`Main.lean` passes nothing.

- **The import closure** (`modules`): the module being elaborated, and every module it imports,
  directly or not, except the toolchain's own: a module whose `.olean` the toolchain ships
  (`Init`, `Std`, `Lean`, `Lake`, …). Each by its name, in byte order. The manifest hashes their
  sources at run time (`Compiler.readInputs`), and `inputs.address` is the address of those
  hashes (`Compiler.Inputs.address`).
- **The declared names of service keys** (`keys`): each declaration of the closure whose type is
  `ServiceKey` and whose value is a literal key `⟨⟨n⟩, ⟨c⟩⟩`, with its name. `check` prints a
  service's key with its declared names beside its spelling: `Todo.repoKey` beside `k30_6`
  (`Elaborated.namesOf`). A key stated by any other value is not read. The names are metadata:
  no certificate holds them, and no artifact.
-/

namespace Compiler

open Lean Elab Term Meta

/-- **What an executable knows of its own elaboration** (`elaborated%`): its import closure
outside the toolchain, and the declared names of the literal service keys in that closure. -/
structure Elaborated where
  /-- the module being elaborated and every module it imports outside the toolchain, by name, in
  byte order -/
  modules : List String := []
  /-- each literal service key that a declaration of the closure states: the key's name, its
  code, and the declaration's name; in byte order of the declarations' names -/
  keys : List (Nat × Nat × String) := []
  deriving Inhabited

/-- **The declared names of a key**, in byte order: every declaration of the closure that states
it as a literal. -/
def Elaborated.namesOf (e : Elaborated) (key : Effect4.ServiceKey) : List String :=
  e.keys.filterMap fun (name, code, declared) =>
    if name == key.name.value && code == key.service.value then some declared else none

/-- A natural number literal: `OfNat.ofNat n` at a raw literal, or a raw literal. -/
def natOf? (e : Expr) : Option Nat := e.nat? <|> e.rawNatLit?

/-- **The name and the code of a literal key** `⟨⟨n⟩, ⟨c⟩⟩`, as a declaration's value states
them; `none` for any other value. -/
def literalKey? (e : Expr) : Option (Nat × Nat) :=
  match e.getAppFn.constName?, e.getAppArgs.toList with
  | some ``Effect4.ServiceKey.mk, [name, code] =>
    match name.getAppFn.constName?, name.getAppArgs.toList, code.getAppFn.constName?,
        code.getAppArgs.toList with
    | some ``Effect4.ServiceName.mk, [n], some ``Effect4.ServiceTypeCode.mk, [c] =>
      match natOf? n, natOf? c with
      | some n, some c => some (n, c)
      | _, _ => none
    | _, _, _, _ => none
  | _, _ => none

/-- A declaration's literal key, with the declaration's name: its type is `ServiceKey`, and its
value states a literal key. -/
def keyOf (c : ConstantInfo) : Option (Nat × Nat × String) :=
  if c.type == Lean.mkConst ``Effect4.ServiceKey then
    (c.value?.bind literalKey?).map fun (n, k) => (n, k, c.name.toString)
  else none

/-- **`elaborated%`**: the elaborating module's environment, read as `Elaborated`. The closure is
the environment's header: the module itself, then every imported module whose `.olean` the
toolchain does not ship (`Lean.getLibDir` of the running toolchain). The keys are read off the
declarations of those modules, and off the module's own declarations so far. -/
elab "elaborated%" : term => do
  let env ← getEnv
  let toolchain ← getLibDir (← getBuildDir)
  let mut modules : Array String := #[env.mainModule.toString]
  let mut keys : Array (Nat × Nat × String) := #[]
  for h : i in [0:env.header.modules.size] do
    let m := env.header.modules[i].module
    unless ← (modToFilePath toolchain m "olean").pathExists do
      modules := modules.push m.toString
      if let some data := env.header.moduleData[i]? then
        keys := keys ++ data.constants.filterMap keyOf
  keys := keys ++ (env.constants.map₂.toList.filterMap fun (_, c) => keyOf c).toArray
  let sorted := modules.qsort (· < ·)
  let keyed := keys.qsort fun a b => a.2.2 < b.2.2
  return mkApp2 (Lean.mkConst ``Elaborated.mk) (toExpr sorted.toList) (toExpr keyed.toList)

end Compiler
