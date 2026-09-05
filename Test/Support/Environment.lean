import Lean

/-! Battery-side declaration ownership. The axiom gate retains an independent lookup. -/
namespace Test.Support.Environment
open Lean Meta Elab Command

def failJoin (label : String) (detail : MessageData) : CommandElabM α :=
  throwError m!"{label}: {detail}"

def declarationOwner? (environment : Environment) (name : Name) : Option Name := do
  if let some moduleIndex := environment.getModuleIdxFor? name then
    environment.header.moduleNames[moduleIndex]?
  else if environment.contains name then
    some environment.mainModule
  else
    none

def declarationsOwnedBy (environment : Environment) (owner : Name) : List Name :=
  environment.constants.toList.foldl (init := []) fun declarations entry =>
    let name := entry.1
    if !name.isInternal && declarationOwner? environment name == some owner then
      name :: declarations
    else
      declarations

def checkOwners (label : String) (expectedOwner : Name) (names : List Name) : CommandElabM Unit := do
  let environment ← getEnv
  for name in names do
    unless environment.contains name do
      failJoin label m!"missing declaration {name}"
    let actualOwner := declarationOwner? environment name
    unless actualOwner == some expectedOwner do
      failJoin label m!"owner drift for {name}: expected {expectedOwner}, found {actualOwner}"

def checkExactModuleSurface
    (label : String) (expectedOwner : Name) (expected : List Name) : CommandElabM Unit := do
  checkOwners label expectedOwner expected
  let actual := declarationsOwnedBy (← getEnv) expectedOwner
  let unexpected := actual.filter fun name => !expected.contains name
  let missing := expected.filter fun name => !actual.contains name
  unless unexpected.isEmpty && missing.isEmpty do
    failJoin label m!"owned declaration census for {expectedOwner}: unexpected {unexpected}; missing {missing}"

def sortedNames (names : List Name) : List Name :=
  names.mergeSort fun left right => left.toString < right.toString

end Test.Support.Environment
