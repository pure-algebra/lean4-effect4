import Lean.Replay
import Lean.Util.Path

/-!
The kernel rung (`make check-kernel`, the sweep tier). Every compiled declaration of this
repository's own modules in the import closure of the given roots is replayed through the kernel
(`Lean.Environment.replay`) into an environment that holds only their dependencies. One
environment and one pass, in safe Lean: the shape the 2026-10-04 environment scout proposed
(`docs/research/2026-10-04-reference-scout/environment.md` §3.1) instead of a bare `leanchecker`,
which holds one imported environment per core and runs this machine out of memory.

What it checks: that the kernel accepts every stored declaration against its dependencies. It
detects a declaration that reached an `.olean` without the kernel, from environment hacking or a
metaprogram that skipped the check. What it does not check: the axioms a declaration reaches (the
axiom gate does), `unsafe` and `partial` constants (`replay` skips them; the gate refuses them in
`Effect4.*` and `Test.*`), compiled code, or the kernel itself, which is the same C++ kernel.

A module is this repository's when its `.olean` lies under `.lake/build/lib/lean`; every other
module of the closure is a dependency, imported and trusted. The module's most private part holds
its full constant table (`readModuleDataParts`), so the replay is unchanged by the module system.

`--self-test` replays a forged theorem of `False` and requires the kernel's refusal.
-/
open Lean

namespace Drivers.KernelReplay

/-- A module is this repository's when its `.olean` lies under `.lake/build/lib/lean`. -/
def isOwn (root : System.FilePath) (olean : System.FilePath) : Bool :=
  olean.toString.startsWith (root.toString ++ "/")

/-- The `.olean` parts that exist for a module, the exported part first. -/
def partsOf (olean : System.FilePath) : IO (Array System.FilePath) := do
  let mut parts := #[olean]
  let server := OLeanLevel.server.adjustFileName olean
  if ← server.pathExists then
    parts := parts.push server
    let priv := OLeanLevel.private.adjustFileName olean
    if ← priv.pathExists then parts := parts.push priv
  return parts

/-- The import closure of `roots`, split into this repository's modules (with their `.olean`) and
dependency modules. Only own modules are opened; a dependency is a leaf. -/
def closure (root : System.FilePath) (roots : Array Name) :
    IO (Array (Name × System.FilePath) × Array Name) := do
  let mut own : Array (Name × System.FilePath) := #[]
  let mut deps : Array Name := #[]
  let mut seen : Std.HashSet Name := {}
  let mut stack := roots
  -- each module is visited once; the bound is a loop bound, not a limit any closure reaches
  for _ in [0:1000000] do
    let some m := stack.back? | break
    stack := stack.pop
    if seen.contains m then continue
    seen := seen.insert m
    let olean ← findOLean m
    if isOwn root olean then
      let (data, _) ← readModuleData olean
      own := own.push (m, olean)
      stack := stack ++ data.imports.map (·.module)
    else
      deps := deps.push m
  return (own, deps)

/-- Every constant the own modules declare, read from each module's most private part. A name a
later module lists again keeps the later entry, as the importer does. -/
def ownConstants (own : Array (Name × System.FilePath)) : IO (Std.HashMap Name ConstantInfo) := do
  let mut out : Std.HashMap Name ConstantInfo := {}
  for (_, olean) in own do
    let parts ← readModuleDataParts (← partsOf olean)
    let some (data, _) := parts.back? | continue
    for (name, info) in data.constNames.zip data.constants do
      out := out.insert name info
  return out

def run (roots : Array Name) : IO UInt32 := do
  let root := (← IO.currentDir) / ".lake" / "build" / "lib" / "lean"
  let (own, deps) ← closure root roots
  let constants ← ownConstants own
  let base ← importModules (deps.map fun m => { module := m }) {} 0
  try
    discard <| base.replay constants
  catch e =>
    IO.eprintln s!"kernel replay: refused: {e}"
    return 1
  IO.println s!"kernel replay: {constants.size} constants of {own.size} modules replayed against {deps.size} dependency modules"
  return 0

/-- The red control: a theorem of `False` whose stored proof is `True.intro` must be refused. -/
def selfTest : IO UInt32 := do
  let base ← importModules #[{ module := `Init }] {} 0
  let forged := ConstantInfo.thmInfo
    { name := `Drivers.KernelReplay.forged, levelParams := [], type := mkConst ``False,
      value := mkConst ``True.intro, all := [`Drivers.KernelReplay.forged] }
  let refused ← try
      discard <| base.replay (({} : Std.HashMap Name ConstantInfo).insert forged.name forged)
      pure false
    catch _ => pure true
  if refused then
    IO.println "kernel replay self-test: the forged theorem is refused"
    return 0
  IO.eprintln "kernel replay self-test: the forged theorem was accepted"
  return 1

end Drivers.KernelReplay

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  match args with
  | ["--self-test"] => Drivers.KernelReplay.selfTest
  | [] => IO.eprintln "usage: kernel-replay <root module>… | --self-test"; return 2
  | roots => Drivers.KernelReplay.run (roots.toArray.map String.toName)
