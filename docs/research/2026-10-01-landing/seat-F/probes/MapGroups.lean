import Tools.Architecture

/-!
Seat F probe (2026-10-01, landing item 7): what the architecture map's group reader returns after
it reads the Makefile's `GEN_GROUPS` and the generator manifest (`tools/Tools/Architecture.lean`,
`readGroups`). Run from the worktree root; writes nothing. Red controls: the reader must return
the twelve `GEN_GROUPS` names in order, the manifest's 23 groups, and `architecture` (described
in `docs/GENERATED.md`, run by name) last.
-/

open Tools.Architecture

#eval show IO Unit from do
  let order ← readGenGroups
  let manifest ← readManifestGroups
  let groups ← readGroups
  IO.println s!"GEN_GROUPS ({order.length}): {order}"
  IO.println s!"manifest groups: {manifest.length}"
  for g in groups do
    IO.println s!"{g.name}\t{g.producer.take 60}"
  match groups.find? (fun (g : Group) => g.name == "derived") with
  | some g => IO.println s!"derived consumers: {g.consumers.take 200}…"
  | none => IO.println "derived: absent"
