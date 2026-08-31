import Effects.Conformance.ManifestIndex

/-- Write the per-family conformance manifests — the CAS, replay,
remote, and Merkle families, all bound to the declared model
version — and the index naming every one of them. -/
def main (args : List String) : IO Unit := do
  let dir := args.headD "conformance/manifest"
  IO.FS.createDirAll dir
  let files :=
    Effects.Conformance.Manifest.allFiles
      ++ Effects.Conformance.Manifest.indexFiles
  for (name, content) in files do
    IO.FS.writeFile (System.FilePath.mk dir / name) content
