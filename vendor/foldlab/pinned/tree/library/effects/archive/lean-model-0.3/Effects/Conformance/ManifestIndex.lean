import Effects.Conformance.Manifest
import Effects.Conformance.ManifestReplay
import Effects.Conformance.ManifestRemote
import Effects.Conformance.ManifestMerkle
import Effects.Conformance.ManifestServer

/-!
# The manifest index

One committed list of every consumable family manifest, emitted beside
the manifests themselves. The index is the TypeScript-side authority
for what must be bound: the implementation suite reads `INDEX.json`
instead of globbing the directory, so a family the model emits without
a suite binding is a red gate rather than a silent gap, and an orphan
file the model no longer emits is equally visible. The emitter, the
briefing, and the index all read the one `allFiles` list.
-/

namespace Effects.Conformance.Manifest

open Json

/-- Every consumable family manifest in emission order — the single
list the emitter writes, the briefing names, and the index projects. -/
def allFiles : List (String × String) :=
  files ++ replayFiles ++ remoteFiles ++ merkleFiles ++ serverFiles

/-- The index document: the family manifest names, sorted, bound to the
declared model version. -/
def indexManifest : Value :=
  .obj [ ("manifests", .arr
           (((allFiles.map (·.1)).mergeSort fun a b => decide (a ≤ b)).map
             Value.str))
       , ("model", .str modelVersion) ]

/-- The committed index file beside the family manifests. -/
def indexFiles : List (String × String) :=
  [("INDEX.json", Json.document indexManifest)]

end Effects.Conformance.Manifest
