import Effect4.Api.Author
import Effect4.Program.Packages

/-!
# Red controls for `VerifyGuards.lean` (expected to FAIL: exit 1, two errors)

1. The claim it falsifies: "`BuildRefusal.serviceCarrier` is a freshness-or-agreement guard",
   which would admit a key the built-in signature does not type. It refuses it.
2. The claim it falsifies: "installing a package into a module is an append", which would leave
   an already elaborated program unchanged. A later install prepends, and the tree changes.
-/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Research.PedigreeVerify.GuardsRed

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring

def freshSvc : ServiceDef := { key := ⟨⟨11⟩, ⟨20⟩⟩, carrier := .string }
def withSvc (s : ServiceDef) : Module NativeOp := { services := [s], main := succeed (nat 0) }

-- Expected to fail: a freshness-or-agreement guard would let the fresh key through.
#guard Effect4.Api.Author.disagreeingService (withSvc freshSvc) [] = none

def kv : Package := Package.ofRows "kv" Packages.keyValueStoreMemory
def sql : Package := Package.ofRows "sql" Packages.sqliteBun

def mainSrc : Src NativeOp := eff do
  let store ← Row.call (kv.op "Kv.make") unit
  Row.call (kv.op "get") (app "pair" [store, str "greeting"])

def m0 : Module NativeOp := Package.install [kv] { main := mainSrc }
def mLater : Module NativeOp := Package.install [sql] m0

-- Expected to fail: the later install moves `get`, so the elaborated tree changes.
#guard (elaborateModule m0).toOption = (elaborateModule mLater).toOption

end Research.PedigreeVerify.GuardsRed
