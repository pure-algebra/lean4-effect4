import Effect4.Program.SigApp

/-!
# The two carriers of the program domain, as the codec generator reads them

`codec/gen.sh` compiles this file as the module `Probe.ObjectDef`, runs the tree's generator
(`tools/Effect4Gen/Main.lean`) on it, and checks that `probe-object.lean` holds this text and the
generator's output unchanged.
-/

set_option autoImplicit false

namespace Effect4.Program

/-- **The object**: a program with the signature it is read against. The program's host calls are
positions in `app.rows`, so a program alone is an open term; with its signature it is a program
source, and nothing else is needed to decide its admission. -/
structure Object where
  /-- Σ_app: the host rows by position, the service declarations, the named types -/
  app : SigApp
  /-- the tree, a term of the free object `Eff` over the native alphabet -/
  program : Eff NativeOp

/-- **What `check` prints of an admitted program**: its type's three columns, its rows, the names
its rows give their service keys, and its block's declarations. A projection of `Built`, so it
certifies nothing by itself. -/
structure Certificate where
  answer : Ty
  error : Ty
  requires : List Effect4.ServiceKey
  rows : RowTable
  services : List (Effect4.ServiceKey × String)
  declarations : List DefDecl

end Effect4.Program
