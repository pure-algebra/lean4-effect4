import Effect4.Program.SigApp

/-! The program domain's two data carriers. Their codecs are generated in `Api.ObjectDerived`.
An object stores no host state, interpreter configuration or target metadata.
The printed certificate is a projection, not admission evidence. -/

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
deriving DecidableEq

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
