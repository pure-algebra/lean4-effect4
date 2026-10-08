import Effect4.Schema.Modeled.Derive
open Effect4.Program Effect4.Schema
set_option autoImplicit false

namespace DeriveCollisionReview
structure Token where
  value : Nat
def Token.modeledTy : Ty := .nat
-- Should reject generated-name collisions before adding any helper.
derive_modeled Token
-- Observations only: recovery declarations may have been added after the error.
#check Token.modeled_checked
#check Token.modeledToC
end DeriveCollisionReview
