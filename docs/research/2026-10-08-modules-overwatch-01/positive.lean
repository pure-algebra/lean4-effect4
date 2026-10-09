import Effect4.Schema.Modeled.Derive
open Effect4.Program Effect4.Schema
set_option autoImplicit false

namespace DeriveReview
structure EmptyRecord where
  deriving Modeled
#guard Modeled.ty (α := EmptyRecord) == .record []
#guard (Modeled.image EmptyRecord).toVal {} == .ctor 0 [.list [], .list []]
structure Parent where
  x : Nat
  deriving Modeled
structure Child extends Parent where
  y : Bool
  deriving Modeled
#guard Modeled.ty (α := Child) == .record [("toParent", false, .record [("x", false, .nat)]), ("y", false, .bool)]
namespace Nested
structure Escaped where
  «open» : Bool
  deriving Modeled
#guard Modeled.ty (α := Escaped) == .record [("open", false, .bool)]
end Nested
structure ImplicitField where
  {x : Nat}
  deriving Modeled
#guard Modeled.ty (α := ImplicitField) == .record [("x", false, .nat)]
end DeriveReview
