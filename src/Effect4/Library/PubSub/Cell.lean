module
import all Init.Data.String.Defs
public import Effect4.Library.PubSub.Model
public import Effect4.Schema.Modeled
public import Effect4.Schema.FieldRef
meta import Effect4.Schema.Modeled.Derive
meta import Effect4.Schema.FieldRef.Elab

/-! Derived images of the natural-message model data.
These logical names do not claim actual subscription-handle allocation or encoding. -/

@[expose] public section
set_option autoImplicit false
namespace Effect4.PubSub
open Effect4.Schema Effect4.Program

derive_modeled Model.Subscriber
derive_modeled Model.State
abbrev subscriberTy := Model.Subscriber.modeledTy
abbrev subscriberFields := match subscriberTy with | .record fs => fs | _ => []
abbrev cellTy := Model.State.modeledTy
abbrev cellFields := match cellTy with | .record fs => fs | _ => []
def idF : FieldRef subscriberFields .nat := field_ref% "id"
def cursorF : FieldRef subscriberFields .nat := field_ref% "cursor"
def publisherIndexF : FieldRef cellFields .nat := field_ref% "publisherIndex"
def remainingF : FieldRef cellFields .nat := field_ref% "remaining"
def subscribersF : FieldRef cellFields (.list subscriberTy) := field_ref% "subscribers"
def valueF : FieldRef cellFields (.option .nat) := field_ref% "value"
end Effect4.PubSub
