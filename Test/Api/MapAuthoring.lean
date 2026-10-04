import Effect4.Api

/-! Finite application examples for string maps.
These checks exercise named composition, presence, immutable updates and entry conversion.
They establish no general target execution or host-session property. -/

namespace Effect4.Test.MapAuthoring
open Effect4.Program

def populated : Authoring.TermSrc :=
  Authoring.mapSet Authoring.mapEmpty (Authoring.str "__proto__") (Authoring.nat 7)

def lookup : Authoring.Src NativeOp :=
  Authoring.bind "map" (Authoring.succeed populated)
    (Authoring.succeed (Authoring.mapGet (Authoring.var "map") (Authoring.str "__proto__")))

def original : Authoring.Src NativeOp :=
  Authoring.bind "map" (Authoring.succeed populated)
    (Authoring.bind "updated"
      (Authoring.succeed (Authoring.mapSet (Authoring.var "map") (Authoring.str "__proto__") (Authoring.str "changed")))
      (Authoring.succeed (Authoring.mapGet (Authoring.var "map") (Authoring.str "__proto__"))))

def keys : Authoring.Src NativeOp :=
  Authoring.succeed (Authoring.mapKeys
    (Authoring.mapSet populated (Authoring.str "10") (Authoring.nat 9)))

def reconstructed : Authoring.Src NativeOp :=
  Authoring.succeed (Authoring.mapGet
    (Authoring.mapFromEntries (Authoring.mapEntries populated)) (Authoring.str "__proto__"))

#guard (Effect4.Api.author lookup).map (fun p => p.ty.answer.normalize) = .ok (.option .nat)
#guard match Effect4.Api.author lookup with
  | .ok p => p.runSync == .success (.some (.nat 7)) && p.print.isOk
  | .error _ => false
#guard match Effect4.Api.author original with
  | .ok p => p.runSync == .success (.some (.nat 7))
  | .error _ => false
#guard match Effect4.Api.author keys with
  | .ok p => p.runSync == .success (.list [.str "10", .str "__proto__"])
  | .error _ => false
#guard match Effect4.Api.author reconstructed with
  | .ok p => p.runSync == .success (.some (.nat 7))
  | .error _ => false

end Effect4.Test.MapAuthoring
