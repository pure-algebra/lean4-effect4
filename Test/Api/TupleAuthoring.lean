import Effect4.Api

/-! Finite application controls for exact tuple composition through the public authoring API. -/
namespace Effect4.Test.TupleAuthoring
open Effect4.Program

def value : Authoring.TermSrc :=
  Authoring.tuple [Authoring.nat 7, Authoring.str "ready", Authoring.bool true]

def selected : Authoring.Src NativeOp :=
  Authoring.bind "entry" (Authoring.succeed value)
    (Authoring.succeed (Authoring.tupleAt (Authoring.var "entry") 1))

#guard (Effect4.Api.author selected).map (fun p => p.ty.answer.normalize) = .ok (.lit "ready")
#guard match Effect4.Api.author selected with
  | .ok p => p.runSync == .success (.str "ready") && p.print.isOk
  | .error _ => false
#guard match Effect4.Api.author (Authoring.succeed (Authoring.tupleAt value 3)) with
  | .error _ => true
  | .ok _ => false

end Effect4.Test.TupleAuthoring
