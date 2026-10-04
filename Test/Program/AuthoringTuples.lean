import Effect4.Laws.Program.Authoring.Tuples

/-! Finite scope-reader controls; raw reconstruction keeps every stored index. -/
namespace Effect4.Test.AuthoringTuples
open Program

#guard Authoring.tuple [] {} [] = .ok (.app "tuple" .nil)
#guard Authoring.tuple [Authoring.var "name", Authoring.var "trace"]
  { names := ["trace", "name"] } [2] = .ok (.app "tuple" (.cons (.var 1) (.cons (.var 0) .nil)))
#guard Authoring.tuple [Authoring.var "missing", Authoring.var "other"] {} [2] =
  .error ⟨[2], .unbound "missing"⟩
#guard Authoring.tupleAt (Authoring.var "value") 999999999999999999999
  { names := ["trace", "value"] } [2] = .ok (.tupleAt (.var 1) 999999999999999999999)
#guard Authoring.tupleAt (Authoring.var "value") 0 { names := ["value", "value"] } [] =
  .ok (.tupleAt (.var 1) 0)
#guard Authoring.tupleAt (Authoring.var "missing") 0 {} [2] = .error ⟨[2], .unbound "missing"⟩

example : (Authoring.tuple [Authoring.var "value"]).Scoped :=
  Authoring.tuple_scoped fun item hi => by
    cases List.mem_singleton.mp hi
    exact Authoring.var_scoped _
example : (Authoring.tupleAt (Authoring.var "value") 999999999999999999999).Scoped :=
  Authoring.tupleAt_scoped (Authoring.var_scoped _) _

#print axioms Authoring.tuple_scoped
#print axioms Authoring.tupleAt_scoped
end Effect4.Test.AuthoringTuples
