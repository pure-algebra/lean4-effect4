import Effect4.Program.Authoring.Services
namespace AuditD5
open Effect4.Program Effect4.Program.Authoring
def oldService : ServiceDef := { key := ⟨⟨10⟩, ⟨4⟩⟩, carrier := .nat, ops := [Row.host "Old.call" .nat .nat] }
def oldModule : Module NativeOp := { services := [oldService], main := succeed unit }
def added : Package := { name := "new", rows := [Row.host "New.call" .unit .unit] }
def appendInstall {Op : Type} (ps : List Package) (m : Module Op) : Module Op :=
  { m with rows := m.rows ++ Package.rowsOf ps, services := m.services ++ Package.servicesOf ps }
#guard oldModule.rowNames = [("Old.call", 0)]
#guard (appendInstall [added] oldModule).rowNames = [("New.call", 0), ("Old.call", 1)]
#guard (appendInstall [added] oldModule).table ≠ oldModule.table ++ (added.rows.map (·.row))
end AuditD5
