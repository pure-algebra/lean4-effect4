import Effect4.Program.Provision

namespace SideAudit.Provision
open Effect4 Effect4.Program Effect4.Program.Provision

#guard docsSig.serviceTy dbKey = some (.handle "Db")
#guard (layerTy docsSig leftWins).isSome
#guard (layerTy docsSig rightWins).isSome
#guard Ty.sub (Lit.ty (.nat 1)).normalize (Ty.handle "Db").normalize = false
#guard Ty.sub (Lit.ty (.nat 2)).normalize (Ty.handle "Db").normalize = false
-- This is the layer composition the proposed new leaf checks retain as a positive witness.
def leftNat : LayerTerm DocsOp :=
  .merge (.succeed dbBinding (.nat 1)) (.succeed dbBinding (.nat 2))
def rightNat : LayerTerm DocsOp :=
  .merge (.succeed dbBinding (.nat 2)) (.succeed dbBinding (.nat 1))
#guard docsSig.serviceTy dbBinding = some .nat
#guard Ty.sub (Lit.ty (.nat 1)).normalize Ty.nat.normalize = true
#guard (layerTy docsSig leftNat).isSome
#guard layerTy docsSig leftNat = layerTy docsSig rightNat
#guard (build docsSem leftNat Effect4.Machine.Env.Context.empty).map (fun c => c.getV dbBinding) = some (some (.nat 2))
#guard (build docsSem rightNat Effect4.Machine.Env.Context.empty).map (fun c => c.getV dbBinding) = some (some (.nat 1))
end SideAudit.Provision
