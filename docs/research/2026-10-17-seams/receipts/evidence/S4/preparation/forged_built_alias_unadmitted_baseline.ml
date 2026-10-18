module A = Effect4_gen.Api_gen
type public_built_alias = A.built
let forged : public_built_alias = {
  app = { rows = []; services = []; types = [] };
  program = Eff_types.Eff.Perform (Eff_types.NativeOp.External 0, Eff_types.Term.Lit Eff_types.Lit.Unit);
  admitted = { answer = Eff_types.Ty.Nat; error = Eff_types.Ty.Never; requires = [] };
  row_names = [] }
