module A = Effect4_gen.Api_gen
let forged : A.built = {
  app = { rows = []; services = []; types = [] };
  program = Eff_types.Eff.Succeed (Eff_types.Term.Lit (Eff_types.Lit.Nat 7));
  admitted = { answer = Eff_types.Ty.Nat; error = Eff_types.Ty.Never; requires = [] };
  row_names = [] }
