(* red_built_literal -- Built stays abstract through its facade alias: no record literal; its build must fail (R6.2). *)
type alias = Effect4.Api.Built.t
let forged : alias = { app = { rows = []; services = []; types = [] };
  program = Eff_types.Eff.Succeed (Eff_types.Term.Lit Eff_types.Lit.Unit);
  admitted = { answer = Eff_types.Ty.Nat; error = Eff_types.Ty.Never; requires = [] };
  row_names = [] }
