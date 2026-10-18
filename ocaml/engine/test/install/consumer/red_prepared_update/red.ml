(* red_prepared_update -- Prepared stays abstract through its facade alias: no record update; its build must fail (R6.2). *)
let forge (p : Effect4.Program.Prepared.t) = { p with table = [] }
