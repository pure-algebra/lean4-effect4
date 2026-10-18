(* red_checked_literal -- Checked stays abstract through its facade alias: no record literal; its build must fail (R6.2). *)
let forged : int Effect4.Program.Check.Checked.t = { value = 7; trace = [] }
