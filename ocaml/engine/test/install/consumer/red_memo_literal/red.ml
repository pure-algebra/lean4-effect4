(* red_memo_literal -- Memo stays abstract through its facade alias: no list literal; its build must fail (R6.2). *)
let forged : Effect4.Program.Check.Memo.t = []
