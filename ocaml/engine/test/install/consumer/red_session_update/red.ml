(* red_session_update -- the tool Session stays abstract through its facade alias: no record update; its build must fail (R6.2). *)
let forge (s : Effect4.Tool.Native.Session.t) = { s with memo = [] }
