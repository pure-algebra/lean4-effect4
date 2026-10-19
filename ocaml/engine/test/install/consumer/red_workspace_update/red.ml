(* red_workspace_update -- the tool Workspace stays abstract through its facade alias: no record update; its build must fail (R6.2). *)
let forge (s : Effect4.Tool.Native.Workspace.t) = { s with memo = [] }
