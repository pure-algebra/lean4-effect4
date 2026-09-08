(* e4_abandon.ml — stop a live run and account for every open scope.

   What it is: the abandon pass of D-A3-9. It runs no user code of its own and knows
   nothing about a machine beyond the three functions of the {!driver} record: interrupt the
   root, list the open scopes, take one finalizer step of one scope. Everything else here is
   bookkeeping under two bounds, so the pass always terminates and always accounts.
   Depends on: nothing (Stdlib only).

   The laws AB1-AB5 and the two refusals are stated at the head of e4_abandon.mli.

   WHY FUEL IS COUNTED IN `Some`s AND NOT IN CALLS. `finalizer_step` answers "here is one
   command step" or "this scope is done". Only the first is a step of the machine, so only
   the first is charged. A scope needing n steps therefore costs n fuel and n+1 calls, and a
   scope with no finalizers at all costs nothing. This is what makes `fuel_left` a statement
   about the RUN (steps not taken) rather than about this module's call pattern.

   WHY THE SCOPES ARE READ BEFORE THE INTERRUPT. AB3 says `closed @ unfinished` is every
   open scope of the machine AT ENTRY. If the list were read after `interrupt`, a root
   interrupt that itself closed a scope would make the report silently smaller than the
   machine the caller handed us -- which is precisely the silent drop the ruling forbids. A
   scope the interrupt already finished is still reported, as `closed` with zero steps. *)

type budget = { finalizer_fuel : int; max_scopes : int }

(* Named constants, never `max_int` (trap #17): the same program must not abandon
   differently on a 63-bit and a 31-bit host. *)
let default_finalizer_fuel = 1000
let default_max_scopes = 1024
let default_budget = { finalizer_fuel = default_finalizer_fuel; max_scopes = default_max_scopes }

type report = {
  closed : int list;
  unfinished : int list;
  exits : string list;
  fuel_left : int;
  decisions : int;
}

type 'm driver = {
  interrupt : 'm -> reason:string -> 'm * int;
  open_scopes : 'm -> int list;
  finalizer_step : 'm -> scope:int -> ('m * string list * int) option;
}

(* One scope, under `fuel` command steps. Returns the machine, the exits in emission order
   (reversed onto `exits_rev`), the decisions appended, and whether the scope closed. *)
let close_scope driver m ~scope ~fuel ~exits_rev ~decisions =
  let rec go m left exits_rev decisions =
    if left <= 0 then (m, exits_rev, decisions, `Exhausted)
    else
      match driver.finalizer_step m ~scope with
      | None -> (m, exits_rev, decisions, `Closed left)
      | Some (m', exits, d) -> go m' (left - 1) (List.rev_append exits exits_rev) (decisions + d)
  in
  go m fuel exits_rev decisions

let run driver m ~reason ~budget =
  if budget.finalizer_fuel < 0 then invalid_arg "E4_abandon.run: negative finalizer_fuel";
  if budget.max_scopes < 0 then invalid_arg "E4_abandon.run: negative max_scopes";
  let at_entry = driver.open_scopes m in
  (* AB1, first half: interrupt the root. *)
  let m, interrupt_decisions = driver.interrupt m ~reason in
  (* AB1, second half: innermost-first. `open_scopes` is outermost-first. *)
  let inner_first = List.rev at_entry in
  let rec pass n m scopes closed unfinished exits_rev decisions fuel_left =
    match scopes with
    | [] -> (m, closed, unfinished, exits_rev, decisions, fuel_left)
    | scope :: rest ->
        if n >= budget.max_scopes then
          (* Beyond the pass bound: never attempted, never granted fuel, always reported. *)
          pass n m rest closed (scope :: unfinished) exits_rev decisions fuel_left
        else
          let m, exits_rev, decisions, outcome =
            close_scope driver m ~scope ~fuel:budget.finalizer_fuel ~exits_rev ~decisions
          in
          let closed, unfinished, fuel_left =
            match outcome with
            | `Closed left -> (scope :: closed, unfinished, fuel_left + left)
            | `Exhausted -> (closed, scope :: unfinished, fuel_left)
          in
          pass (n + 1) m rest closed unfinished exits_rev decisions fuel_left
  in
  let m, closed, unfinished, exits_rev, decisions, fuel_left =
    pass 0 m inner_first [] [] [] interrupt_decisions 0
  in
  ( m,
    {
      closed = List.rev closed;
      unfinished = List.rev unfinished;
      exits = List.rev exits_rev;
      fuel_left;
      decisions;
    } )

let accounted r ~at_entry =
  List.sort compare (r.closed @ r.unfinished) = List.sort compare at_entry

let to_string r =
  let ints xs = String.concat "," (List.map string_of_int xs) in
  Printf.sprintf "closed=[%s] unfinished=[%s] exits=%d fuel_left=%d decisions=%d" (ints r.closed)
    (ints r.unfinished) (List.length r.exits) r.fuel_left r.decisions
