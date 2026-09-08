(* E4_env_list — the LIST twin of E4_env: the same signature (`PENV`,
   src/OCaml5/Lcnf/Externs.lean `carrierSignatures`), backed by the list Lean actually
   carries, in binding order.

   It reproduces `Effect4.Program.Point.childWith` (src/Effect4/Program/Compile.lean:164-165,
   `env := p.env ++ [v]`), `env[i]?` (`List.get?`), `List.length` and `List.take` operation
   for operation, so `Ref` still means what Lean means and the only difference from E4_env is
   the Θ(depth) copy per child — which is the point of the differential (test/test_diff.ml,
   `Ref` vs `Fast`).

   Depends on: the OCaml standard library only (List).

   Behaviours:
   ELT1 to_list is the identity: the carrier IS the environment          by construction
   ELT2 snoc e v = e @ [v], a full copy                                  by construction
   ELT3 get is List.nth_opt and length is List.length: O(n), not O(1) — the twin maintains
        no count, because Lean does not                                  by construction
   ELT4 take is Lean's List.take, clamped                                by construction *)

type 'a t = 'a list

let empty : 'a t = []

let snoc (e : 'a t) (v : 'a) : 'a t = e @ [ v ]

let append (e : 'a t) (l : 'a list) : 'a t = e @ l

let get (e : 'a t) (i : int) : 'a option = if i < 0 then None else List.nth_opt e i

let length (e : 'a t) : int = List.length e

let rec take_go (e : 'a t) (k : int) : 'a t =
  if k <= 0 then [] else match e with [] -> [] | v :: rest -> v :: take_go rest (k - 1)

let take (e : 'a t) (k : int) : 'a t = take_go e k

let to_list (e : 'a t) : 'a list = e

let of_list (l : 'a list) : 'a t = l
