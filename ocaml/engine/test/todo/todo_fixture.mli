(* Fixture reader shared by the to-do tests and benchmark.
   Depends on Todo_gen and Eff_types.
   Properties: malformed fixtures raise Failure; row names agree with rows.
   Tested by test_todo. *)
type request = private
  { entry : string
  ; program : string
  ; rows : string list
  ; typed : string
  ; names : string
  ; state : string
  ; result : string
  ; forgetful : string
  ; broken : string
  ; admits : string
  ; answer : string
  }

val read_fixture : string -> request list
val exactly : string -> (string -> 'a option) -> string -> 'a
val repo_of : Eff_types.Val.t -> Z.t * (Z.t * (string * bool)) list
val built_of : request -> Todo_gen.built
val hex_of : Eff_types.Val.t -> string
