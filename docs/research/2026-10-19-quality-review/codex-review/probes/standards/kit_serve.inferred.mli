module J = Effect4_kit.Kit.Json
exception Input of string
val input : ('a, unit, string, 'b) format4 -> 'a
val read_file : string -> string
val json_of : string -> string -> Effect4_kit.Kit.Json.t
val program_of_json : Effect4_kit.Kit.Json.t -> Effect4_kit.Kit.program
val program_of_path : string -> Effect4_kit.Kit.program
val rows_of_json : Effect4_kit.Kit.Json.t -> Eff_types.Row.t list
val tape_of_json : Effect4_kit.Kit.Json.t -> Effect4_kit.Kit.exit list
type request = {
  op : string;
  program : Effect4_kit.Kit.program option;
  rows : Eff_types.Row.t list;
  tape : Effect4_kit.Kit.exit list option;
  limit : int;
  frames : bool;
  budget : int;
  width : int;
  fast : bool;
}
type 'a with_host = { go : 's. 's Effect4_kit.Kit.reactor -> 's -> 'a; }
val with_host : request -> 'a with_host -> 'a
val answer : request -> J.t
val error_json : string -> J.t
val request_of_json : J.t -> request
val serve_line : string -> string
