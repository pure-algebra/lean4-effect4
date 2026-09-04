(* The estate's trace wire, in OCaml: header blocks, row kinds, the mask table, the
   projection and the comparison.

   This is a transcription of `ocaml/avatar/compare.py`, which is itself a
   transcription of `effect4-tools/packages/harness/trace.mjs`'s `parseGolden`, `parseMasks`,
   `keeps`, `project` and comparison loop. The daemon carries it so that a `diff` request is
   answered by the daemon and not by shelling out to python: the same rule, one process, and
   available on all three hosts including js_of_ocaml, where there is no python.

   The row kinds are `trace.mjs`'s `EVENT_KINDS`. `enter`, `leave` and `finalizer` are
   emitted by the Flow faces, never by the avatar, but they are kept in the vocabulary so a
   daemon answer can be diffed against a Flow golden without a second parser. *)

let event_kinds =
  [ "op"; "answer"; "failed"; "decide"; "enter"; "leave"; "finalizer"; "done"; "frontier" ]

let is_row_kind (k : string) = List.mem k event_kinds

let split_tabs (line : string) = String.split_on_char '\t' line

let lines_of (text : string) =
  String.split_on_char '\n' text |> List.map (fun l ->
      let n = String.length l in
      if n > 0 && l.[n - 1] = '\r' then String.sub l 0 (n - 1) else l)

type trace = {
  header : (string * string) list;  (* key -> the tab-joined rest, in file order *)
  header_lines : string list;       (* the header block verbatim *)
  rows : string list;               (* the row lines verbatim, in file order *)
  comments : string list;           (* `#`-prefixed lines, which the avatar uses for events *)
}

(* `parse_trace` in compare.py: a line whose first cell is a row kind is a row, a line
   starting `#` is a comment, anything else is a header field. Blank lines are dropped. *)
let parse_trace (text : string) : trace =
  let header = ref [] and header_lines = ref [] and rows = ref [] and comments = ref [] in
  List.iter
    (fun line ->
      if line = "" then ()
      else
        let cells = split_tabs line in
        match cells with
        | [] -> ()
        | first :: rest ->
          if is_row_kind first then rows := line :: !rows
          else if String.length first > 0 && first.[0] = '#' then comments := line :: !comments
          else begin
            header := (first, String.concat "\t" rest) :: !header;
            header_lines := line :: !header_lines
          end)
    (lines_of text);
  { header = List.rev !header;
    header_lines = List.rev !header_lines;
    rows = List.rev !rows;
    comments = List.rev !comments }

let header_field (t : trace) (key : string) : string option = List.assoc_opt key t.header

(* --------------------------------------------------------------------------- masks *)

(* `parseMasks`: seven flags per mask, in the order the mask table writes them --
   ops, answers, decisions, regions, finalizers, outcome, frontier -- expanded to the nine
   row kinds. `failed` follows `answers`; `enter` and `leave` follow `regions`. *)
type mask = { name : string; keeps : (string * bool) list }

let mask_of_flags name (flags : bool list) : mask =
  match flags with
  | [ ops; answers; decisions; regions; finalizers; outcome; frontier ] ->
    { name;
      keeps =
        [ ("op", ops); ("answer", answers); ("failed", answers); ("decide", decisions);
          ("enter", regions); ("leave", regions); ("finalizer", finalizers);
          ("done", outcome); ("frontier", frontier) ] }
  | _ -> failwith (Printf.sprintf "mask %s: expected 7 flags, got %d" name (List.length flags))

let parse_masks (text : string) : mask list =
  List.filter_map
    (fun line ->
      match split_tabs line with
      | "mask" :: name :: flags -> Some (mask_of_flags name (List.map (fun c -> c = "1") flags))
      | _ -> None)
    (lines_of text)

let keeps (m : mask) (kind : string) : bool =
  match List.assoc_opt kind m.keeps with Some b -> b | None -> false

let project (m : mask) (rows : string list) : string list =
  List.filter (fun r -> keeps m (List.hd (split_tabs r))) rows

(* ---------------------------------------------------------------------- comparison *)

type mask_verdict = {
  mask_name : string;
  agree : bool;
  row_count : int;              (* rows kept on the expected side *)
  first_difference : int;       (* the index compare.py prints; = row_count when they agree *)
  expected_row : string option; (* `None` is compare.py's `<end>` *)
  actual_row : string option;
}

let compare_under (m : mask) (expected_rows : string list) (actual_rows : string list) =
  let expected = Array.of_list (project m expected_rows) in
  let actual = Array.of_list (project m actual_rows) in
  let i = ref 0 in
  while !i < Array.length expected && !i < Array.length actual && expected.(!i) = actual.(!i) do
    incr i
  done;
  let agree = !i = Array.length expected && !i = Array.length actual in
  { mask_name = m.name;
    agree;
    row_count = Array.length expected;
    first_difference = !i;
    expected_row = (if !i < Array.length expected then Some expected.(!i) else None);
    actual_row = (if !i < Array.length actual then Some actual.(!i) else None) }

let compare_all (masks : mask list) expected_rows actual_rows : mask_verdict list =
  List.map (fun m -> compare_under m expected_rows actual_rows) masks

let json_of_verdict (v : mask_verdict) : E4d_json.t =
  E4d_json.Obj
    [ ("mask", Str v.mask_name);
      ("agree", Bool v.agree);
      ("rows", Int v.row_count);
      ("firstDifference", Int v.first_difference);
      ("expected", match v.expected_row with Some r -> Str r | None -> Null);
      ("actual", match v.actual_row with Some r -> Str r | None -> Null) ]

(* ------------------------------------------------------------- the classified table

   `corpus/known-divergences.tsv`: `<program>\t<class>\t<why>`. compare.py prints these
   separately and does not fail on them; `diff` reports the class on the verdict so a caller
   can apply the same rule. *)
type known = { program : string; klass : string; why : string }

let parse_known (text : string) : known list =
  List.filter_map
    (fun line ->
      if String.trim line = "" || (String.length line > 0 && line.[0] = '#') then None
      else
        match split_tabs line with
        | program :: klass :: rest ->
          Some { program; klass; why = String.concat "\t" rest }
        | _ -> None)
    (lines_of text)
