(* Round five: the adversarial corpus, as data.

   A corpus program is a list of steps over the union of the five service alphabets, plus a
   root table for the bodies its forks name. The same text is interpreted by two faces --
   `corpus_run.ml` over the avatar and `corpus_rc112.mjs` over rc.112 -- so a program is
   written once and neither face can drift from the other by transcription.

   Grammar (one record per program, blank-line separated):

     prog <name>
     tape <site:0|1,...>          optional
     maxops <n>                   optional
     note <text>                  optional, repeatable
     root <code> <step> ; <step> ; ...
     main <step> ; <step> ; ...

   A step is `<op> <arg>*`, optionally prefixed `@<n>=` to publish its result into a global
   slot. An argument is a literal integer, `#<n>` (the result of step n of this body) or
   `@<n>` (a global slot); a list argument is comma-separated.

   `mask` and `unmask` bracket an uninterruptible region: the avatar spells it
   `WithFiberAction.setInterruptible`, rc.112 spells it `Effect.uninterruptible` over the
   block, which is the same mask with the same M2 restoration. *)

type arg = Lit of int | Local of int | Global of int | List of arg list

type step = { publish : int option; op : string; args : arg list }

type prog = {
  name : string;
  tape : string;
  maxops : int option;
  notes : string list;
  roots : (int * step list) list;
  main : step list;
}

let trim = String.trim

let split_on_string sep s =
  let n = String.length sep in
  let rec go i acc start =
    if i + n > String.length s then List.rev (String.sub s start (String.length s - start) :: acc)
    else if String.sub s i n = sep then go (i + n) (String.sub s start (i - start) :: acc) (i + n)
    else go (i + 1) acc start
  in
  go 0 [] 0

let parse_arg (t : string) : arg =
  let one t =
    let t = trim t in
    if t = "" then Lit 0
    else if t.[0] = '#' then Local (int_of_string (String.sub t 1 (String.length t - 1)))
    else if t.[0] = '@' then Global (int_of_string (String.sub t 1 (String.length t - 1)))
    else Lit (int_of_string t)
  in
  if String.contains t ',' then List (List.map one (String.split_on_char ',' t)) else one t

let parse_step (t : string) : step =
  let t = trim t in
  let publish, t =
    if String.length t > 1 && t.[0] = '@' then
      match String.index_opt t '=' with
      | Some i -> (Some (int_of_string (String.sub t 1 (i - 1))), trim (String.sub t (i + 1) (String.length t - i - 1)))
      | None -> (None, t)
    else (None, t)
  in
  match List.filter (fun w -> w <> "") (String.split_on_char ' ' t) with
  | [] -> failwith "empty step"
  | op :: args -> { publish; op; args = List.map parse_arg args }

let parse_steps (t : string) : step list =
  List.filter_map
    (fun piece -> if trim piece = "" then None else Some (parse_step piece))
    (split_on_string ";" t)

let parse (text : string) : prog list =
  let lines = String.split_on_char '\n' text in
  let progs = ref [] in
  let cur = ref None in
  let flush () = match !cur with None -> () | Some p -> progs := p :: !progs; cur := None in
  let starts_with p s = String.length s >= String.length p && String.sub s 0 (String.length p) = p in
  let after p s = trim (String.sub s (String.length p) (String.length s - String.length p)) in
  List.iter
    (fun raw ->
      let line = trim raw in
      if line = "" || starts_with "#" line then ()
      else if starts_with "prog " line then begin
        flush ();
        cur := Some { name = after "prog " line; tape = ""; maxops = None; notes = []; roots = []; main = [] }
      end
      else
        match !cur with
        | None -> ()
        | Some p ->
          if starts_with "tape " line then cur := Some { p with tape = after "tape " line }
          else if starts_with "maxops " line then
            cur := Some { p with maxops = Some (int_of_string (after "maxops " line)) }
          else if starts_with "note " line then cur := Some { p with notes = p.notes @ [ after "note " line ] }
          else if starts_with "root " line then begin
            let rest = after "root " line in
            match String.index_opt rest ' ' with
            | None -> failwith ("bad root line: " ^ line)
            | Some i ->
              let code = int_of_string (trim (String.sub rest 0 i)) in
              let steps = parse_steps (String.sub rest (i + 1) (String.length rest - i - 1)) in
              cur := Some { p with roots = p.roots @ [ (code, steps) ] }
          end
          else if starts_with "main " line then cur := Some { p with main = parse_steps (after "main " line) }
          else failwith ("unknown corpus line: " ^ line))
    lines;
  flush ();
  List.rev !progs
