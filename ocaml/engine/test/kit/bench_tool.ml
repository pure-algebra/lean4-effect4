(* bench_tool — what one native tool request costs as a session's checker memo grows.

   What it measures: one Kit_tool session opens the session fixture's document, then serves N draft
   edits, each putting a different natural at address [0], so each checks a new part and the
   checker memo learns new entries; it prints the mean milliseconds of the first and the last 100
   edits. A memo whose lookup scans its entries makes the last edits slower; a flat cost means
   the scan is not what a request pays.
   Run from the repository root (it reads the session fixture):
     opam exec --switch=effect4 -- dune build --root ocaml ./engine/test/kit/bench_tool.exe
     ./ocaml/_build/default/engine/test/kit/bench_tool.exe 1000 *)
open Effect4_kit

let edit_line i =
  Printf.sprintf
    "{\"method\":\"edit\",\"payload\":{\"_tag\":\"act\",\"a\":{\"_tag\":\"edit\",\"a\":{\"_tag\":\"draft\",\"e\":{\"_tag\":\"fill\",\"path\":[0],\"program\":{\"_tag\":\"succeed\",\"value\":{\"_tag\":\"lit\",\"value\":{\"_tag\":\"nat\",\"value\":%d}}}}},\"at_\":{\"doc\":{\"generation\":0,\"name\":\"default\"},\"revision\":%d}}},\"version\":1}"
    (i + 100)
    i
;;

let () =
  let n = if Array.length Sys.argv > 1 then int_of_string Sys.argv.(1) else 2000 in
  let t = Kit_tool.create () in
  let first =
    In_channel.with_open_bin "Test/fixtures/session/requests.jsonl" In_channel.input_line
    |> Option.get
  in
  ignore (Kit_tool.serve_line t first);
  let times = Array.make n 0.0 in
  for i = 0 to n - 1 do
    let start = Unix.gettimeofday () in
    let reply = Kit_tool.serve_line t (edit_line i) in
    times.(i) <- (Unix.gettimeofday () -. start) *. 1000.0;
    if i < 2 && String.length reply > 12 && String.sub reply 0 12 = "{\"refused\":"
    then failwith ("refused: " ^ reply)
  done;
  let mean lo hi =
    let sum = ref 0.0 in
    for i = lo to hi - 1 do
      sum := !sum +. times.(i)
    done;
    !sum /. float_of_int (hi - lo)
  in
  let last =
    Kit_tool.serve_line
      t
      "{\"method\":\"history\",\"payload\":{\"_tag\":\"ask\",\"q\":{\"_tag\":\"history\"}},\"version\":1}"
  in
  let accepted = List.length (String.split_on_char '{' last) in
  Printf.printf "history reply holds %d objects (each accepted edit adds some)\n" accepted;
  let block = min 100 n in
  Printf.printf
    "edits %d: first %d mean %.3f ms, last %d mean %.3f ms\n"
    n
    block
    (mean 0 block)
    block
    (mean (n - block) n)
;;
