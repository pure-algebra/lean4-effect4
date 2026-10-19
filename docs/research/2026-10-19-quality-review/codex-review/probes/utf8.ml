let () =
 let cases = ref 0 and mismatches = ref 0 in
 let check s = incr cases; if Eff_frame.utf8_valid s <> String.is_valid_utf_8 s then incr mismatches in
 check "";
 for n=0 to 255 do check (String.make 1 (Char.chr n)); for m=0 to 255 do check (String.init 2 (function 0 -> Char.chr n | _ -> Char.chr m)) done done;
 let b=Buffer.create 4 in
 for n=0 to 0x10ffff do if Uchar.is_valid n then (Buffer.clear b; Buffer.add_utf_8_uchar b (Uchar.of_int n); check (Buffer.contents b)) done;
 let rng=Random.State.make [|3471|] in
 for _=1 to 100000 do check (String.init (1+Random.State.int rng 12) (fun _ -> Char.chr (Random.State.int rng 256))) done;
 Printf.printf "cases=%d mismatches=%d\n" !cases !mismatches;
 if !mismatches>0 then exit 1
