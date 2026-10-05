#mod_use "/Users/pooks/Dev/lean4-effect4/ocaml/engine/e4_be.ml";;
#mod_use "/Users/pooks/Dev/lean4-effect4/ocaml/eff/eff_frame.ml";;
let count = ref 0;;
let check name p = incr count; if not p then failwith name;;
let native_be64 n = if n < 0 then invalid_arg "negative" else let b=Bytes.create 8 in Bytes.set_int64_be b 0 (Int64.of_int n); Bytes.to_string b;;
let native_read s pos = if pos < 0 || pos > String.length s - 8 then None else let n=String.get_int64_be s pos in if n < 0L || n > Int64.of_int max_int then None else Some (Int64.to_int n);;
let values = [0;1;255;256;65535;65536;max_int-1;max_int];;
List.iter (fun n -> check "be64 bytes" (native_be64 n = E4_be.be64 n); check "be64 roundtrip" (native_read (native_be64 n) 0=Some n); check "frame writer" (E4_be.be64 n=Eff_frame.to_string Eff_frame.emit_be64 n)) values;;
let rand = Random.State.make [|20261005|];;
for k=0 to 255 do
 let s=String.init (k mod 32) (fun _ -> Char.chr (Random.State.int rand 256)) in
 List.iter (fun pos -> check "checked read" (native_read s pos=E4_be.read_be64 s pos)) [-1;0;1;7;8;String.length s;max_int;min_int];
 List.iter (fun pos -> List.iter (fun limit -> check "frame shared" (E4_be.read_frame s pos limit=Eff_frame.read_frame s pos limit)) [-1;0;String.length s;max_int;min_int]) [-1;0;1;String.length s;max_int;min_int]
done;;
let overflow = Bytes.make 8 '\000';;
Bytes.set_int64_be overflow 0 (Int64.add (Int64.of_int max_int) 1L);;
check "positive overflow refusal" (native_read (Bytes.to_string overflow) 0=None);;
Bytes.set_int64_be overflow 0 (-1L);;
check "unsigned high-bit refusal" (native_read (Bytes.to_string overflow) 0=None);;
let mul_capture x _mula = let _mula=x in let _mulb=_mula in if _mula=0 then 0 else if _mulb > max_int / _mula then max_int else _mula * _mulb;;
let mul_control x operand = let _mula=x in let _mulb=operand in if _mula=0 then 0 else if _mulb > max_int / _mula then max_int else _mula * _mulb;;
let partial_capture _b1 = (fun _b1 -> _b1 + _b1);;
let partial_control captured = (fun _b1 -> captured + _b1);;
let shift_capture _shift_scale b = let _shift_scale = (1 lsl b) in if _shift_scale=0 then 0 else if _shift_scale > max_int / _shift_scale then max_int else _shift_scale * _shift_scale;;
let shift_control a b = let _shift_scale = (1 lsl b) in if a=0 then 0 else if _shift_scale > max_int / a then max_int else a * _shift_scale;;
check "capture multiplication witness" (mul_capture 3 5 = 9 && mul_control 3 5 = 15);;
check "capture partial addition witness" (partial_capture 3 5 = 10 && partial_control 3 5 = 8);;
check "capture shift witness" (shift_capture 3 2 = 16 && shift_control 3 2 = 12);;
Printf.printf "{\"ocaml\":\"%s\",\"int_bits\":%d,\"assertions\":%d,\"failures\":0,\"mul_capture\":9,\"mul_control\":15,\"partial_capture\":10,\"partial_control\":8,\"shift_capture\":16,\"shift_control\":12}\n" Sys.ocaml_version Sys.int_size !count;;
