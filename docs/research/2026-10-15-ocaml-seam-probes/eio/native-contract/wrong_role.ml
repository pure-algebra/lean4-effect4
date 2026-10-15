(* Expected compiler refusal: a native sink is not a readable source. *)
let _ = Eio.Flow.copy
  (Eio.Flow.buffer_sink (Buffer.create 1))
  (Eio.Flow.buffer_sink (Buffer.create 1))
