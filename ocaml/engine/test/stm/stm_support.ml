(* Stm_support -- the runner the estate's qcheck-stm model tests share (plan E2). Its behaviours
   U1-U3 are stated in stm_support.mli. *)

let seed = 20261018

let repeat n prop x =
  let rec go i = i >= n || (prop x && go (i + 1)) in
  go 0

let par_test ?(retries = 10) ~neg ~name ~count ~repeats ~ok arb prop =
  let make = if neg then QCheck.Test.make_neg else QCheck.Test.make in
  make ~retries ~max_gen:(3 * count) ~count ~name arb (fun triple ->
      QCheck.assume (ok triple);
      repeat repeats prop triple)

let run tests =
  exit (QCheck_base_runner.run_tests ~colors:false ~verbose:true ~rand:(Random.State.make [| seed |]) tests)
