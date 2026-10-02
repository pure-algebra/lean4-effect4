import Effect4.Laws.Machine.Handles

open Lean Elab Command

-- Keep the optional brackets and comma policy while sharing Lean's simp argument parser.
#guard_msgs in
run_cmd do
  let env ← getEnv
  let forms := #["keys_mem_norm", "keys_mem_norm_at h", "mem_tac", "close_mem h", "sub_tac norm"]
  let suffixes := #[" []", " [h]", " [← h]", " [-h]", " [*]", " [h, ← h, -h, *]"]
  for form in forms do
    for suffix in suffixes do
      let text := form ++ suffix
      if let .error why := Parser.runParserCategory env `tactic text then
        throwError "expected tactic syntax to parse: {text}: {why}"
    for suffix in #[" [h,]", " [", " [,h]", " [←]"] do
      let text := form ++ suffix
      if (Parser.runParserCategory env `tactic text).isOk then
        throwError "expected tactic syntax to refuse: {text}"
  for text in #["keys_mem_norm", "keys_mem_norm_at h", "mem_tac", "close_mem h", "sub_tac",
      "sub_tac using h", "sub_tac using h, k norm [h]"] do
    if let .error why := Parser.runParserCategory env `tactic text then
      throwError "expected optional arguments to parse: {text}: {why}"
