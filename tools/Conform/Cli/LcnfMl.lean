import Conform.Effect4.LcnfMl

/-- Thin command entry point; the reusable reader/evaluator module has no global main. -/
def main (args : List String) : IO UInt32 := Conform.Effect4.LcnfMl.main args
