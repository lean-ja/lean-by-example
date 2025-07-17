def s := "\ndef main : IO Unit := do\n  IO.println (\"def s := \" ++ s.quote)\n  IO.println (s)"

def main : IO Unit := do
  IO.println ("def s := " ++ s.quote)
  IO.println (s)

-- see: https://github.com/leanprover-community/lean4-samples/pull/22
