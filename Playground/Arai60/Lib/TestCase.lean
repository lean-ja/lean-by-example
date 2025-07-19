variable {Input Output : Type}
variable [BEq Output]
variable [ToString Input] [ToString Output]

structure TestCase  where
  input : Input
  expected : Output

def runTest (tests : List <| @TestCase Input Output) (f : Input → Output) : IO Unit := do
  for test in tests do
    let actual := f test.input
    if actual != test.expected then
      throw <| .userError s!"Test failed for input `{test.input}`: expected {test.expected}, got {actual}"
  IO.println s!"All tests passed!"
