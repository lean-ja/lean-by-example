-- `LEAN_ABORT_ON_PANIC` に値が設定されていると、
-- `hello world!` は表示されずに処理が中断される
def main : IO Unit := do
  let a : Nat := panic! "panic message"
  IO.println a

  IO.println "hello world!"
