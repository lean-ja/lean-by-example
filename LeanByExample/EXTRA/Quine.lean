/- # クワイン

そのプログラムを実行した時の標準出力が自分自身と等しくなるようなコードを書くことができます。そのようなコードを **クワイン（Quine）** と呼ぶのですが、Lean 4 ではクワインはたとえば次のようにして作ることができます。[^quine]
-/

def s := "\ndef main : IO Unit := do\n  IO.println (\"def s := \" ++ s.quote)\n  IO.println (s)"

def main : IO Unit := do
  IO.println ("def s := " ++ s.quote)
  IO.println (s)

--#--
/--
info: def s := "\ndef main : IO Unit := do\n  IO.println (\"def s := \" ++ s.quote)\n  IO.println (s)"

def main : IO Unit := do
  IO.println ("def s := " ++ s.quote)
  IO.println (s)
-/
#guard_msgs in
#eval main
--#--
/-
[^quine]: このコード例は [leanprover-community/lean4-samples に対するPR](https://github.com/leanprover-community/lean4-samples/pull/22) からの引用です。
-/
