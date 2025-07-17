/- # IO

`IO` は、入出力という副作用を伴うプログラムを表します。`IO α` の項のことを IO アクションと呼ぶことがあります。

## 標準入出力

`IO.println` は、標準出力に文字列を出力します。たとえば、ターミナルに文字列を出力したりすることができます。
-/

/-⋆-//-- info: hello, world! -/
#guard_msgs in --#
#eval
  let greet := "world"
  IO.println s!"hello, {greet}!"

/- なお、出力が自分自身と等しくなるコードを **クワイン（Quine）** と呼ぶのですが、Lean 4 ではクワインはたとえば次のようにして作ることができます。[^quine] -/

def s := "\ndef main : IO Unit := do\n  IO.println (\"def s := \" ++ s.quote)\n  IO.println (s)"

def main : IO Unit := do
  IO.println ("def s := " ++ s.quote)
  IO.println (s)

/-⋆-//--
info: def s := "\ndef main : IO Unit := do\n  IO.println (\"def s := \" ++ s.quote)\n  IO.println (s)"

def main : IO Unit := do
  IO.println ("def s := " ++ s.quote)
  IO.println (s)
-/
#guard_msgs in --#
#eval main

/- ## ランダム性

ランダムな操作は IO アクションです。
-/

/-- 長さ `n` で、中身の値が 0 以上 `bound` 以下であるようなリストをランダム生成する -/
def randList (n : Nat) (bound : Nat) : IO (List Nat) := do
  let mut out := []
  for _ in [0 : n] do
    -- ランダムに 0 以上 bound 以下の自然数を生成する
    let x ← IO.rand 0 bound

    -- 生成した自然数をリストに追加する
    out := x :: out
  return out

#eval randList 5 10

/- [^quine] このコード例は [leanprover-community/lean4-samples に対するPR](https://github.com/leanprover-community/lean4-samples/pull/22) からの引用です。 -/
