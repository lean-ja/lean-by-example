/- # IO

`IO` は、入出力(I/O)という副作用を伴うプログラムを表します。ファイル操作・入出力・乱数・時刻などの副作用のある処理を包んで、副作用のない処理と区別します。-/

/- ## 標準入出力

「ターミナルに文字列を出力する」という操作や、「標準入力から文字列を読み込む」という操作も `IO` で扱われます。以下は、入力された文字を受け取って、挨拶を返す単純なプログラムの例です。

{{#include ./IO/Greet.md}}
-/

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

/- ## ファイル操作

以下は、ファイルを読んでその内容を表示するような簡単なコマンドラインツールを実装する例です。(`lean --run` を使って実行することができます)

{{#include ./IO/Cat.md}}
-/

/- ## ランダム性

乱数を扱うような操作は IO アクション(`IO α` の項)です。
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

/- ## 時刻

時刻を扱うような操作も IO アクションです。
-/

/-- フィボナッチ数列 -/
def fibonacci (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | n + 2 => fibonacci n + fibonacci (n + 1)

/-- `fibonacci` の計算にかかった時間を計測する -/
def computeTime : IO Unit := do
  let start_time ← IO.monoMsNow
  let result := fibonacci 30
  let end_time ← IO.monoMsNow
  IO.println s!"Result: {result}, Time taken: {end_time - start_time} ms"

#eval computeTime

/- [^quine]: このコード例は [leanprover-community/lean4-samples に対するPR](https://github.com/leanprover-community/lean4-samples/pull/22) からの引用です。 -/
