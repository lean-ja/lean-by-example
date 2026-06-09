/- # IO

`IO` は、入出力(input / output)などの外界とのやり取りを含む計算を表す[モナド](#{root}/TypeClass/Monad.md)です。ファイル操作・入出力・乱数・時刻の取得などの副作用のある処理を包んで、副作用のない処理と区別します。

`IO α` の項は、「実行すると `α` の値を得られるかもしれない計算」を表します。特に、`IO α` の項は計算によって得られる値そのものではありません。このニュアンスを強調するために、`IO α` の項のことを **IO アクション** と呼ぶことがあります。
-/

/- ## IO アクションの例 -/

/- ### 標準入出力

標準出力ストリームに何かを書き込んだり、標準入力ストリームから何かを受け取ったりする処理は `IO` アクションです。以下は、ユーザによりキーボードから入力された文字を受け取って、挨拶を返す単純なプログラムの例です。

{{#include ./IO/Greet.md}}
-/

/-
標準出力に書き込んだ後、同じ行を上書きすることによって、ターミナル上でアニメーションを表示することができます。以下は、処理の進捗を表すスピナーを表示する例です。

{{#include ./IO/Spinner.md}}
-/

/-
また、ユーザの入力を扱うことができるということは、対話的(interactive)なプログラムを書くことができるということです。たとえば、以下のようなプログラムを書くことができます。

* [ユーザとじゃんけんをするCLIプログラム](#{root}/EXTRA/Janken.md)
* [3目並べが遊べるCLIプログラム](#{root}/EXTRA/TicTacToe.md)
-/

/-
余談ですが、Lean 4 でも[クワイン(quine)](#{root}/EXTRA/Quine.md)を書くことができます。
-/

/- ### ファイル操作

以下は、ファイルを読んでその内容を表示するような簡単なコマンドラインツールを実装する例です。

{{#include ./IO/Cat.md}}
-/

/- ### ランダム性

乱数を扱うような操作は `IO` アクションです。
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

/- ### 時刻

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
  -- コンパイラに最適化されて実行順序が変わらないように、`IO.lazyPure` で包む
  let result ← IO.lazyPure <| fun _ => fibonacci 30
  let end_time ← IO.monoMsNow
  IO.println s!"Result: {result}, Time taken: {end_time - start_time} ms"

#eval computeTime

/- ## IO からの脱出

`IO` アクションは基本的に「副作用のある計算」であり、`IO` から脱出する安全かつ汎用的な関数はありません。言い換えれば、`runIO : IO α → α` というような参照透過な関数はありません。

しかし Lean は自由度が高い言語でありまして、この制約も破ることができます。[`unsafe`](#{root}/Modifier/Unsafe.md) な機能を使ってよければ、`IO` から脱出することができます。[^runio]

{{#include ./IO/RunIO.md}}
-/

/-
[^runio]: このコードは [Lake.DSL.Meta](https://github.com/leanprover/lean4/blob/bfad38b63df86f3edf99c5697600e57199661803/src/lake/Lake/DSL/Meta.lean#L42-L61) のコードをほぼそのまま引用したものです。
-/
