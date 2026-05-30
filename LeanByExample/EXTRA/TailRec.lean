/- # 付録: 末尾再帰

再帰関数の中で、再帰呼び出しの結果がそのまま関数全体の結果になるものを
**末尾再帰** と呼びます。末尾再帰になっている関数は、次の呼び出しへ進む前に
現在の呼び出しで残っている仕事がないため、実行時にコールスタックを節約できます。

たとえば次の `countNonTR` は末尾再帰ではありません。再帰呼び出し `countNonTR n`
の結果を受け取ってから、さらに `+ 1` を計算する必要があるからです。この場合、
再帰呼び出しは「末尾位置」ではなく、加算の引数の位置にあります。
-/

def countNonTR (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => countNonTR n + 1

#guard countNonTR 10 = 10

/- 一方で、次の `countTR` は末尾再帰です。これまでに数えた分を `acc` に記録しておくことで、
再帰呼び出しを分岐全体の結果にしています。 -/

def countTR (n : Nat) : Nat :=
  countTRAux n 0
where
  countTRAux (n acc : Nat) : Nat :=
    match n with
    | 0 => acc
    | n + 1 => countTRAux n (acc + 1)

#guard countTR 10 = 10

theorem countTRAux_eq (n acc : Nat) : countTR.countTRAux n acc = countNonTR n + acc := by
  induction n generalizing acc with
  | zero =>
      simp [countTR.countTRAux, countNonTR]
  | succ n ih =>
      simp [countTR.countTRAux, countNonTR, ih, Nat.add_comm, Nat.add_left_comm]

theorem countTR_eq_countNonTR (n : Nat) : countTR n = countNonTR n := by
  simp [countTR, countTRAux_eq]

/- `countTRAux_eq` の証明では、補助関数が持つ `acc` の意味を明示しています。
`countTR.countTRAux n acc` は、`n` から数えた結果に、すでに数えてある `acc` を足したものです。
このように末尾再帰化のためにアキュムレータを追加したときは、アキュムレータについて一般化した命題を
証明すると、元の関数との対応を示しやすくなります。 -/

/- ## メモリ使用量の違い

`countNonTR` と `countTR` は同じ値を返します。しかし、メモリ使用量に制限をかけて
大きめの入力を計算すると違いが現れます。

以下の `main` は、`lean --run` でこのファイルを実行したときに使うためのものです。
引数に `nontr` を渡すと末尾再帰ではない実装を、`tr` を渡すと末尾再帰の実装を実行します。
-/

def main (args : List String) : IO Unit := do
  let x := 100_000
  match args with
  | [] =>
    throw <| IO.userError "引数が必要です: `nontr` または `tr` を指定してください"
  | "nontr" :: _ =>
    IO.println s!"countNonTR {x} = {countNonTR x}"
  | "tr" :: _ =>
    IO.println s!"countTR {x} = {countTR x}"
  | _ =>
    throw <| IO.userError "不明な引数です: `nontr` または `tr` を指定してください"

/- このファイルを直接 `lean --run` する代わりに、以下のテスト用ファイルでは２つの実行を別プロセスで行い、
`--memory` によって使用メモリを制限しています。末尾再帰の実装は成功し、末尾再帰でない実装は失敗することを
終了コードによって確認しています。

{{#include ./TailRec/Run.md}}

末尾再帰性は、[`partial_fixpoint`](#{root}/Modifier/PartialFixpoint.md) で修飾できる関数の条件にも現れます。
詳しくは `partial_fixpoint` のページを参照してください。
-/
