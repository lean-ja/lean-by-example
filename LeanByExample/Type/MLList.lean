/- # MLList

`MLList` は、遅延評価のリストです。遅延評価とは、大まかには「値が必要になるまで計算を遅らせること」を意味します。ここで、Lean は純粋関数型言語であり、すべての関数は純粋であるため、評価の順序によって式の値は変わらないことに注意してください。

遅延評価のリストは通常のリストと異なり値が必要になるまで評価されることがないので、「～を満たす値を一つ見つける」というタイプの問題を解くのに向いています。以下は、ゴールドバッハ予想（２より大きいすべての偶数は、２つの素数の和で表せる）を検証する関数を実装する例です。
-/
import Batteries

open Lean Elab Command in

/-- 2つのコマンドのうち最初のコマンドのほうが `n` 倍早く終わることを確かめるコマンド -/
elab "#speed_rank " "(" "ratio" ":=" n:num ")" "|" stx1:command "|" stx2:command : command => do
  let start_time ← IO.monoMsNow
  elabCommand stx1
  let end_time ← IO.monoMsNow
  let time1 := end_time - start_time

  let start_time ← IO.monoMsNow
  elabCommand stx2
  let end_time ← IO.monoMsNow
  let time2 := end_time - start_time

  logInfo m!"1つめのコマンドの実行時間: {time1}ms"
  logInfo m!"2つめのコマンドの実行時間: {time2}ms"

  let threshold := n.getNat
  unless time1 * threshold < time2 do
    throwError m!"エラー: 1つめのコマンドが期待されるより速くありません。"

/-- 遅延評価のリスト -/
abbrev LazyList := MLList Id

/-- 与えられた自然数が素数かどうか判定する。
素朴なアルゴリズムであり、かなり遅い。 -/
def Nat.isPrime (n : Nat) : Bool := Id.run do
  if n ≤ 1 then
    return false
  for d in [2:n] do
    if n % d = 0 then
      return false
    if d ^ 2 > n then
      break
  return true

-- テスト
#guard
  let actual := (List.range 100).filter Nat.isPrime
  let expected := [
    2, 3, 5, 7, 11,
    13, 17, 19, 23, 29,
    31, 37, 41, 43, 47,
    53, 59, 61, 67, 71,
    73, 79, 83, 89, 97
  ]
  actual == expected

/-- ゴールドバッハ予想を検証する関数。
遅延評価ではないリストを使っているので、
`Nat.isPrime` をすべての`1 .. n`に対して計算するなどしており非効率。
-/
def goldbachEager (n : Nat) (_ : n % 2 = 0 := by decide) : Nat × Nat :=
  let candidates : List (Nat × Nat) := List.range n
    |>.filter Nat.isPrime
    |>.filter (fun x => (n - x).isPrime)
    |>.map (fun x => (x, n - x))
  candidates.head!

/-- ゴールドバッハ予想を検証する関数。
遅延評価のリストを使用しているので、`Nat.isPrime` を必要なときにのみ計算しており高速。-/
def goldbachLazy (n : Nat) (_ : n % 2 = 0 := by decide) : Nat × Nat :=
  let candidates : LazyList (Nat × Nat) := MLList.range -- 無限リスト
    |>.filter (· < n)
    |>.filter Nat.isPrime
    |>.filter (fun x => (n - x).isPrime)
    |>.map (fun x => (x, n - x))
  candidates.head? |>.get!

-- 遅延評価版の方が10倍以上速いことが確認できる
#speed_rank (ratio := 10)
  | #eval goldbachLazy 123456
  | #eval goldbachEager 123456
