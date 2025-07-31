/- # HashMap

`Std.HashMap` は、キー（鍵）と値のペアを格納するデータ構造です。-/
import Lean

open Std in

/-⋆-//-- info: Std.HashMap.ofList [(1, "hello"), (2, "world")] -/
#guard_msgs in --#
#eval ({(1, "hello"), (2, "world")} : HashMap Nat String)

/-
```admonish info title="HashMapの記法"

`HashMap` は `{ (key, value), ... }` という構文で定義することができるのですが、この記法は `HashMap` 専用のものではなくて型クラスで定義されているものなので、期待されている型が `HashMap` だとわかっていなければ人間にとっても Lean にとっても解釈に紛れが発生します。そのため、`HashMap` を `#eval` したときは `HashMap.ofList` を使った表記が選ばれます。
```
-/

/-
## 使用例

### 頻度のカウント

`HashMap` を使うと、たとえば「文字列中に登場する文字の出現回数を数える」といった処理が効率的にできます。 -/

open Std in

/--
文字列中の各文字の出現回数を数えて `HashMap` にまとめる関数。
-/
def countingChars (s : String) : HashMap Char Nat := Id.run do
  -- 空のハッシュマップを作成（キー：文字、値：出現回数）
  let mut counts : HashMap Char Nat := {}
  -- 文字列をリストに変換して1文字ずつ処理
  for c in s.toList do
    -- 既存のカウント値を取得し（なければ 0）、1 を加算して更新
    counts := counts.insert c (counts.getD c 0 + 1)
  -- 完成したハッシュマップを返す
  return counts

#guard (countingChars "").toList == []  -- 空文字列のカウントは空のハッシュマップ
#guard (countingChars "hello")['h']! == 1
#guard (countingChars "hello")['l']! == 2

/- ### ペアの検索

以下は、`HashMap` を使って「足してゼロになるペア」を配列から効率的に探す例です。
-/

open Std in

/--
`nums` は整数の配列、`target` は目標の和。
`nums` の中から、2つの異なるインデックス `i`, `j` を見つけて、
`nums[i] + nums[j] = target` を満たすものを返す。

見つかった場合は `(i, j)` を `some` で返し、なければ `none` を返す。
-/
def twoSum (nums : Array Int) (target : Int) : Option (Nat × Nat) := Id.run do
  -- すでに見た数とそのインデックスを記録するためのハッシュマップ
  let mut seen : HashMap Int Nat := {}

  -- 配列の要素とそのインデックスを1つずつ取り出して処理する
  for (n, idx) in nums.zipIdx do
    -- 現在の数値に対して、必要な差分（ペアとなるべき数）を計算
    let diff := target - n
    -- 差分がすでに見た値に含まれていれば、それが解の一部
    match seen[diff]? with
    | some seenIdx =>
      -- 差分が見つかったので、そのインデックスと現在のインデックスを返す
      return (seenIdx, idx)
    | none =>
      -- 見つからなければ、現在の値とそのインデックスを記録して次へ
      seen := seen.insert n idx
      continue

  -- 最後まで見つからなければ `none` を返す
  return none

-- 動作確認用のテスト
#guard twoSum #[2, 7, 11, 15] 9 = some (0, 1)
#guard twoSum #[3, 2, 4] 6 = some (1, 2)
#guard twoSum #[3, 3] 6 = some (0, 1)
