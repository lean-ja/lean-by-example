/- # 1 Two Sum

整数の配列 `nums` と整数 `target` が与えられたとき、合計して `target` になるような 2 つの数のインデックスを返してください。
各入力には**必ずちょうど一つの解**が存在すると仮定してよく、**同じ要素を二度使うことはできません**。
答えは**どのような順序でも**構いません。

---

**例 1:**

入力: `nums = [2,7,11,15]`, `target = 9`
出力: `[0,1]`
説明: `nums[0] + nums[1] == 9` なので、`[0, 1]` を返します。

---

**例 2:**

入力: `nums = [3,2,4]`, `target = 6`
出力: `[1,2]`

---

**例 3:**

入力: `nums = [3,3]`, `target = 6`
出力: `[0,1]`
-/
import Lean

open Std

def twoSum (nums : List Int) (target : Int) : Option (Nat × Nat) := Id.run do
  -- すでに見た数とそのインデックスを記録する
  -- **TODO** HashMap の使用例として良いのでは？
  let mut seen : HashMap Int Nat := {}

  for (n, idx) in nums.zipIdx do
    let diff := target - n
    match seen.get? diff with
    | some seenIdx =>
      return (seenIdx, idx)
    | none =>
      -- `n` を見たので、`seen` に追加する
      seen := seen.insert n idx
      continue
  return none

#guard twoSum [2,7,11,15] 9 = some (0, 1)
#guard twoSum [3,2,4] 6 = some (1, 2)
#guard twoSum [3,3] 6 = some (0, 1)
