import Lean

open Std.WP

-- `α` は加法的な可換モノイドであると仮定する
variable {α : Type} [Add α] [Zero α]
variable [@Std.Associative α (· + ·)] [@Std.LawfulIdentity α (· + ·) 0]
variable [@Std.Commutative α (· + ·)]

/-- 二重リストに対する和を計算する、関数型スタイルで定義された関数 -/
@[grind]
def doubleSum (l : List (List α)) : α :=
  l.foldr (fun xs acc => acc + xs.sum) 0

/-- 二重リストに対する和を計算する、命令型スタイルで定義された関数 -/
def doubleSumDo (l : List (List α)) : α := Id.run do
  let mut result := 0
  for sublist in l do
    for x in sublist do
      result := result + x
  return result

@[grind =, simp]
theorem List.sum_append_singleton {l : List α} {x : α} :
    (l ++ [x]).sum = l.sum + x := by
  induction l with simp_all <;> grind

/-- `doubleSum` は `append` を和に変換する -/
@[grind =]
theorem doubleSum_append {l1 l2 : List (List α)} :
    doubleSum (l1 ++ l2) = doubleSum l1 + doubleSum l2 := by
  induction l1 with grind

-- `vcgen` が実験的機能であることを明示する
set_option experimental.vcgen true in

theorem doubleSum_spec (l : List (List α)) : doubleSumDo l = doubleSum l := by
  generalize h : doubleSumDo l = r
  apply Id.of_run_eq_wp h

  vcgen invariants
  -- 外側のループについての不変条件。
  -- `outerPref` はこれまでに外側の `for` ループで見てきた部分を指している
  · fun outerPref _ result => result = doubleSum outerPref

  -- 内側のループについての不変条件。
  · fun innerPref _ result => by
    rename_i outerPref cur suff _h _ _ _

    -- `outerPref` は外側のループで今まで見てきた部分を表していて、
    -- `l = outerPref ++ (cur :: suff)` が成り立つ。
    guard_hyp _h :ₛ l = outerPref ++ cur :: suff

    -- `innerPref` は内側のループで今まで見てきた部分を表している。
    exact result = doubleSum outerPref + innerPref.sum
  with finish
