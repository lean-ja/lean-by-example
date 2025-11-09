import Lean

open Std.Do

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

set_option mvcgen.warning false

@[grind =, simp]
theorem List.sum_append_singleton {l : List α} {x : α} :
    (l ++ [x]).sum = l.sum + x := by
  induction l with simp_all <;> grind

/-- `doubleSum` は `append` を和に変換する -/
@[grind =]
theorem doubleSum_append {l1 l2 : List (List α)} :
    doubleSum (l1 ++ l2) = doubleSum l1 + doubleSum l2 := by
  induction l1 with grind

theorem doubleSum_spec (l : List (List α)) : doubleSumDo l = doubleSum l := by
  generalize h : doubleSumDo l = r
  apply Id.of_wp_run_eq h

  mvcgen invariants
  -- 外側のループについての不変条件。
  -- `cursor.prefix` はこれまでに外側の`for`ループで見てきた部分を指している
  · ⇓⟨cursor, result⟩ => ⌜result = doubleSum cursor.prefix⌝

  -- 内側のループについての不変条件。
  · ⇓⟨cursor, result⟩ => by
    expose_names -- すべての死んだ変数に名前を付ける

    -- `pref` は外側のループで今まで見てきた部分を表していて、
    -- `l = pref ++ (cur :: suff)` が成り立つ。
    guard_hyp h_1 :ₛ l = pref ++ cur :: suff

    -- `cursor` は内側のループの進捗を表している。
    exact ⌜result = doubleSum pref + (cursor.prefix).sum⌝
  with grind
