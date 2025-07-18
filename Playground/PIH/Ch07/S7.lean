import Std.Data.HashSet.Basic
/- # 投票アルゴリズム -/

/-- 投票結果 -/
def votes := ["Red", "Blue", "Green", "Blue", "Blue", "Red"]

/-- リストの中の特定の要素の数を数える -/
def count {α : Type} [BEq α] (x : α) (xs : List α) : Nat :=
  xs.filter (· == x) |>.length

#guard count 1 [1, 2, 3, 4, 1, 2, 3, 1, 2, 1] = 4

#guard count "Red" votes = 2

open Std (HashSet)

/-- リストから重複を削除する -/
def rmdups {α : Type} [BEq α] [Hashable α] (xs : List α) : List α :=
  HashSet.ofList xs |>.toList

#guard rmdups [1, 2, 3, 4, 1, 2, 3, 1, 2, 1] = [1, 2, 3, 4]
