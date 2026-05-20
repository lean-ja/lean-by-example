/- # 付録: 選択ソートの実装とソートであることの証明

## 実装

以下の疑似コードで表される、選択ソートというソートアルゴリズムがあります。

1. 1 番目の要素から最後尾の要素までで最も値の小さいものを探し、それを 1 番目の要素と交換する
2. 以降同様に、未ソート部分の最小要素を見つけだし、未ソート部分の先頭要素と交換する
3. 未ソート部分が空になったら終了

これを Lean で実装すると、次のようになります。
-/
namespace List

-- ソートなので大小比較が必要
variable {α : Type} [LE α] [DecidableLE α]

-- リストの要素を交換するためには、要素が等しいかどうか判定できる必要がある
variable [DecidableEq α]

-- `List.min` で取得した最小値が実際に最小値であることを保証するのに必要
variable [Std.IsLinearPreorder α]

-- `Std.IsLinearOrder` は仮定していないことに注意
#check_failure (by infer_instance : Std.IsLinearOrder α)

/-- `LE` インスタンスから `Min` インスタンスを作る -/
instance : Min α := minOfLe

grind_pattern List.le_min_iff => x ≤ _, l.min

/-- リストの最小値を先頭に持ってくる -/
@[grind]
def minFirst (xs : List α) : List α :=
  match h : xs with
  | [] => []
  | x :: xs =>
    let μ := List.min (x :: xs) (h := by simp)
    have mem : μ ∈ x :: xs := by grind
    have min : ∀ y ∈ x :: xs, μ ≤ y := by grind
    let rest := List.erase (x :: xs) μ
    have len_eq : (μ :: rest).length = (x :: xs).length := by grind
    μ :: rest

-- 簡単な動作確認
#guard minFirst [3, 1, 4, 15, 9] = [1, 3, 4, 15, 9]

@[grind =]
theorem minFirst_length (xs : List α) :
    (minFirst xs).length = xs.length := by
  fun_cases minFirst xs with grind

/-- 選択ソート -/
@[grind]
def selectionSort (xs : List α) : List α :=
  let ys := minFirst xs
  have : ys.length = xs.length := by grind
  match hy : ys with
  | [] => []
  | z :: zs =>
    have : zs.length < ys.length := by grind
    z :: selectionSort zs
termination_by xs.length

-- 簡単な動作確認
#guard selectionSort [3, 1, 4, 15, 9] = [1, 3, 4, 9, 15]

end List
