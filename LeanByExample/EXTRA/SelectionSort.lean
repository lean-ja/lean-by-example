/- # 付録: 選択ソートの実装とソートであることの証明

## 実装

以下の疑似コードで表される、選択ソートというソートアルゴリズムがあります。（選択ソートと呼ばれるアルゴリズムにはバリエーションがあり、ここに挙げたものとは異なるものもあります）

1. 1 番目の要素から最後尾の要素までで最も値の小さいものを探し、それを取り除いて 1 番目に置く
2. 以降同様に、未ソート部分の最小要素を見つけだし、未ソート部分の先頭へ移す
3. 未ソート部分が空になったら終了

これを Lean で実装すると、次のようになります。
-/
-- ソートなので大小比較が必要
variable {α : Type} [LE α] [DecidableLE α]

-- リストから最小値を取り除くためには、要素が等しいかどうか判定できる必要がある
variable [DecidableEq α]

-- `List.min` で取得した最小値が実際に最小値であることを保証するのに必要
variable [Std.IsLinearPreorder α]

-- `Std.IsLinearOrder` は仮定していないことに注意
#check_failure (by infer_instance : Std.IsLinearOrder α)

/-- `LE` インスタンスから `Min` インスタンスを作る -/
instance : Min α := minOfLe

grind_pattern List.le_min_iff => x ≤ _, l.min

namespace List

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
/- ## 証明

ソートであることを証明するには、２つのことを証明する必要があります。並び替えになっていることと、昇順に並んでいることです。

### 並び替えであること

2 つのリストが互いの順列であることは `List.Perm` を使って表現でき、`~` という記号で表されます。
-/

open scoped List in

example : [1, 2, 3] ~ [3, 2, 1] := by grind

/-
証明は、`grind` ですぐに終わります。
-/
namespace List

/-- `minFirst` は元のリストの要素を並び替えるだけ -/
@[grind! ·]
theorem minFirst_perm (xs : List α) :
    minFirst xs ~ xs := by
  cases xs with grind

/-- `selectionSort` は元のリストの要素を並び替えるだけ -/
@[grind! ·]
theorem selectionSort_perm (xs : List α) :
    selectionSort xs ~ xs := by
  fun_induction selectionSort xs with grind

end List
/-
### 昇順に並んでいること

昇順に並んでいることは、`List.Pairwise` を使って表現できます。これも、証明は `grind` ですぐに終わります。
-/
namespace List

attribute [grind] List.Pairwise

@[grind ->]
theorem minFirst_spec (x : α) (xs ys : List α) (h : x :: xs = minFirst ys) :
    ∀ y ∈ xs, x ≤ y := by
  fun_cases minFirst ys with grind

theorem selectionSort_sorted (xs : List α) :
    (selectionSort xs).Pairwise (· ≤ ·) := by
  fun_induction selectionSort xs with grind

end List
