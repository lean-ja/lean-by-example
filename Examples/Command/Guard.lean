/-
  # guard
  `#guard` は与えられた Bool 値が true であることを確かめます．
-/
import Std.Tactic.GuardExpr -- `#guard` のために必要
import Std.Classes.SetNotation -- `⊆` のため --#
import Std.Data.List.Lemmas -- `List` 関連の補題のため --#
namespace guard --#

-- 階乗関数
def fac : Nat → Nat
| 0 => 1
| n + 1 => (n + 1) * fac n

#guard fac 5 = 120

/-
  ## guard と Prop 型
  `#guard` に `Bool` ではなく `Prop` 型の項を与えた場合，エラーになることがあります．次の命題は証明があるので真ですが， `#guard` は通りません.
-/

example (α : Type) (l : List α) : [] ⊆ l := by simp

-- Prop 型を持つ
#check (α : Type) → ∀ (l : List α), [] ⊆ l

-- コメントを外してみよう
-- #guard (α : Type) → ∀ (l : List α), [] ⊆ l

/-! しかし， `1 + 1 = 2` 等も `#check` で確かめてみると型は `Prop` です．にも関わらず `#guard` に渡してもエラーになりません． これはなぜでしょうか？ -/

-- 1 + 1 = 2 : Prop と表示される
-- つまり型は Prop
#check 1 + 1 = 2

#guard 1 + 1 = 2

/-!
  ## 決定可能性
  `Prop` 型であっても， Decidable (決定可能)であれば `Bool` に変換できます．それを自動で行っているので，`Prop` 型の項でも `#guard` に通せることがあります．
-/

-- Decidable.decide (p : Prop) [h : Decidable p] : Bool
-- 決定可能な Prop 型の項を Bool に変換する関数
#check decide

-- Bool 型になっている！
#check decide (1 + 1 = 2)

end guard --#
