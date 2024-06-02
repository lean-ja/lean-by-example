/- # `#guard`
`#guard` は与えられた Bool 値が true であることを確かめます．
-/
import Batteries.Data.List.Lemmas -- リストに対して `⊆` が使えるようにする

namespace guard --#

-- 階乗関数
def fac : Nat → Nat
| 0 => 1
| n + 1 => (n + 1) * fac n

#guard fac 5 == 120

/- ## guard と Prop 型
`#guard` に `Bool` ではなく `Prop` 型の項を与えた場合，エラーになることがあります．次の命題は証明があるので真ですが， `#guard` は通りません.
-/

example (α : Type) (l : List α) : [] ⊆ l := by simp

-- Prop 型を持つ
#check ((α : Type) → ∀ (l : List α), [] ⊆ l : Prop)

/--
error: type mismatch
  ∀ (α : Type) (l : List α), [] ⊆ l
has type
  Prop : Type
but is expected to have type
  Bool : Type
---
error: cannot evaluate code because 'sorryAx' uses 'sorry' and/or contains errors
-/
#guard_msgs (whitespace := lax) in
#guard ((α : Type) → ∀ (l : List α), [] ⊆ l : Prop)

/-! しかし， `1 + 1 = 2` 等も `#check` で確かめてみると型は `Prop` です．にも関わらず `#guard` に渡してもエラーになりません． これはなぜでしょうか？ -/

-- 型は Prop
/-- info: 1 + 1 = 2 : Prop -/
#guard_msgs in #check 1 + 1 = 2

#guard 1 + 1 = 2

/-! ## 決定可能性
`Prop` 型であっても， Decidable (決定可能)であれば `Bool` に変換できます．それを自動で行っているので，`Prop` 型の項でも `#guard` に通せることがあります．
-/

-- 決定可能な Prop 型の項を Bool に変換する関数
#check (decide : (p : Prop) → [_h : Decidable p] → Bool)

-- Bool 型になっている！
/-- info: decide (1 + 1 = 2) : Bool -/
#guard_msgs in #check decide (1 + 1 = 2)

end guard --#
