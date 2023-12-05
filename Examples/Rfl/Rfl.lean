import Mathlib.Data.Nat.Basic -- `n ≤ n` を示すために必要
import Mathlib.Tactic.Relation.Rfl

/-! ## rfl -/

universe u

-- `MyEq` という二項関係を定義する
inductive MyEq {α : Type u} : α → α → Prop
  | refl (a : α) : MyEq a a

-- `MyEq` が反射的であることを登録する
attribute [refl] MyEq.refl

-- `rfl` で示せることが増えている
example (n : ℕ) : MyEq n n := by rfl

/-! ## ≤ と rfl -/

-- `import Mathlib.Data.Nat.Basic` が必要だが，
-- 不等式 ≤ の反射性も登録されているので示すことができる
example (n : ℕ) : n ≤ n := by rfl
