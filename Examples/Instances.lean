import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic

/-! # instances -/

/-! ## 型クラスとは何か -/

-- `⁻¹` で逆数を表すことができます
#check (2 : ℚ)⁻¹

-- 実数として見た場合でも同様です
#check (2 : ℝ)⁻¹

-- では, `⁻¹` の定義は何でしょうか？
-- 特に，定義域はどうなっているのでしょうか．
-- 行列や複素数 `ℂ` など，逆数を取ることができる型(集合)は
-- 他にもあるはずですね．
-- 定義域を一般の型 `α` に拡張してみて，どうなるか見てみましょう．

variable (α : Type)

-- failed to synthesize instance
--   Inv αL
#check_failure ((fun x ↦ x⁻¹) : α → α)

-- 一般の `α` に対して逆数が定義できるはずはないですね．
-- たとえば，自然数に逆数は定義できません！
-- したがって予想通りエラーになるのですが，
-- エラーメッセージが役に立ちます．
-- `α` は `Inv` のインスタンスではないと Lean に言われています．

-- inductive Inv.{u} : Type u → Type u
-- number of parameters: 1
-- constructors:
-- Inv.mk : {α : Type u} → (α → α) → Inv α
#print Inv

-- この `Inv` が型クラスの例になっています．
-- `Inv` のインスタンスになっている型については，
-- 逆数が定義できます．

/-! ## instances コマンド -/

-- 実際にインスタンスを列挙してみましょう．

#instances Inv

-- たくさん出てきますが，その中に
-- `Real.instInvReal : Inv ℝ` や
-- `Rat.instInvRat : Inv ℚ` があるのがわかります．
-- `ℝ` や `ℚ` では逆数が定義できる理由が確認できました．
