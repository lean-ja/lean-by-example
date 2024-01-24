/- # gcongr

`gcongr` は合同関係(congruence)を扱うタクティクです．
ゴールが `=` や `≤` などの2項関係で表されているとき， 左辺と両辺にある「共通のパターン」を取り出し，分解します．
-/
import Mathlib.Tactic.GCongr -- `gcongr` を使うため
import Mathlib.Analysis.SpecialFunctions.Log.Basic -- `log` を使うため

open Real

variable (a b : ℝ) (x y : ℝ)

example (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
  gcongr

example (h1 : x ≤ y) (h2 : a ≤ b) (h3 : 0 ≤ a) (h4 : 0 ≤ y)
    : x * a ≤ y * b := by
  gcongr

/-! さらに `@[gcongr]` という `attribute` を付与することにより， `gcongr` で呼び出して使える補題を増やすことができます．-/

variable {U : Type*}
variable (A B C : Set U)

/-- 独自に定義した二項関係．中身は `⊆` と同じ．-/
def mysubset (A B : Set U) : Prop := ∀ x, x ∈ A → x ∈ B

/-- `mysubset` を二項関係らしく書けるようにしたもの. -/
infix:50 " mys " => mysubset

-- `@[gcongr]` をコメントアウトしてみて，下の証明がどうなるか見てみよう．
@[gcongr]
lemma inter_subset_inter_left (h : A ⊆ B) : A ∩ C mys B ∩ C := by
  intro x hx
  aesop

example : B ∩ C mys (A ∪ B) ∩ C := by
  gcongr
  intro x hx
  aesop
