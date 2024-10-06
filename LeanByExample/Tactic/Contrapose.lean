/- # contrapose
`contrapose` は対偶を取るタクティクです。

ローカルコンテキストに `h : P` という仮定があるときに `contrapose h` を実行すると、ゴールの否定がローカルコンテキストに追加されて、同時にゴールが `⊢ ¬ P` に変わります。
-/
import Mathlib.Tactic

namespace Contrapose --#

variable {f : Int → Int} {a b : Int}

def Monotone (f : Int → Int) : Prop :=
  ∀ ⦃a₁ a₂⦄, a₁ ≤ a₂ → f a₁ ≤ f a₂

example (h : Monotone f) (h' : f a < f b) : a < b := by
  -- 対偶をとる
  contrapose h'

  -- ゴールと仮定が否定になって入れ替わる
  show ¬f a < f b

  simp_all only [not_lt]
  apply h
  assumption

/- ## contrapose!
`contrapose!` は、対偶をとった後に簡略化を実行します。
-/

example (h : Monotone f) (h' : f a < f b) : a < b := by
  -- 対偶をとる
  contrapose! h'

  -- 不等号の否定を逆向きの不等号に簡略化してくれる
  show f b ≤ f a

  apply h
  assumption

end Contrapose --#
