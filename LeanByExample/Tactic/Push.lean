/- # push

`push` タクティクは、演算子などを式の内側に押し込む(push)ためのタクティクです。

## 否定の押し込み

典型的な `push` の使用例は、ドモルガン則を使って否定(negation)を式の中に押し込むことです。
デフォルトの設定だと、次のように変形します。

* `¬ (P ∧ Q)` は `P → ¬ Q` に変形。
* `¬ ∀ x, P x` は `∃ x, ¬ P x` に変形。
-/
import Mathlib.Tactic

example (P Q : Prop) (h : P → Q) : ¬ (P ∧ ¬ Q) := by
  -- ドモルガン則を適用して、`¬` を内側に押し込む
  push Not

  -- デフォルトの設定だと `P → Q` に変形される
  show P → Q

  exact h

/- 以下の例は、「酔っぱらいのパラドクス」として有名な命題です。 -/
section --#

-- `People` という空ではない集合がある
variable {People : Type} [Inhabited People]

-- 人が飲んでいるかどうかを表す述語を考える
variable (isDrinking : People → Prop)

/-- ある `x` という人が存在して、以下が成り立つ:
「`x` が飲んでいるのであれば、すべての人が飲んでいる」 -/
example : ∃ (x : People), isDrinking x → ∀ (y : People), isDrinking y := by
  -- 「すべての人が飲んでいる」かどうかで場合分けをする
  by_cases h : ∀ (y : People), isDrinking y

  case pos =>
    -- すべての人が飲んでいると仮定したので、
    -- 任意の誰かを `x` として取ればよい
    exists default
    intro _
    assumption

  case neg =>
    -- 「すべての人が飲んでいる」が偽の場合。
    -- このとき、飲んでいない人が存在する。
    push Not at h

    -- このとき、飲んでいない人を `x` として取れば前件が偽になるので条件を満たす
    replace ⟨x, h⟩ := h
    exists x
    simp_all

end --#
/-
### distrib オプション

option で `+distrib` を渡すと、`¬ (p ∧ q)` を `¬ p ∨ ¬ q` に変形します。
-/

example (P Q : Prop) (h : P → Q) : ¬ (P ∧ ¬ Q) := by
  -- ドモルガン則を適用して、`¬` を内側に押し込む
  push +distrib Not

  -- goal が論理和の形になる
  show ¬ P ∨ Q

  -- 場合分けで示す
  by_cases hP : P
  · right
    exact h hP
  · left
    assumption

/- ## 他の使用例

以下は、`push` タクティクを使って所属関係 `_ ∈ _` を式の内側に押し込む例です。
`x ∈ A ∪ B` を `x ∈ A ∨ x ∈ B` に変形することができます。
-/

open Set in

example {α : Type} (x y : α) (s : Set α) :
    x ∈ ({y} : Set α) ∪ sᶜ ↔ x = y ∨ ¬ x ∈ s := by
  push _ ∈ _

  -- ∈ が内側に押し込まれる
  guard_target =ₛ x = y ∨ x ∉ s ↔ x = y ∨ x ∉ s

  simp
