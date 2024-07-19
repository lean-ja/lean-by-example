/- # push_neg

`push_neg` はドモルガン則を使って、否定(negation)を式の中に押し込みます。デフォルトの設定だと、たとえば

* `¬ (P ∧ Q)` は `P → ¬ Q` に、

* `¬ ∀ x, P x` は `∃ x, ¬ P x` に

という調子で変形します。 -/
import Mathlib.Tactic.PushNeg

variable (P Q : Prop)

example (h: P → Q) : ¬ (P ∧ ¬ Q) := by
  -- ドモルガン則を適用して、`¬` を内側に押し込む
  push_neg

  -- デフォルトの設定だと `P → Q` に変形される
  show P → Q

  exact h

/-! 以下の例は、「酔っぱらいのパラドクス」として有名な命題です。 -/

-- `People` という空ではない集合がある
variable {People : Type} [Inhabited People]

-- 人が飲んでいるかどうかを表す述語を考える
variable (isDrinking : People → Prop)

/-- ある `x` という人が存在して、以下が成り立つ:
「`x` が飲んでいるのであれば、すべての人が飲んでいる」 -/
example : ∃ (x : People), isDrinking x → ∀ (y : People), isDrinking y := by
  -- 「すべての人が飲んでいる」かどうかで場合分けをする
  by_cases h : ∀ (y:People), isDrinking y

  case pos =>
    -- すべての人が飲んでいると仮定したので、
    -- 任意の誰かを `x` として取ればよい
    exists default
    intro _
    assumption

  case neg =>
    -- 「すべての人が飲んでいる」が偽の場合。
    -- このとき、飲んでいない人が存在する。
    push_neg at h

    -- このとき、飲んでいない人を `x` として取れば前件が偽になるので条件を満たす
    replace ⟨x, h⟩ := h
    exists x
    simp_all

/-!
## use_distrib

option で `push_neg.use_distrib` を `true` にすると、`¬ (p ∧ q)` を `¬ p ∨ ¬ q` に変形します。
-/

set_option push_neg.use_distrib true

example (h: P → Q) : ¬ (P ∧ ¬ Q) := by
  -- ドモルガン則を適用して、`¬` を内側に押し込む
  push_neg

  -- goal が論理和の形になる
  show ¬ P ∨ Q

  -- 場合分けで示す
  by_cases hP : P
  · right
    exact h hP
  · left
    assumption
