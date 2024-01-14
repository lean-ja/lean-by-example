/- # constructor

ゴールが `⊢ P ∧ Q` であるとき，`constructor` を実行すると，ゴールが２つのゴール `⊢ P` と `⊢ Q` に分割されます．-/
variable (P Q : Prop)

example (hP: P) (hQ: Q) : P ∧ Q := by
  -- goal が `left` と `right` に分割される
  constructor
  · -- `P` を示す
    exact hP
  · -- `Q` を示す
    exact hQ

/-! ## case を使う書き方

同じ証明を `case` を使って次のように書き直すことができます．
-/

example (hP: P) (hQ: Q) : P ∧ Q := by
  constructor

  case left =>
    exact hP

  case right =>
    exact hQ

/-! ## 同値を示す

同値 `↔` に対しても，`constructor` は利用できます．-/

example (x : Nat) : x = 0 ↔ x + 1 = 1 := by
  constructor
  · -- `x = 0 → x + 1 = 1` を示す
    intro hx
    rw [hx]
  · -- `x + 1 = 1 → x = 0` を示す
    simp_all

/-! ## 補足

逆に，論理積 `∧` を分解したい場合は `And.left` や `And.right` を使用します．
-/

example (h: P ∧ Q) : P := by
  exact h.left

example (h: P ∧ Q) : Q := by
  exact h.right
