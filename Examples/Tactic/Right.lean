/- # right
ゴールが `⊢ P ∨ Q` であるとき、`right` はゴールを `⊢ Q` に変えます。類似のタクティクに [left](./Left.md) があります。-/
variable (P Q : Prop)

example (hQ : Q) : P ∨ Q := by
  right

  -- ゴールが変わる
  guard_target =ₛ Q

  assumption

/- ## left, right を使わない方法

以下に示すように、`Or.inl` は `a` から `a ∨ b` を得る関数です。また `Or.inr` は `b` から `a ∨ b` を得る関数です。これを使うことで `left` や `right` を使わずに証明できます。
-/

#check (Or.inl : P → P ∨ Q)

#check (Or.inr : Q → P ∨ Q)

example (hP: P) : P ∨ Q := by
  apply Or.inl
  exact hP
