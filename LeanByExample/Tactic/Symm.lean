/- # symm

`symm` は、等式や同値性などの対称な関係の向きを反転するタクティクです。

たとえばゴールが `b = a` であるとき、`symm` を実行するとゴールは `a = b` に変わります。-/

variable {a b c : Nat}

example (h : a = b) : b = a := by
  symm

  -- ゴールが反転する
  guard_target =ₛ a = b

  assumption

/- ## 仮定を反転する

`symm at h` と書くと、ローカルコンテキストにある仮定 `h` の向きを反転できます。-/

example (h : a = b) (ha : a + c = 0) : b + c = 0 := by
  symm at h

  -- 仮定の向きが反転する
  guard_hyp h : b = a

  rw [h]
  assumption

/- ## 同値関係にも使える

`symm` は等式だけではなく、命題の同値性 `↔` にも使えます。-/

example {P Q : Prop} (h : Q ↔ P) : P ↔ Q := by
  symm

  -- ゴールが反転する
  guard_target =ₛ Q ↔ P

  assumption

example {P Q : Prop} (h : P ↔ Q) (hq : Q) : P := by
  symm at h

  -- 仮定の向きが反転する
  guard_hyp h : Q ↔ P

  rw [h] at hq
  assumption

/- ## カスタマイズ

一般の二項関係に対して `symm` を使いたい場合は、その関係が対称であることを示す定理に `[symm]` 属性を付与します。-/

/-- 2つの自然数の差が高々1であることを表す関係 -/
def Close (x y : Nat) : Prop :=
  x ≤ y + 1 ∧ y ≤ x + 1

/-- `Close` は対称な関係 -/
theorem Close.symm {x y : Nat} (h : Close x y) : Close y x := by
  exact ⟨h.right, h.left⟩

example {x y : Nat} (h : Close x y) : Close y x := by
  -- 登録していないと `symm` は使用できない
  fail_if_success symm

  exact Close.symm h

-- `Close` が対称であることを登録する
attribute [symm] Close.symm

example {x y : Nat} (h : Close x y) : Close y x := by
  symm

  -- `Close y x` が `Close x y` に反転する
  guard_target =ₛ Close x y

  assumption
